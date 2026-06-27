//! # GAP-2 G2-F — master-management gadgets (`q_clean` / `load_master`), position-parametric.
//!
//! Between the two `fam_digits` emit phases the local master must change from `b+1` (the `uinv_digits(b)`
//! phase) to `a+1` (the `u_digits(a)` phase). Per the N+12 design resolution (`docs/gap2-input-loader-plan.md`,
//! "master-mgmt is LOCAL to `u`", confirmed w/ Danielle 2026-06-27) this is **WIPE-AND-LOAD**: `q_clean`
//! erases the old `b+1` master, then `load_master` rebuilds the `a+1` master from a **preserved high-tail
//! backup** (option (A): the backup sits ABOVE the master at a parametric offset `H ≥ g+M`, isolated from
//! the active workspace because every mark/deposit op is bounded by the gap `g ≥ M+2` and never reaches that
//! high — so the phase chain carries the tail through untouched). The backup placement (the offset `H` and
//! the eventual concrete layout) is Danielle's R-P/dovetail call; **everything here is parametric over it**,
//! so the layout decision plugs in only at the final `psc_act` instantiation — zero rip-out risk, the same
//! de-risking pattern as the exit-target-parametric emitter windows.
//!
//! ## This module so far — the WIPE primitive
//! [`lemma_wipe_ones_left`]: the `(q, 1, 0, q, L)` sweep, the master-erasing analog of
//! [`crate::tm_copy_refresh::lemma_unmark_fives_left`] (`5 → 1`). Reading a run of `len + 1` ones (the
//! scanned one plus `len` more in `u`), it writes a blank `0` over each and piles the blanks onto `v`,
//! landing on the tail `w` above the run. This is `q_clean`'s erase core; the round-trip framing
//! (seek-left over the gap → wipe → seek-right return) composes it with the existing
//! [`crate::tm_copy_refresh`] seek lemmas.
//!
//! Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use verus_group_theory::word_numbering::lemma_div_mod_step;
use crate::tm::{Tm, TmConfig, tm_wf, tm_step, tm_run};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};
use crate::tm_two_counter::{repunit_m, lemma_repunit_zero};
use crate::tm_dstring::{pow_nat, lemma_pow_nat_unfold};
use crate::tm_emit::{pile_sym, lemma_pile_sym_shift};
use crate::tm_copy_refresh::{lemma_seek_left_blanks, lemma_seek_right_blanks};
use crate::tm_run_lemmas::lemma_tm_run_split;

verus! {

/// Piling `k` blanks onto `v` just shifts it up: `pile_sym(v, 0, k, m) == v · m^k`. (The closed form
/// `v·m^k + 0·repunit(k)` with the zero term dropped.) Bridges the `seek`/`wipe` `v`-formats. Induction.
pub proof fn lemma_pile_sym_zero(v: nat, k: nat, m: nat)
    ensures
        pile_sym(v, 0, k, m) == v * pow_nat(m, k),
    decreases k,
{
    if k == 0 {
        assert(pile_sym(v, 0, 0, m) == v);
        assert(pow_nat(m, 0) == 1);
        assert(v * pow_nat(m, 0) == v) by(nonlinear_arith) requires pow_nat(m, 0) == 1;
    } else {
        lemma_pile_sym_zero(v, (k - 1) as nat, m);   // pile_sym(v,0,k-1) == v·m^(k-1)
        lemma_pow_nat_unfold(m, k);                  // m^k == m·m^(k-1)
        // pile_sym(v,0,k) == pile_sym(v,0,k-1)·m + 0 == v·m^(k-1)·m == v·m^k.
        assert(pile_sym(v, 0, k, m) == pile_sym(v, 0, (k - 1) as nat, m) * m + 0);
        assert(pile_sym(v, 0, k, m) == v * pow_nat(m, k)) by(nonlinear_arith)
            requires
                pile_sym(v, 0, k, m) == pile_sym(v, 0, (k - 1) as nat, m) * m + 0,
                pile_sym(v, 0, (k - 1) as nat, m) == v * pow_nat(m, (k - 1) as nat),
                pow_nat(m, k) == m * pow_nat(m, (k - 1) as nat);
    }
}

/// **Walk-LEFT over a run of ones ERASING each to a blank (the master-wipe sweep core).** The mirror of
/// [`crate::tm_copy_refresh::lemma_unmark_fives_left`] with the read symbol `5 → 1` and the written symbol
/// `1 → 0`: the quintuple `(q, 1, 0, q, L)` READS a one and WRITES a blank. From the run's lowest one with
/// `len` more ones then tail `w` above (`u == repunit(len) + m^len·w`, scanning a `1`), it fires `len + 1`
/// times — erasing each one and piling a blank `0` onto `v` — and lands the head on `w`'s low cell
/// (`a == w % m`, `u == w / m`), the erased run now `len + 1` blanks piled in `v` (`pile_sym(c.v, 0, ·)`).
/// The caller picks `w` so `w % m != 1` (the separator blank above the master, so the sweep stops). The
/// erase leg of `q_clean`. Induction on `len`; structurally identical to the proven `lemma_unmark_fives_left`.
pub proof fn lemma_wipe_ones_left(tm: Tm, c: TmConfig, q: nat, len: nat, w: nat, i1: int)
    requires
        tm_wf(tm),
        tm.n >= 1,
        0 <= i1 < tm.quints.len(),
        tm.quints[i1] == mk_quint(q, 1, 0, q, Dir::L),
        c.u == repunit_m(len, tm.m) + pow_nat(tm.m, len) * w,
        c.a == 1,
        c.q == q,
    ensures
        tm_run(tm, c, (len + 1) as nat)
            == (TmConfig { u: w / tm.m, v: pile_sym(c.v, 0, (len + 1) as nat, tm.m),
                a: w % tm.m, q: q }),
    decreases len,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1);   // tm_wf ⟹ 0 < n < m, and 1 ≤ n < m
    lemma_tm_step_picks(tm, c, i1);
    let c_next = TmConfig { u: c.u / m, v: c.v * m + 0, a: c.u % m, q: q };
    assert(tm_step(tm, c) == Some(c_next));
    if len == 0 {
        // u == repunit(0) + m^0·w == 0 + 1·w == w. One step erases the lone one, lands on w.
        assert(pow_nat(m, 0) == 1);
        lemma_repunit_zero(m);
        assert(c.u == w) by(nonlinear_arith)
            requires c.u == repunit_m(0, m) + pow_nat(m, 0) * w, repunit_m(0, m) == 0,
                pow_nat(m, 0) == 1;
        assert(pile_sym(c.v, 0, 0, m) == c.v);
        assert(pile_sym(c.v, 0, 1, m) == pile_sym(c.v, 0, 0, m) * m + 0);
        assert(c_next == (TmConfig { u: w / m, v: pile_sym(c.v, 0, 1, m), a: w % m, q: q }));
        assert(tm_run(tm, c_next, 0) == c_next);
        assert(tm_run(tm, c, 1) == c_next);
    } else {
        // u == repunit(len) + m^len·w == (repunit(len-1) + m^(len-1)·w)·m + 1.
        let x = repunit_m((len - 1) as nat, m) + pow_nat(m, (len - 1) as nat) * w;
        assert(repunit_m(len, m) == m * repunit_m((len - 1) as nat, m) + 1);   // repunit recurrence
        lemma_pow_nat_unfold(m, len);                                          // m^len == m·m^(len-1)
        assert(c.u == x * m + 1) by(nonlinear_arith)
            requires
                c.u == repunit_m(len, m) + pow_nat(m, len) * w,
                repunit_m(len, m) == m * repunit_m((len - 1) as nat, m) + 1,
                pow_nat(m, len) == m * pow_nat(m, (len - 1) as nat),
                x == repunit_m((len - 1) as nat, m) + pow_nat(m, (len - 1) as nat) * w;
        lemma_div_mod_step(x, m, 1);   // (x·m + 1)/m == x, %m == 1
        assert(c_next.u == x);
        assert(c_next.a == 1);
        lemma_wipe_ones_left(tm, c_next, q, (len - 1) as nat, w, i1);
        lemma_pile_sym_shift(c.v, 0, len, m);   // pile_sym(c.v·m+0, 0, len) == pile_sym(c.v, 0, len+1)
        assert(tm_run(tm, c, (len + 1) as nat) == tm_run(tm, c_next, len));
    }
}

/// **`q_clean` ERASE leg — seek over the gap, then wipe the whole master, landing at the separator.**
/// The local tape at a phase boundary is `u == m^g·(R(K) + m^(K+1)·T)` (gap `g` blanks below the master
/// `K = old+1` ones, a separator blank at position `K`, then the preserved high-tail backup `T` from
/// position `K+1`), head on the pivot blank (`a == 0`) in the seek state `q_s`. Three quintuples drive it:
///   * `(q_s, 0, 0, q_s, L)` — seek left over the pivot + `g` gap blanks ([`lemma_seek_left_blanks`]),
///   * `(q_s, 1, 0, q_w, L)` — the seek→wipe transition: erase the master's lowest one, enter `q_w`,
///   * `(q_w, 1, 0, q_w, L)` — wipe the remaining ones ([`lemma_wipe_ones_left`]), stop at the separator.
/// After exactly `g + K + 1` steps the master is gone: `u == T` (the backup, now flush at the head), the
/// erased `g + K + 1` blanks piled onto `v` (`v == v0·m^(g+K+1)`), head on the separator blank (`a == 0`)
/// in `q_w`. The backup `T` is untouched (the wipe stops at the separator). The return leg (seek-right back
/// to the pivot) composes next. `K == 1` (single-one master, `old == 0`) is the no-wipe-lemma case (the
/// transition alone clears it); `K ≥ 2` runs the wipe over the `K − 1` survivors.
pub proof fn lemma_q_clean_erase(
    tm: Tm, g: nat, big_k: nat, t: nat, v0: nat,
    q_s: nat, q_w: nat, i_seek: int, i_trans: int, i_wipe: int,
)
    requires
        tm_wf(tm),
        tm.n >= 1,
        big_k >= 1,
        0 <= i_seek < tm.quints.len(),
        0 <= i_trans < tm.quints.len(),
        0 <= i_wipe < tm.quints.len(),
        tm.quints[i_seek] == mk_quint(q_s, 0, 0, q_s, Dir::L),
        tm.quints[i_trans] == mk_quint(q_s, 1, 0, q_w, Dir::L),
        tm.quints[i_wipe] == mk_quint(q_w, 1, 0, q_w, Dir::L),
    ensures
        tm_run(tm,
            TmConfig {
                u: pow_nat(tm.m, g) * (repunit_m(big_k, tm.m) + pow_nat(tm.m, (big_k + 1) as nat) * t),
                v: v0, a: 0, q: q_s },
            (g + big_k + 1) as nat)
            == (TmConfig { u: t, v: v0 * pow_nat(tm.m, (g + big_k + 1) as nat), a: 0, q: q_w }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1);
    let r = (repunit_m(big_k, m) + pow_nat(m, (big_k + 1) as nat) * t) as nat;
    let c0 = TmConfig { u: pow_nat(m, g) * r, v: v0, a: 0, q: q_s };

    // ── r % m == 1 (the master's lowest one), r / m == R(K-1) + m^K·t. ──
    assert(((big_k - 1) + 1) as nat == big_k);
    lemma_pow_nat_unfold(m, (big_k + 1) as nat);    // m^(K+1) == m·m^K
    // r = R(K) + m^(K+1)·t = (m·R(K-1)+1) + m·(m^K·t) = 1 + m·(R(K-1) + m^K·t) = rhi·m + 1.
    let rhi = (repunit_m((big_k - 1) as nat, m) + pow_nat(m, big_k) * t) as nat;
    assert(repunit_m(big_k, m) == m * repunit_m((big_k - 1) as nat, m) + 1);
    assert(r == rhi * m + 1) by(nonlinear_arith)
        requires
            r == repunit_m(big_k, m) + pow_nat(m, (big_k + 1) as nat) * t,
            repunit_m(big_k, m) == m * repunit_m((big_k - 1) as nat, m) + 1,
            pow_nat(m, (big_k + 1) as nat) == m * pow_nat(m, big_k),
            rhi == repunit_m((big_k - 1) as nat, m) + pow_nat(m, big_k) * t;
    lemma_div_mod_step(rhi, m, 1);   // (rhi·m+1)/m == rhi, %m == 1
    assert(r % m == 1);
    assert(r / m == rhi);

    // ── Run 1: seek-left over the gap (g+1 steps). Lands scanning the master's lowest one. ──
    lemma_seek_left_blanks(tm, c0, q_s, g, r, i_seek);
    let c1 = TmConfig { u: r / m, v: v0 * pow_nat(m, (g + 1) as nat), a: r % m, q: q_s };
    assert(tm_run(tm, c0, (g + 1) as nat) == c1);
    assert(c1.a == 1);
    assert(c1.u == rhi);

    // ── Run 2: the transition step (erase lowest one) then wipe the rest. K steps total. ──
    lemma_tm_step_picks(tm, c1, i_trans);
    let c1p = TmConfig { u: c1.u / m, v: c1.v * m + 0, a: c1.u % m, q: q_w };
    assert(tm_step(tm, c1) == Some(c1p));

    if big_k == 1 {
        // rhi == R(0) + m^1·t == m·t == t·m + 0; c1p == {u: t, v: c1.v·m, a: 0, q_w}.
        lemma_repunit_zero(m);
        assert(pow_nat(m, 1) == m) by {
            lemma_pow_nat_unfold(m, 1);
            assert(pow_nat(m, 0) == 1);
            assert(m * pow_nat(m, 0) == m) by(nonlinear_arith) requires pow_nat(m, 0) == 1;
        }
        assert(c1.u == t * m + 0) by(nonlinear_arith)
            requires c1.u == rhi, rhi == repunit_m(0, m) + pow_nat(m, 1) * t,
                repunit_m(0, m) == 0, pow_nat(m, 1) == m;
        lemma_div_mod_step(t, m, 0);   // (t·m+0)/m == t, %m == 0
        assert(c1p.u == t);
        assert(c1p.a == 0);
        // fuel: (g+1) + 1 == g + K + 1 (K==1).
        lemma_tm_run_split(tm, c0, (g + 1) as nat, 1);
        assert((g + 1 + 1) as nat == (g + big_k + 1) as nat);
        assert(tm_run(tm, c1p, 0) == c1p);
        assert(tm_run(tm, c1, 1) == c1p);
        // v: c1.v·m == v0·m^(g+1)·m == v0·m^(g+2) == v0·m^(g+K+1).
        assert((g + big_k + 1) as nat == (g + 2) as nat);
        lemma_pow_nat_unfold(m, (g + 2) as nat);   // m^(g+2) == m·m^(g+1)
        assert(c1p.v == v0 * pow_nat(m, (g + 2) as nat)) by(nonlinear_arith)
            requires
                c1p.v == v0 * pow_nat(m, (g + 1) as nat) * m,
                pow_nat(m, (g + 2) as nat) == m * pow_nat(m, (g + 1) as nat);
        assert(c1p.v == v0 * pow_nat(m, (g + big_k + 1) as nat));
        assert(tm_run(tm, c0, (g + big_k + 1) as nat) == c1p);
    } else {
        // rhi == R(K-1) + m^K·t == (m·R(K-2)+1) + m^(K-2)·(m·t) == wlo·m + 1; c1p.u == wlo.
        let w = (m * t) as nat;
        assert(((big_k - 2) + 1) as nat == (big_k - 1) as nat);
        lemma_pow_nat_unfold(m, big_k);                 // m^K == m·m^(K-1)
        let wlo = (repunit_m((big_k - 2) as nat, m) + pow_nat(m, (big_k - 2) as nat) * w) as nat;
        assert(repunit_m((big_k - 1) as nat, m) == m * repunit_m((big_k - 2) as nat, m) + 1);
        // rhi = R(K-1) + m^K·t = 1 + m·(R(K-2) + m^(K-1)·t) and m^(K-1)·t = m^(K-2)·(m·t).
        lemma_pow_nat_unfold(m, (big_k - 1) as nat);    // m^(K-1) == m·m^(K-2)
        assert(rhi == wlo * m + 1) by(nonlinear_arith)
            requires
                rhi == repunit_m((big_k - 1) as nat, m) + pow_nat(m, big_k) * t,
                repunit_m((big_k - 1) as nat, m) == m * repunit_m((big_k - 2) as nat, m) + 1,
                pow_nat(m, big_k) == m * pow_nat(m, (big_k - 1) as nat),
                pow_nat(m, (big_k - 1) as nat) == m * pow_nat(m, (big_k - 2) as nat),
                wlo == repunit_m((big_k - 2) as nat, m) + pow_nat(m, (big_k - 2) as nat) * w,
                w == m * t;
        assert(c1.u == wlo * m + 1);   // c1.u == rhi
        lemma_div_mod_step(wlo, m, 1);   // (wlo·m+1)/m == wlo, %m == 1
        assert(c1p.u == wlo);
        assert(c1p.a == 1);

        // wipe the remaining K-1 ones: len = K-2, fires K-1 steps.
        lemma_wipe_ones_left(tm, c1p, q_w, (big_k - 2) as nat, w, i_wipe);
        let c3 = TmConfig {
            u: w / m, v: pile_sym(c1p.v, 0, (big_k - 1) as nat, m), a: w % m, q: q_w };
        assert(((big_k - 2) + 1) as nat == (big_k - 1) as nat);
        assert(tm_run(tm, c1p, (big_k - 1) as nat) == c3);

        // c3.u == w/m == (m·t)/m == t; c3.a == w%m == 0.
        assert(w == t * m + 0) by(nonlinear_arith) requires w == m * t;
        lemma_div_mod_step(t, m, 0);   // (t·m+0)/m == t, %m == 0
        assert(c3.u == t);
        assert(c3.a == 0);
        // c3.v == pile_sym(c1p.v, 0, K-1) == c1p.v·m^(K-1) == v0·m^(g+2)·m^(K-1) == v0·m^(g+K+1).
        lemma_pile_sym_zero(c1p.v, (big_k - 1) as nat, m);
        lemma_pow_nat_unfold(m, (g + 2) as nat);   // m^(g+2) == m·m^(g+1)
        crate::tm_copy_refresh::lemma_pow_nat_add(m, (g + 2) as nat, (big_k - 1) as nat);  // m^(g+K+1)==m^(g+2)·m^(K-1)
        assert((g + 2 + (big_k - 1)) as nat == (g + big_k + 1) as nat);
        // c1p.v == v0·m^(g+1)·m == v0·m^(g+2).
        assert(c1p.v == v0 * pow_nat(m, (g + 2) as nat)) by(nonlinear_arith)
            requires
                c1p.v == v0 * pow_nat(m, (g + 1) as nat) * m,
                pow_nat(m, (g + 2) as nat) == m * pow_nat(m, (g + 1) as nat);
        assert(c3.v == v0 * pow_nat(m, (g + big_k + 1) as nat)) by(nonlinear_arith)
            requires
                c3.v == c1p.v * pow_nat(m, (big_k - 1) as nat),
                c1p.v == v0 * pow_nat(m, (g + 2) as nat),
                pow_nat(m, (g + big_k + 1) as nat)
                    == pow_nat(m, (g + 2) as nat) * pow_nat(m, (big_k - 1) as nat);

        // compose: (g+1) + K steps; tm_run(c1, K) == tm_run(c1p, K-1) == c3.
        assert(tm_run(tm, c1p, 0) == c1p);
        assert(tm_run(tm, c1, 1) == c1p);   // one step c1 → c1p (folds via tm_step(c1)==Some(c1p))
        lemma_tm_run_split(tm, c1, 1, (big_k - 1) as nat);
        assert((1 + (big_k - 1)) as nat == big_k);
        assert(tm_run(tm, c1, big_k) == c3);
        lemma_tm_run_split(tm, c0, (g + 1) as nat, big_k);
        assert(((g + 1) + big_k) as nat == (g + big_k + 1) as nat);
        assert(tm_run(tm, c0, (g + big_k + 1) as nat) == c3);
    }
}

/// **`q_clean` RETURN leg — walk back right over the `p` piled blanks to the home pivot.** The erase leg
/// leaves the head `p = g+K+1` cells left of the pivot (`{u: t, v: v0·m^p, a: 0, q: q_w}` — `t` the
/// preserved backup flush at the head, the erased blanks piled atop the output `v0` whose low digit is a
/// real `1..4` output digit). This walks the head back: the wipe→return transition `(q_w, 0, 0, q_r, R)`,
/// then a blank seek-right ([`lemma_seek_right_blanks`], `(q_r, 0, 0, q_r, R)`) crossing the piled blanks
/// and landing ON the output's low digit, then a one-step walk-back `(q_r, d, d, q_home, L)` (one quint per
/// digit `d ∈ {1,2,3,4}`) onto the pivot. After `p + 2` steps the head is home (`a == 0`) in `q_home` with
/// the backup floated up to `u == t·m^p` and the output `v == v0` restored. (The pivot is a blank that the
/// blank seek-right can't distinguish from the piled blanks, so it overshoots by one onto the output digit
/// and the digit walk-back recovers it — the same walk-back-compatible hand-off the emitter's final
/// singleton uses for `q_cmp`.)
pub proof fn lemma_q_clean_return(
    tm: Tm, p: nat, t: nat, v0: nat,
    q_w: nat, q_r: nat, q_home: nat,
    i_wr: int, i_seekr: int, i_sb1: int, i_sb2: int, i_sb3: int, i_sb4: int,
)
    requires
        tm_wf(tm),
        tm.n >= 4,
        p >= 1,
        1 <= v0 % tm.m <= 4,
        0 <= i_wr < tm.quints.len(),
        0 <= i_seekr < tm.quints.len(),
        0 <= i_sb1 < tm.quints.len(),
        0 <= i_sb2 < tm.quints.len(),
        0 <= i_sb3 < tm.quints.len(),
        0 <= i_sb4 < tm.quints.len(),
        tm.quints[i_wr] == mk_quint(q_w, 0, 0, q_r, Dir::R),
        tm.quints[i_seekr] == mk_quint(q_r, 0, 0, q_r, Dir::R),
        tm.quints[i_sb1] == mk_quint(q_r, 1, 1, q_home, Dir::L),
        tm.quints[i_sb2] == mk_quint(q_r, 2, 2, q_home, Dir::L),
        tm.quints[i_sb3] == mk_quint(q_r, 3, 3, q_home, Dir::L),
        tm.quints[i_sb4] == mk_quint(q_r, 4, 4, q_home, Dir::L),
    ensures
        tm_run(tm,
            TmConfig { u: t, v: v0 * pow_nat(tm.m, p), a: 0, q: q_w },
            (p + 2) as nat)
            == (TmConfig { u: t * pow_nat(tm.m, p), v: v0, a: 0, q: q_home }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 4);   // tm_wf ⟹ n < m and n ≥ 4
    let c3 = TmConfig { u: t, v: v0 * pow_nat(m, p), a: 0, q: q_w };

    // ── Step 1: wipe→return transition (q_w,0,0,q_r,R). v0·m^p has a low blank (p ≥ 1). ──
    lemma_tm_step_picks(tm, c3, i_wr);
    let c4 = TmConfig { u: c3.u * m + 0, v: c3.v / m, a: c3.v % m, q: q_r };
    assert(tm_step(tm, c3) == Some(c4));
    // v0·m^p == (v0·m^(p-1))·m, so %m == 0 and /m == v0·m^(p-1).
    lemma_pow_nat_unfold(m, p);   // m^p == m·m^(p-1)
    let vmid = (v0 * pow_nat(m, (p - 1) as nat)) as nat;
    assert(c3.v == vmid * m + 0) by(nonlinear_arith)
        requires c3.v == v0 * pow_nat(m, p), pow_nat(m, p) == m * pow_nat(m, (p - 1) as nat),
            vmid == v0 * pow_nat(m, (p - 1) as nat);
    lemma_div_mod_step(vmid, m, 0);   // (vmid·m+0)/m == vmid, %m == 0
    assert(c4.v == vmid);
    assert(c4.a == 0);

    // ── Step 2: seek-right over the remaining p-1 piled blanks, landing ON v0's low digit. ──
    assert(c4.v == pow_nat(m, (p - 1) as nat) * v0) by(nonlinear_arith)
        requires c4.v == v0 * pow_nat(m, (p - 1) as nat);
    lemma_seek_right_blanks(tm, c4, q_r, (p - 1) as nat, v0, i_seekr);
    let c5 = TmConfig { u: c4.u * pow_nat(m, p), v: v0 / m, a: v0 % m, q: q_r };
    assert(tm_run(tm, c4, p) == c5);   // seek fires (p-1)+1 == p steps
    // c5.u == (t·m)·m^p == t·m^(p+1).
    crate::tm_copy_refresh::lemma_pow_nat_add(m, 1, p);   // m^(p+1) == m^1·m^p == m·m^p
    assert(pow_nat(m, 1) == m) by {
        lemma_pow_nat_unfold(m, 1);
        assert(pow_nat(m, 0) == 1);
        assert(m * pow_nat(m, 0) == m) by(nonlinear_arith) requires pow_nat(m, 0) == 1;
    }
    assert(c5.u == t * pow_nat(m, (p + 1) as nat)) by(nonlinear_arith)
        requires
            c5.u == (t * m) * pow_nat(m, p),
            pow_nat(m, (p + 1) as nat) == pow_nat(m, 1) * pow_nat(m, p),
            pow_nat(m, 1) == m;

    // ── Step 3: digit walk-back (q_r, d, d, q_home, L) onto the pivot blank. ──
    let d = (v0 % m) as nat;
    let i_sb: int = if d == 1 { i_sb1 } else if d == 2 { i_sb2 } else if d == 3 { i_sb3 } else { i_sb4 };
    assert(tm.quints[i_sb] == mk_quint(q_r, d, d, q_home, Dir::L));
    lemma_tm_step_picks(tm, c5, i_sb);
    let c6 = TmConfig { u: c5.u / m, v: c5.v * m + d, a: c5.u % m, q: q_home };
    assert(tm_step(tm, c5) == Some(c6));
    // c6.u == (t·m^(p+1))/m == t·m^p; c6.a == (t·m^(p+1))%m == 0; c6.v == (v0/m)·m + v0%m == v0.
    lemma_pow_nat_unfold(m, (p + 1) as nat);   // m^(p+1) == m·m^p
    assert(c5.u == (t * pow_nat(m, p)) * m + 0) by(nonlinear_arith)
        requires c5.u == t * pow_nat(m, (p + 1) as nat),
            pow_nat(m, (p + 1) as nat) == m * pow_nat(m, p);
    lemma_div_mod_step((t * pow_nat(m, p)) as nat, m, 0);   // (X·m+0)/m == X, %m == 0
    assert(c6.u == t * pow_nat(m, p));
    assert(c6.a == 0);
    // c6.v == (v0/m)·m + v0%m == v0 (Euclidean).
    assert(c6.v == v0) by(nonlinear_arith)
        requires c6.v == (v0 / m) * m + v0 % m, m > 4;

    // ── Compose: p+2 total (1 transition + p seek + 1 walk-back). ──
    assert(tm_run(tm, c5, 1) == c6) by {
        assert(tm_run(tm, c6, 0) == c6);
    }
    lemma_tm_run_split(tm, c4, p, 1);
    assert((p + 1) as nat == (p + 1) as nat);
    assert(tm_run(tm, c4, (p + 1) as nat) == c6);
    assert(tm_run(tm, c3, 1) == c4) by {
        assert(tm_run(tm, c4, 0) == c4);
    }
    lemma_tm_run_split(tm, c3, 1, (p + 1) as nat);
    assert((1 + (p + 1)) as nat == (p + 2) as nat);
    assert(tm_run(tm, c3, (p + 2) as nat) == c6);
}

/// Total fuel of one `q_clean` (erase `g+K+1` + return `(g+K+1)+2`): `2g + 2K + 4`.
pub open spec fn q_clean_fuel(g: nat, big_k: nat) -> nat {
    (2 * g + 2 * big_k + 4) as nat
}

/// **`q_clean` — wipe the local master, position-parametric in the high-tail backup.** The full
/// master-erase gadget for WIPE-AND-LOAD: from a phase-boundary tape
/// `u == m^g·(R(K) + m^(K+1)·T)` (gap `g`, old master `K = old+1` ones, separator blank, preserved backup
/// `T` above) with the output `v0` (low digit `1..4`) on the right and the head on the pivot in `q_s`, it
/// erases the whole master and returns the head to the pivot in `q_home`, leaving `u == m^(g+K+1)·T` (the
/// master region `g..g+K` now blank, `T` floated up by one separator place, untouched) and `v0` restored.
/// Composes [`lemma_q_clean_erase`] (seek-left + wipe) and [`lemma_q_clean_return`] (seek-right +
/// digit walk-back) over the nine quintuples of three states `q_s`/`q_w`/`q_r`. `load_master` then rebuilds
/// the `a+1` master at position `g` from `T`; the backup offset stays parametric (Danielle's R-P/dovetail
/// call) so the layout plugs in only at the final `psc_act` instantiation.
pub proof fn lemma_q_clean(
    tm: Tm, g: nat, big_k: nat, t: nat, v0: nat,
    q_s: nat, q_w: nat, q_r: nat, q_home: nat,
    i_seek: int, i_trans: int, i_wipe: int,
    i_wr: int, i_seekr: int, i_sb1: int, i_sb2: int, i_sb3: int, i_sb4: int,
)
    requires
        tm_wf(tm),
        tm.n >= 4,
        big_k >= 1,
        1 <= v0 % tm.m <= 4,
        0 <= i_seek < tm.quints.len(),
        0 <= i_trans < tm.quints.len(),
        0 <= i_wipe < tm.quints.len(),
        0 <= i_wr < tm.quints.len(),
        0 <= i_seekr < tm.quints.len(),
        0 <= i_sb1 < tm.quints.len(),
        0 <= i_sb2 < tm.quints.len(),
        0 <= i_sb3 < tm.quints.len(),
        0 <= i_sb4 < tm.quints.len(),
        tm.quints[i_seek] == mk_quint(q_s, 0, 0, q_s, Dir::L),
        tm.quints[i_trans] == mk_quint(q_s, 1, 0, q_w, Dir::L),
        tm.quints[i_wipe] == mk_quint(q_w, 1, 0, q_w, Dir::L),
        tm.quints[i_wr] == mk_quint(q_w, 0, 0, q_r, Dir::R),
        tm.quints[i_seekr] == mk_quint(q_r, 0, 0, q_r, Dir::R),
        tm.quints[i_sb1] == mk_quint(q_r, 1, 1, q_home, Dir::L),
        tm.quints[i_sb2] == mk_quint(q_r, 2, 2, q_home, Dir::L),
        tm.quints[i_sb3] == mk_quint(q_r, 3, 3, q_home, Dir::L),
        tm.quints[i_sb4] == mk_quint(q_r, 4, 4, q_home, Dir::L),
    ensures
        tm_run(tm,
            TmConfig {
                u: pow_nat(tm.m, g) * (repunit_m(big_k, tm.m) + pow_nat(tm.m, (big_k + 1) as nat) * t),
                v: v0, a: 0, q: q_s },
            q_clean_fuel(g, big_k))
            == (TmConfig { u: t * pow_nat(tm.m, (g + big_k + 1) as nat), v: v0, a: 0, q: q_home }),
{
    let m = tm.m;
    let c0 = TmConfig {
        u: pow_nat(m, g) * (repunit_m(big_k, m) + pow_nat(m, (big_k + 1) as nat) * t),
        v: v0, a: 0, q: q_s };
    let p = (g + big_k + 1) as nat;

    // ── erase leg: c0 → c3 in g+K+1 steps. ──
    lemma_q_clean_erase(tm, g, big_k, t, v0, q_s, q_w, i_seek, i_trans, i_wipe);
    let c3 = TmConfig { u: t, v: v0 * pow_nat(m, p), a: 0, q: q_w };
    assert(tm_run(tm, c0, p) == c3);

    // ── return leg: c3 → home in p+2 steps. ──
    lemma_q_clean_return(tm, p, t, v0, q_w, q_r, q_home, i_wr, i_seekr, i_sb1, i_sb2, i_sb3, i_sb4);
    let home = TmConfig { u: t * pow_nat(m, p), v: v0, a: 0, q: q_home };
    assert(tm_run(tm, c3, (p + 2) as nat) == home);

    // ── compose: p + (p+2) == 2g+2K+4 == q_clean_fuel. ──
    lemma_tm_run_split(tm, c0, p, (p + 2) as nat);
    assert((p + (p + 2)) as nat == q_clean_fuel(g, big_k));
    assert(tm_run(tm, c0, q_clean_fuel(g, big_k)) == home);
}

} // verus!
