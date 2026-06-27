//! # GAP-2 G2-F Route (i) brick R-relnum-gen (STEP 2, model B) — copy-refresh foundation (seek walks).
//!
//! After a per-block loop ([`crate::tm_block_loop`]) consumes the active `temp` counter, the left tape is
//! `u == dec_u(0, m^temp·w) == m^temp·w` — the master content `w` has floated UP by `temp` cells, leaving a
//! growing blank gap between the home pivot and the master. To emit the NEXT power-block of the same phase
//! (same exponent) the machine must rebuild a fresh `temp` counter from the PRESERVED master (a copy-refresh,
//! plan §5 / the n=5 marker decision). The first ingredient is locating the master across that blank gap.
//!
//! This file builds the **seek** walks — the blank-gap analogs of [`crate::tm_dwalk`] (which walk over
//! nonzero digit blocks and stop at a blank); here the head walks over a run of blanks and stops at the
//! first NONZERO cell (the master's low digit):
//!   - [`lemma_seek_left_blanks`]: walk-LEFT over a blank gap to the master (`(q, 0, 0, q, L)`), and
//!   - [`lemma_seek_right_blanks`]: walk-RIGHT over a blank gap back to the pivot (`(q, 0, 0, q, R)`),
//!     the un-seek mirror.
//! Both are symbol-agnostic in the piled content (`v` / `u` round-trips through the seek + un-seek).
//!
//! `docs/gap2-input-loader-plan.md` §5 (R-relnum-gen STEP 2, model B). Fully verified, no escape hatches.

use vstd::prelude::*;
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
use verus_group_theory::machine_group::Dir;
use verus_group_theory::word_numbering::lemma_div_mod_step;
use crate::tm::{Tm, TmConfig, tm_wf, tm_step, tm_run, quint_matches, apply_quint};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};
use crate::tm_two_counter::{repunit_m, lemma_repunit_zero};
use crate::tm_dstring::{pow_nat, lemma_pow_nat_unfold};
use crate::tm_walk::{pile_ones, lemma_pile_ones_div_mod};
use crate::tm_run_lemmas::lemma_tm_run_split;
use crate::tm_dec_master::{dec_u, lemma_walk_left_prefix, lemma_walk_back_prefix};
use crate::tm_block_loop::lemma_dec_u_step;

verus! {

/// `m^(a+b) == m^a · m^b` (the additive place-value law; induction on `b`).
pub proof fn lemma_pow_nat_add(m: nat, a: nat, b: nat)
    ensures
        pow_nat(m, (a + b) as nat) == pow_nat(m, a) * pow_nat(m, b),
    decreases b,
{
    if b == 0 {
        assert(pow_nat(m, 0) == 1);
        assert((a + 0) as nat == a);
        assert(pow_nat(m, a) * 1 == pow_nat(m, a)) by(nonlinear_arith);
    } else {
        lemma_pow_nat_add(m, a, (b - 1) as nat);   // m^(a+b-1) == m^a·m^(b-1)
        assert((a + (b - 1)) as nat == (a + b - 1) as nat);
        lemma_pow_nat_unfold(m, (a + b) as nat);   // m^(a+b) == m·m^(a+b-1)
        lemma_pow_nat_unfold(m, b);                // m^b == m·m^(b-1)
        assert(pow_nat(m, (a + b) as nat) == pow_nat(m, a) * pow_nat(m, b)) by(nonlinear_arith)
            requires
                pow_nat(m, (a + b) as nat) == m * pow_nat(m, (a + b - 1) as nat),
                pow_nat(m, (a + b - 1) as nat) == pow_nat(m, a) * pow_nat(m, (b - 1) as nat),
                pow_nat(m, b) == m * pow_nat(m, (b - 1) as nat);
    }
}

// ============================================================================
// the marked-copy invariant (closed form, drift-free)
// ============================================================================

/// **The left-tape value during the marked unary copy (STATIONARY-MASTER design, `G ≥ M`).** After `j` of
/// the master's `big_m` ones have been copied (marked `1 → 5` low-to-high), reading `u` low→high from the
/// home pivot:
///   `[temp: j ones][G − j blanks: shrinking gap][master @ position G: j fives (low) then (big_m − j) ones]`.
/// The master sits at the FIXED absolute position `G` (factor `m^G`, independent of `j`); the temp counter
/// grows at its HIGH end INTO the gap (the gap shrinks `G → G−j`), so **no `u·m+1` shift and no `v`/output
/// corruption** — every iteration is two in-place additions (mark `+4·m^(G+j)`, deposit `+m^j`). This needs
/// `G ≥ big_m` so the gap never runs out before the copy finishes (guaranteed: at every `copy_refresh` the
/// gap `G = k·i ≥ i = big_m`, the phase's shared exponent). Closed form:
///   `copy_u(j, M, G) = repunit(j) + m^G·(5·repunit(j) + m^j·repunit(M−j))`.
/// Endpoints: `copy_u(0,M,G) = m^G·repunit(M)` (the post-[`crate::tm_block_loop`] state — master at gap `G`,
/// no counter), and `copy_u(M,M,G) = repunit(M) + m^G·5·repunit(M)` (fresh temp `M` ones built at the
/// pivot, master all fives at `G`), which the un-mark pass `5 → 1` turns into `dec_u(M, m^(G−M)·repunit(M))`
/// — a fresh `M`-counter below the preserved master (`M` ones at the stationary position `G`), ready for the
/// next `block_loop`.
pub open spec fn copy_u(j: nat, big_m: nat, g: nat, m: nat) -> nat {
    repunit_m(j, m)
        + pow_nat(m, g)
            * (5 * repunit_m(j, m) + pow_nat(m, j) * repunit_m((big_m - j) as nat, m))
}

/// **Start endpoint:** `copy_u(0, M, G) == m^G · repunit(M)` — the post-`block_loop` left tape (the master's
/// `M` ones floated up by the consumed counter to gap `G`, nothing below the pivot). The input to the copy.
pub proof fn lemma_copy_u_start(big_m: nat, g: nat, m: nat)
    ensures
        copy_u(0, big_m, g, m) == pow_nat(m, g) * repunit_m(big_m, m),
{
    lemma_repunit_zero(m);          // repunit_m(0) == 0
    assert(pow_nat(m, 0) == 1);
    // copy_u(0,M,G) = 0 + m^G·(5·0 + m^0·repunit(M)) = m^G·repunit(M).
    assert(5 * repunit_m(0, m) == 0) by(nonlinear_arith) requires repunit_m(0, m) == 0;
    assert(pow_nat(m, 0) * repunit_m((big_m - 0) as nat, m) == repunit_m(big_m, m)) by(nonlinear_arith)
        requires pow_nat(m, 0) == 1;
    assert(copy_u(0, big_m, g, m) == pow_nat(m, g) * repunit_m(big_m, m)) by(nonlinear_arith)
        requires
            copy_u(0, big_m, g, m)
                == repunit_m(0, m) + pow_nat(m, g) * (5 * repunit_m(0, m)
                    + pow_nat(m, 0) * repunit_m(big_m, m)),
            repunit_m(0, m) == 0,
            5 * repunit_m(0, m) == 0,
            pow_nat(m, 0) * repunit_m(big_m, m) == repunit_m(big_m, m);
}

/// **End endpoint (pre-unmark):** `copy_u(M, M, G) == repunit(M) + m^G·(5·repunit(M))` — the fresh temp
/// counter (`M` ones) is built at the pivot, and the whole master block (stationary at `G`) is now `M`
/// fives (every one copied). The subsequent un-mark pass rewrites those `M` fives back to ones, yielding
/// `dec_u(M, m^(G−M)·repunit(M))` (see [`lemma_copy_u_end_unmarked`]).
pub proof fn lemma_copy_u_end(big_m: nat, g: nat, m: nat)
    ensures
        copy_u(big_m, big_m, g, m)
            == repunit_m(big_m, m) + pow_nat(m, g) * (5 * repunit_m(big_m, m)),
{
    lemma_repunit_zero(m);
    assert(pow_nat(m, big_m) * repunit_m((big_m - big_m) as nat, m) == 0) by(nonlinear_arith)
        requires repunit_m((big_m - big_m) as nat, m) == 0, (big_m - big_m) as nat == 0;
    // copy_u(M,M,G) = repunit(M) + m^G·(5·repunit(M) + m^M·repunit(0)) = repunit(M) + m^G·5·repunit(M).
    assert(copy_u(big_m, big_m, g, m)
        == repunit_m(big_m, m) + pow_nat(m, g) * (5 * repunit_m(big_m, m)))
        by(nonlinear_arith)
        requires
            copy_u(big_m, big_m, g, m)
                == repunit_m(big_m, m) + pow_nat(m, g)
                    * (5 * repunit_m(big_m, m) + pow_nat(m, big_m) * repunit_m((big_m - big_m) as nat, m)),
            pow_nat(m, big_m) * repunit_m((big_m - big_m) as nat, m) == 0;
}

/// **The un-marked end state IS a `dec_u` home config.** After the copy builds `copy_u(M,M,G)` and the
/// un-mark pass rewrites the master's `M` fives back to ones (replacing the `5·repunit(M)` factor by
/// `repunit(M)`, giving `repunit(M) + m^G·repunit(M)`), the left tape is exactly
/// `dec_u(M, m^(G−M)·repunit(M))` — a fresh `M`-counter (`repunit(M)`) below the preserved master (`M` ones
/// at the stationary position `G`, i.e. `G−M` above the new counter). Needs `G ≥ M` (the stationary-master
/// gap invariant). This pins the post-copy-refresh home config for the next `block_loop`.
pub proof fn lemma_copy_u_end_unmarked(big_m: nat, g: nat, m: nat)
    requires
        g >= big_m,
    ensures
        repunit_m(big_m, m) + pow_nat(m, g) * repunit_m(big_m, m)
            == dec_u(big_m, (pow_nat(m, (g - big_m) as nat) * repunit_m(big_m, m)) as nat, m),
{
    lemma_pow_nat_add(m, big_m, (g - big_m) as nat);   // m^(M+(G−M)) == m^M·m^(G−M)
    assert((big_m + (g - big_m)) as nat == g);
    // dec_u(M, w) = repunit(M) + m^M·w with w = m^(G−M)·repunit(M); m^M·(m^(G−M)·repunit(M)) = m^G·repunit(M).
    assert(pow_nat(m, big_m) * (pow_nat(m, (g - big_m) as nat) * repunit_m(big_m, m))
        == pow_nat(m, g) * repunit_m(big_m, m)) by(nonlinear_arith)
        requires pow_nat(m, g) == pow_nat(m, big_m) * pow_nat(m, (g - big_m) as nat);
}

/// **Seek-left over a blank gap to the master.** From `{u: m^g·r, a: 0, q: q_seek}` with `r % m != 0`
/// (the target's low digit is nonzero — the master), the loop quintuple `(q_seek, 0, 0, q_seek, L)` fires
/// `g + 1` times: it peels the initial scanned blank (the pivot) plus the `g` gap blanks of `u`, piling all
/// `g + 1` blanks onto `v` (multiplying it by `m^(g+1)`), and lands the head on the master's low digit
/// `{u: r/m, v: c.v · m^(g+1), a: r % m, q: q_seek}` — where `r % m != 0` makes the loop quintuple stop
/// firing (a different `(q_seek, s, …)` quintuple then takes over). The blank-gap analog of
/// [`crate::tm_dwalk::lemma_dwalk_left`]; induction on `g`.
pub proof fn lemma_seek_left_blanks(tm: Tm, c: TmConfig, q_seek: nat, g: nat, r: nat, i0: int)
    requires
        tm_wf(tm),
        0 <= i0 < tm.quints.len(),
        tm.quints[i0] == mk_quint(q_seek, 0, 0, q_seek, Dir::L),
        c.u == pow_nat(tm.m, g) * r,
        r % tm.m != 0,
        c.a == 0,
        c.q == q_seek,
    ensures
        tm_run(tm, c, (g + 1) as nat)
            == (TmConfig { u: r / tm.m, v: c.v * pow_nat(tm.m, (g + 1) as nat), a: r % tm.m, q: q_seek }),
    decreases g,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1);   // tm_wf ⟹ 0 < n < m
    // the loop quintuple matches (q == q_seek, a == 0) and fires (L-move, a2 == 0).
    assert(quint_matches(tm.quints[i0], c));
    lemma_tm_step_picks(tm, c, i0);
    let c_next = apply_quint(tm.quints[i0], c, m);
    assert(tm_step(tm, c) == Some(c_next));
    // L-move, a2 == 0: u' = c.u/m, v' = c.v·m + 0, a' = c.u%m.
    assert(c_next.u == c.u / m);
    assert(c_next.v == c.v * m + 0);
    assert(c_next.a == c.u % m);
    assert(c_next.q == q_seek);
    if g == 0 {
        // u == m^0·r == r; a' == r%m ≠ 0 (master), u' == r/m. Done in one step.
        assert(pow_nat(m, 0) == 1);
        assert(1nat * r == r) by(nonlinear_arith);
        assert(c.u == r);
        assert(pow_nat(m, 1) == m) by { lemma_pow_nat_unfold(m, 1); assert(pow_nat(m, 0) == 1); }
        assert(c.v * m + 0 == c.v * pow_nat(m, 1)) by(nonlinear_arith)
            requires pow_nat(m, 1) == m;
        assert(c_next == (TmConfig { u: r / m, v: c.v * pow_nat(m, (g + 1) as nat), a: r % m,
            q: q_seek }));
        assert(tm_run(tm, c_next, 0) == c_next);
        assert(tm_run(tm, c, 1) == c_next);
    } else {
        // u == m^g·r == m·(m^(g-1)·r); a' == 0 (still in the gap), u' == m^(g-1)·r.
        let r1 = pow_nat(m, (g - 1) as nat) * r;
        lemma_pow_nat_unfold(m, g);   // m^g == m·m^(g-1)
        assert(c.u == m * r1) by(nonlinear_arith)
            requires c.u == pow_nat(m, g) * r, pow_nat(m, g) == m * pow_nat(m, (g - 1) as nat),
                r1 == pow_nat(m, (g - 1) as nat) * r;
        assert(m * r1 == r1 * m) by(nonlinear_arith);
        lemma_div_mod_step(r1, m, 0);   // (r1·m + 0)/m == r1, %m == 0
        assert(c_next.u == r1);
        assert(c_next.a == 0);
        // recurse on g-1.
        lemma_seek_left_blanks(tm, c_next, q_seek, (g - 1) as nat, r, i0);
        // IH: tm_run(c_next, g) == (r/m, c_next.v · m^g, r%m, q_seek); chain to g+1.
        lemma_pow_nat_unfold(m, (g + 1) as nat);   // m^(g+1) == m·m^g
        assert(c_next.v * pow_nat(m, g) == c.v * pow_nat(m, (g + 1) as nat)) by(nonlinear_arith)
            requires c_next.v == c.v * m + 0, pow_nat(m, (g + 1) as nat) == m * pow_nat(m, g);
        assert(tm_run(tm, c, (g + 1) as nat) == tm_run(tm, c_next, g));
    }
}

/// **Seek-right over a blank gap (the un-seek mirror of [`lemma_seek_left_blanks`]).** The exact `u ↔ v`,
/// `L ↔ R` swap: from `{v: m^g·rv, a: 0, q: q_seek}` with `rv % m != 0` (the target's low digit on the
/// right is nonzero), the loop quintuple `(q_seek, 0, 0, q_seek, R)` fires `g + 1` times — peeling the
/// initial scanned blank plus the `g` gap blanks of `v`, piling all `g + 1` onto `u` (multiplying it by
/// `m^(g+1)`) — and lands the head on the target's low digit `{u: c.u · m^(g+1), v: rv/m, a: rv % m,
/// q: q_seek}`. Used to walk the head back right toward home after the marked copy. Induction on `g`.
pub proof fn lemma_seek_right_blanks(tm: Tm, c: TmConfig, q_seek: nat, g: nat, rv: nat, i0: int)
    requires
        tm_wf(tm),
        0 <= i0 < tm.quints.len(),
        tm.quints[i0] == mk_quint(q_seek, 0, 0, q_seek, Dir::R),
        c.v == pow_nat(tm.m, g) * rv,
        rv % tm.m != 0,
        c.a == 0,
        c.q == q_seek,
    ensures
        tm_run(tm, c, (g + 1) as nat)
            == (TmConfig { u: c.u * pow_nat(tm.m, (g + 1) as nat), v: rv / tm.m, a: rv % tm.m,
                q: q_seek }),
    decreases g,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1);
    assert(quint_matches(tm.quints[i0], c));
    lemma_tm_step_picks(tm, c, i0);
    let c_next = apply_quint(tm.quints[i0], c, m);
    assert(tm_step(tm, c) == Some(c_next));
    // R-move, a2 == 0: u' = c.u·m + 0, v' = c.v/m, a' = c.v%m.
    assert(c_next.u == c.u * m + 0);
    assert(c_next.v == c.v / m);
    assert(c_next.a == c.v % m);
    assert(c_next.q == q_seek);
    if g == 0 {
        assert(pow_nat(m, 0) == 1);
        assert(1nat * rv == rv) by(nonlinear_arith);
        assert(c.v == rv);
        assert(pow_nat(m, 1) == m) by { lemma_pow_nat_unfold(m, 1); assert(pow_nat(m, 0) == 1); }
        assert(c.u * m + 0 == c.u * pow_nat(m, 1)) by(nonlinear_arith)
            requires pow_nat(m, 1) == m;
        assert(c_next == (TmConfig { u: c.u * pow_nat(m, (g + 1) as nat), v: rv / m, a: rv % m,
            q: q_seek }));
        assert(tm_run(tm, c_next, 0) == c_next);
        assert(tm_run(tm, c, 1) == c_next);
    } else {
        let rv1 = pow_nat(m, (g - 1) as nat) * rv;
        lemma_pow_nat_unfold(m, g);   // m^g == m·m^(g-1)
        assert(c.v == m * rv1) by(nonlinear_arith)
            requires c.v == pow_nat(m, g) * rv, pow_nat(m, g) == m * pow_nat(m, (g - 1) as nat),
                rv1 == pow_nat(m, (g - 1) as nat) * rv;
        assert(m * rv1 == rv1 * m) by(nonlinear_arith);
        lemma_div_mod_step(rv1, m, 0);   // (rv1·m + 0)/m == rv1, %m == 0
        assert(c_next.v == rv1);
        assert(c_next.a == 0);
        lemma_seek_right_blanks(tm, c_next, q_seek, (g - 1) as nat, rv, i0);
        lemma_pow_nat_unfold(m, (g + 1) as nat);   // m^(g+1) == m·m^g
        assert(c_next.u * pow_nat(m, g) == c.u * pow_nat(m, (g + 1) as nat)) by(nonlinear_arith)
            requires c_next.u == c.u * m + 0, pow_nat(m, (g + 1) as nat) == m * pow_nat(m, g);
        assert(tm_run(tm, c, (g + 1) as nat) == tm_run(tm, c_next, g));
    }
}

// ============================================================================
// the deposit (high-end temp grow) — the dec_temp MIRROR (insert, not discard)
// ============================================================================

/// **The `deposit` gadget — grow the temp counter by ONE at its HIGH end (the temp/master separator),
/// returning to the home pivot.** The stationary-master copy-refresh deposit (plan §5 / N+5 mechanics note):
/// the home layout is `[temp: j ones][separator blank][gap…][master @ G]…` with the head on the pivot `0`
/// before the temp counter. Four quintuples — the MIRROR of [`crate::tm_dec_master::lemma_dec_temp`], with
/// the erase+discard replaced by a single INSERT-turnaround that writes a fresh `1` at the separator blank:
///   `(q_dh, 0, 0, q_dw, L)`  peel the pivot (push it onto v, expose temp's inner one),
///   `(q_dw, 1, 1, q_dw, L)`  walk left over temp's ones to the temp/master separator blank,
///   `(q_dw, 0, 1, q_bk, R)`  INSERT-turnaround: write a `1` at the separator (was `0`), grow temp,
///   `(q_bk, 1, 1, q_bk, R)`  walk back, reconstructing temp+1 (the high content `w` shifts DOWN one).
/// From `{u: dec_u(j, w), v: out, a: 0, q_dh}` (`w % m == 0`, the separator is a blank), `2·j + 2` steps
/// reach `{u: dec_u(j, w) + m^j, v: out, a: 0, q_bk}` — temp grown to `j + 1` ones at the high end (so the
/// gap above shrinks by one), the output `v` round-tripped (pushed onto the pile, restored). Composes
/// [`crate::tm_dec_master::lemma_walk_left_prefix`] + [`crate::tm_dec_master::lemma_walk_back_prefix`].
pub proof fn lemma_deposit(
    tm: Tm, j: nat, w: nat, out: nat,
    q_dh: nat, q_dw: nat, q_bk: nat,
    i_pivot: int, i_one_l: int, i_ins: int, i_one_r: int,
)
    requires
        tm_wf(tm),
        tm.n >= 2,
        w % tm.m == 0,
        0 <= i_pivot < tm.quints.len(),
        0 <= i_one_l < tm.quints.len(),
        0 <= i_ins < tm.quints.len(),
        0 <= i_one_r < tm.quints.len(),
        tm.quints[i_pivot] == mk_quint(q_dh, 0, 0, q_dw, Dir::L),
        tm.quints[i_one_l] == mk_quint(q_dw, 1, 1, q_dw, Dir::L),
        tm.quints[i_ins] == mk_quint(q_dw, 0, 1, q_bk, Dir::R),
        tm.quints[i_one_r] == mk_quint(q_bk, 1, 1, q_bk, Dir::R),
    ensures
        tm_run(tm,
            TmConfig { u: dec_u(j, w, tm.m), v: out, a: 0, q: q_dh },
            (2 * j + 2) as nat)
            == (TmConfig { u: (dec_u(j, w, tm.m) + pow_nat(tm.m, j)) as nat, v: out, a: 0, q: q_bk }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 2);   // tm_wf ⟹ 0 < n < m, n ≥ 2
    let c0 = TmConfig { u: dec_u(j, w, m), v: out, a: 0, q: q_dh };
    let v1 = out * m;   // the output with the pivot 0 pushed on top
    lemma_div_mod_step(out, m, 0);   // v1/m == out, v1%m == 0
    assert(out * m + 0 == v1);

    // w == (w/m)·m  (w%m == 0).
    lemma_fundamental_div_mod(w as int, m as int);
    assert(w == m * (w / m)) by { assert(w % m == 0); }
    assert(m * (w / m) == w);

    // ── Step 1: peel the pivot (q_dh, 0, 0, q_dw, L). ──
    // dec_u(j,w) % m == 0 when j==0 (== w, w%m==0), == 1 when j>=1; we want the head on temp's low one
    // (j>=1) or directly on the separator (j==0). Compute u0/m and u0%m uniformly.
    lemma_tm_step_picks(tm, c0, i_pivot);
    let c_peel = apply_quint(tm.quints[i_pivot], c0, m);
    assert(tm_step(tm, c0) == Some(c_peel));
    assert(c_peel.v == v1);
    assert(c_peel.q == q_dw);
    assert(tm_run(tm, c_peel, 0) == c_peel);
    assert(tm_run(tm, c0, 1) == c_peel);

    if j == 0 {
        // u0 == dec_u(0,w) == w; head onto the separator (a == w%m == 0), u == w/m.
        assert(dec_u(0, w, m) == w) by { lemma_repunit_zero(m); assert(pow_nat(m, 0) == 1); }
        assert(c_peel.u == w / m);
        assert(c_peel.a == 0);   // w % m == 0
        // ── Step 2 (j==0): INSERT directly (q_dw, 0, 1, q_bk, R). ──
        lemma_tm_step_picks(tm, c_peel, i_ins);
        let c_ins = apply_quint(tm.quints[i_ins], c_peel, m);
        assert(tm_step(tm, c_peel) == Some(c_ins));
        // R-move, a2 == 1: u = (w/m)·m + 1 == w + 1, v = v1/m == out, a = v1%m == 0.
        assert(c_ins.u == (w / m) * m + 1);
        assert((w / m) * m == w) by(nonlinear_arith) requires m * (w / m) == w;
        assert(c_ins.u == w + 1);
        assert(c_ins.v == out);
        assert(c_ins.a == 0);
        assert(c_ins.q == q_bk);
        // dec_u(0,w) + m^0 == w + 1.
        assert(pow_nat(m, 0) == 1);
        assert((dec_u(0, w, m) + pow_nat(m, 0)) as nat == w + 1) by { assert(dec_u(0, w, m) == w); }
        assert(c_ins == (TmConfig { u: (dec_u(0, w, m) + pow_nat(m, 0)) as nat, v: out, a: 0, q: q_bk }));
        assert(tm_run(tm, c_ins, 0) == c_ins);
        assert(tm_run(tm, c_peel, 1) == c_ins);
        lemma_tm_run_split(tm, c0, 1, 1);
        assert((2 * j + 2) as nat == 2);
        assert(tm_run(tm, c0, 2) == c_ins);
    } else {
        // u0 == dec_u(j,w), j>=1: %m==1, /m==dec_u(j-1,w). Head onto temp's low one (a==1).
        lemma_dec_u_step(j, w, m);   // dec_u(j,w)%m==1, /m==dec_u(j-1,w)
        assert(c_peel.u == dec_u((j - 1) as nat, w, m));
        assert(c_peel.a == 1);

        // ── Step 2: walk-left over temp's ones (j steps) to the separator. ──
        // dec_u(j-1,w) == repunit(j-1) + m^(j-1)·w (matches lemma_walk_left_prefix's shape).
        lemma_walk_left_prefix(tm, c_peel, q_dw, (j - 1) as nat, w, i_one_l);
        let c_sep = TmConfig { u: w / m, v: pile_ones(v1, j, m), a: w % m, q: q_dw };
        assert(((j - 1) + 1) as nat == j);
        assert(tm_run(tm, c_peel, j) == c_sep);
        lemma_tm_run_split(tm, c0, 1, j);
        assert(tm_run(tm, c0, (1 + j) as nat) == c_sep);

        // ── Step 3: INSERT-turnaround at the separator (a == w%m == 0). ──
        assert(c_sep.a == 0);   // w % m == 0
        lemma_tm_step_picks(tm, c_sep, i_ins);
        let c_ins = apply_quint(tm.quints[i_ins], c_sep, m);
        assert(tm_step(tm, c_sep) == Some(c_ins));
        lemma_pile_ones_div_mod(v1, j, m);   // pile_ones(v1,j)%m==1, /m==pile_ones(v1,j-1)
        // R-move, a2 == 1: u = (w/m)·m + 1 == w + 1, v = pile_ones(v1,j)/m, a = pile_ones(v1,j)%m == 1.
        assert((w / m) * m == w) by(nonlinear_arith) requires m * (w / m) == w;
        assert(c_ins.u == w + 1);
        assert(c_ins.v == pile_ones(v1, (j - 1) as nat, m));
        assert(c_ins.a == 1);
        assert(c_ins.q == q_bk);
        assert(tm_run(tm, c_ins, 0) == c_ins);
        assert(tm_run(tm, c_sep, 1) == c_ins);
        lemma_tm_run_split(tm, c0, (1 + j) as nat, 1);
        assert(tm_run(tm, c0, (1 + j + 1) as nat) == c_ins);

        // ── Step 4: walk-back (j steps): k0=0, rem0=j-1, w_hi = w+1. u == w+1 == repunit(0)+m^0·(w+1). ──
        assert(pow_nat(m, 0) == 1);
        lemma_repunit_zero(m);
        assert(c_ins.u == repunit_m(0, m) + pow_nat(m, 0) * (w + 1)) by(nonlinear_arith)
            requires c_ins.u == w + 1, repunit_m(0, m) == 0, pow_nat(m, 0) == 1;
        lemma_walk_back_prefix(tm, c_ins, q_bk, 0, (j - 1) as nat, v1, (w + 1) as nat, i_one_r);
        let c_final = TmConfig {
            u: repunit_m(j, m) + pow_nat(m, j) * (w + 1),
            v: v1 / m, a: v1 % m, q: q_bk };
        assert((0 + (j - 1) + 1) as nat == j);
        assert(tm_run(tm, c_ins, j) == c_final);
        // c_final.u == repunit(j) + m^j·(w+1) == dec_u(j,w) + m^j.
        assert(c_final.u == (dec_u(j, w, m) + pow_nat(m, j)) as nat) by(nonlinear_arith)
            requires
                c_final.u == repunit_m(j, m) + pow_nat(m, j) * (w + 1),
                dec_u(j, w, m) == repunit_m(j, m) + pow_nat(m, j) * w;
        assert(c_final.v == out);   // v1 / m
        assert(c_final.a == 0);     // v1 % m
        assert(c_final == (TmConfig { u: (dec_u(j, w, m) + pow_nat(m, j)) as nat, v: out, a: 0,
            q: q_bk }));
        lemma_tm_run_split(tm, c0, (1 + j + 1) as nat, j);
        assert((1 + j + 1 + j) as nat == (2 * j + 2) as nat);
        assert(tm_run(tm, c0, (2 * j + 2) as nat) == c_final);
    }
}

} // verus!
