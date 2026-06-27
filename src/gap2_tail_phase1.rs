//! # GAP-2 G2-F — tail-safety of copy_refresh's PHASE 1 (the marked-copy loop)
//!
//! Discharges [`crate::gap2_tail_lift::tail_safe`] for the phase-1 gadgets of `tm_copy_refresh` — the
//! `deposit`/`mark`/`copy_iter`/`copy_loop` family that builds `copy_u(0) → copy_u(M)` (each master one
//! marked `1 → 5`, temp grown to `M`). Same mirror-and-chain recipe as [`crate::gap2_tail_phases`]: copy
//! each source gadget's segment decomposition, apply the per-segment walk/step companions at the tracked
//! offset, chain with [`crate::gap2_tail_lift::lemma_tail_chain`].
//!
//! Phase 1 is **shallow**: every gadget enters at the home pivot offset `H_0 = g+M+1` and the deepest
//! leftward excursion lands at offset `M − j ≥ 1` (the mark reaches the master's lowest *unmarked* one,
//! never the blank above the all-fives master), so unlike `terminate`/`unmark` (phases 2 & 3) NO segment
//! is tight. Each gadget has **net displacement 0** (return to the pivot), so it re-enters at `H_0`.
//!
//! The two ones-walk primitives `deposit` uses (`walk_left_prefix`, `walk_back_prefix` from
//! `tm_dec_master`) are the `s = 1` specializations of the general walks, so their tail-safety IS the
//! existing [`crate::gap2_tail_walks::lemma_run_walk_left_tail_safe`] /
//! [`crate::gap2_tail_walks::lemma_run_walk_right_tail_safe`] — the only bridge needed is
//! `pile_ones == pile_sym(·, 1, ·)` ([`lemma_pile_ones_eq_pile_sym`]).
//!
//! Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
use verus_group_theory::machine_group::Dir;
use verus_group_theory::word_numbering::lemma_div_mod_step;
use crate::tm::{Tm, TmConfig, tm_wf, tm_run, tm_step, apply_quint, quint_matches};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};
use crate::tm_two_counter::{repunit_m, lemma_repunit_zero, lemma_repunit_step};
use crate::tm_dstring::{pow_nat, lemma_pow_nat_unfold};
use crate::tm_dec_master::{dec_u, lemma_walk_left_prefix, lemma_walk_back_prefix};
use crate::tm_block_loop::lemma_dec_u_step;
use crate::tm_walk::{pile_ones, lemma_pile_ones_div_mod};
use crate::tm_emit::{pile_sym, lemma_pile_sym_shift};
use crate::tm_run_lemmas::lemma_tm_run_split;
use crate::tm_copy_refresh::{copy_u, master_at, lemma_copy_u_master, lemma_pow_nat_add,
    lemma_run_walk_left, lemma_seek_left_blanks, lemma_run_walk_right, lemma_seek_right_blanks,
    lemma_master_at_step, lemma_mark_fwd, lemma_pile_sym_div_mod, lemma_mark,
    copy_loop_fuel, lemma_copy_loop_general};
use crate::gap2_tail_lift::{tail_safe, tail_end_h, lemma_step_tail_safe, lemma_tail_chain};
use crate::gap2_tail_walks::{lemma_run_walk_left_tail_safe, lemma_run_walk_right_tail_safe,
    lemma_seek_left_tail_safe, lemma_seek_right_tail_safe};

verus! {

/// **`pile_ones` is `pile_sym` with symbol `1`.** The two accumulators (`tm_walk::pile_ones`,
/// `tm_emit::pile_sym`) share the same `·m + s` push recurrence; with `s = 1` they coincide. The bridge
/// that lets the deposit companion reuse the general-symbol walk-right companion on the ones-pile.
pub proof fn lemma_pile_ones_eq_pile_sym(v: nat, k: nat, m: nat)
    ensures
        pile_ones(v, k, m) == pile_sym(v, 1, k, m),
    decreases k,
{
    if k == 0 {
    } else {
        lemma_pile_ones_eq_pile_sym(v, (k - 1) as nat, m);
    }
}

/// **`deposit` is tail-safe** for its `2j + 2` steps when the tail enters at offset `h ≥ j + 1`, and the
/// offset RETURNS to `h` (net displacement 0). Mirror of [`crate::tm_copy_refresh::lemma_deposit`]: the
/// `j = 0` branch is peel(L)·insert(R); the `j ≥ 1` branch is peel(L)·walkleft(L,j)·insert(R)·walkback(R,j).
/// The deepest excursion is `h − 1 − j ≥ 0` (after the walk-left), never tight on the phase path
/// (`h = H_0 = g+M+1`, `j ≤ M−1` ⟹ `h−1−j ≥ g+1`). The two ones-walks are the `s = 1` general walks.
pub proof fn lemma_deposit_tail_safe(
    tm: Tm, j: nat, w: nat, out: nat,
    q_dh: nat, q_dw: nat, q_bk: nat,
    i_pivot: int, i_one_l: int, i_ins: int, i_one_r: int,
    h: nat,
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
        h >= j + 1,
    ensures
        tail_safe(tm, TmConfig { u: dec_u(j, w, tm.m), v: out, a: 0, q: q_dh }, (2 * j + 2) as nat, h),
        tail_end_h(tm, TmConfig { u: dec_u(j, w, tm.m), v: out, a: 0, q: q_dh }, (2 * j + 2) as nat, h)
            == h,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 2);
    let c0 = TmConfig { u: dec_u(j, w, m), v: out, a: 0, q: q_dh };
    let v1 = out * m;
    lemma_div_mod_step(out, m, 0);
    assert(out * m + 0 == v1);
    lemma_fundamental_div_mod(w as int, m as int);
    assert(w == m * (w / m)) by { assert(w % m == 0); }
    assert(m * (w / m) == w);

    // ── S1: peel the pivot (q_dh, 0, 0, q_dw, L). offset h → h-1. ──
    lemma_tm_step_picks(tm, c0, i_pivot);
    let c_peel = apply_quint(tm.quints[i_pivot], c0, m);
    assert(tm_step(tm, c0) == Some(c_peel));
    assert(c_peel.v == v1);
    assert(c_peel.q == q_dw);
    assert(tm_run(tm, c_peel, 0) == c_peel);
    assert(tm_run(tm, c0, 1) == c_peel);
    assert(quint_matches(tm.quints[i_pivot], c0));
    lemma_step_tail_safe(tm, c0, i_pivot, h);   // L, end h-1 (h >= j+1 >= 1)

    if j == 0 {
        assert(dec_u(0, w, m) == w) by { lemma_repunit_zero(m); assert(pow_nat(m, 0) == 1); }
        assert(c_peel.u == w / m);
        assert(c_peel.a == 0);   // w % m == 0
        // ── S2 (j==0): INSERT directly (q_dw, 0, 1, q_bk, R). offset h-1 → h. ──
        lemma_tm_step_picks(tm, c_peel, i_ins);
        let c_ins = apply_quint(tm.quints[i_ins], c_peel, m);
        assert(tm_step(tm, c_peel) == Some(c_ins));
        assert((w / m) * m == w) by(nonlinear_arith) requires m * (w / m) == w;
        assert(c_ins.u == w + 1);
        assert(c_ins.q == q_bk);
        assert(tm_run(tm, c_ins, 0) == c_ins);
        assert(tm_run(tm, c_peel, 1) == c_ins);
        lemma_tm_run_split(tm, c0, 1, 1);
        assert((2 * j + 2) as nat == 2);
        assert(tm_run(tm, c0, 2) == c_ins);
        // tail_safe S2 + chain:
        assert(quint_matches(tm.quints[i_ins], c_peel));
        lemma_step_tail_safe(tm, c_peel, i_ins, (h - 1) as nat);   // R, end h
        assert(((h - 1) + 1) as nat == h);
        lemma_tail_chain(tm, c0, 1, 1, h, (h - 1) as nat, h);
    } else {
        lemma_dec_u_step(j, w, m);   // dec_u(j,w)%m==1, /m==dec_u(j-1,w)
        assert(c_peel.u == dec_u((j - 1) as nat, w, m));
        assert(c_peel.a == 1);

        // ── S2: walk-left over temp's ones (j steps, q_dw). offset h-1 → h-1-j. ──
        lemma_walk_left_prefix(tm, c_peel, q_dw, (j - 1) as nat, w, i_one_l);
        let c_sep = TmConfig { u: w / m, v: pile_ones(v1, j, m), a: w % m, q: q_dw };
        assert(((j - 1) + 1) as nat == j);
        assert(tm_run(tm, c_peel, j) == c_sep);
        lemma_tm_run_split(tm, c0, 1, j);
        assert(tm_run(tm, c0, (1 + j) as nat) == c_sep);
        // companion (s=1): c_peel.u == 1·R(j-1) + m^(j-1)·w.
        assert(c_peel.u == 1 * repunit_m((j - 1) as nat, m) + pow_nat(m, (j - 1) as nat) * w)
            by(nonlinear_arith)
            requires c_peel.u == dec_u((j - 1) as nat, w, m),
                dec_u((j - 1) as nat, w, m)
                    == repunit_m((j - 1) as nat, m) + pow_nat(m, (j - 1) as nat) * w;
        lemma_run_walk_left_tail_safe(tm, c_peel, q_dw, 1, (j - 1) as nat, w, i_one_l, (h - 1) as nat);
        assert(((h - 1) - j) as nat == (h - 1 - j) as nat);
        lemma_tail_chain(tm, c0, 1, j, h, (h - 1) as nat, (h - 1 - j) as nat);

        // ── S3: INSERT-turnaround (q_dw, 0, 1, q_bk, R). offset h-1-j → h-j. ──
        assert(c_sep.a == 0);   // w % m == 0
        lemma_tm_step_picks(tm, c_sep, i_ins);
        let c_ins = apply_quint(tm.quints[i_ins], c_sep, m);
        assert(tm_step(tm, c_sep) == Some(c_ins));
        lemma_pile_ones_div_mod(v1, j, m);
        assert((w / m) * m == w) by(nonlinear_arith) requires m * (w / m) == w;
        assert(c_ins.u == w + 1);
        assert(c_ins.v == pile_ones(v1, (j - 1) as nat, m));
        assert(c_ins.a == 1);
        assert(c_ins.q == q_bk);
        assert(tm_run(tm, c_ins, 0) == c_ins);
        assert(tm_run(tm, c_sep, 1) == c_ins);
        lemma_tm_run_split(tm, c0, (1 + j) as nat, 1);
        assert(tm_run(tm, c0, (1 + j + 1) as nat) == c_ins);
        // tail_safe S3 + chain:
        assert(quint_matches(tm.quints[i_ins], c_sep));
        lemma_step_tail_safe(tm, c_sep, i_ins, (h - 1 - j) as nat);   // R, end h-j
        assert(((h - 1 - j) + 1) as nat == (h - j) as nat);
        lemma_tail_chain(tm, c0, (1 + j) as nat, 1, h, (h - 1 - j) as nat, (h - j) as nat);

        // ── S4: walk-back (j steps, q_bk). offset h-j → h. ──
        assert(pow_nat(m, 0) == 1);
        lemma_repunit_zero(m);
        assert(c_ins.u == repunit_m(0, m) + pow_nat(m, 0) * (w + 1)) by(nonlinear_arith)
            requires c_ins.u == w + 1, repunit_m(0, m) == 0, pow_nat(m, 0) == 1;
        lemma_walk_back_prefix(tm, c_ins, q_bk, 0, (j - 1) as nat, v1, (w + 1) as nat, i_one_r);
        let c_final = TmConfig {
            u: repunit_m(j, m) + pow_nat(m, j) * (w + 1), v: v1 / m, a: v1 % m, q: q_bk };
        assert((0 + (j - 1) + 1) as nat == j);
        assert(tm_run(tm, c_ins, j) == c_final);
        lemma_tm_run_split(tm, c0, (1 + j + 1) as nat, j);
        assert((1 + j + 1 + j) as nat == (2 * j + 2) as nat);
        assert(tm_run(tm, c0, (2 * j + 2) as nat) == c_final);
        // companion (s=1): c_ins.u == 1·R(0) + m^0·(w+1); c_ins.v == pile_sym(v1, 1, j-1).
        assert(c_ins.u == 1 * repunit_m(0, m) + pow_nat(m, 0) * (w + 1)) by(nonlinear_arith)
            requires c_ins.u == w + 1, repunit_m(0, m) == 0, pow_nat(m, 0) == 1;
        lemma_pile_ones_eq_pile_sym(v1, (j - 1) as nat, m);
        assert(c_ins.v == pile_sym(v1, 1, (j - 1) as nat, m));
        lemma_run_walk_right_tail_safe(tm, c_ins, q_bk, 1, 0, (j - 1) as nat, v1, (w + 1) as nat,
            i_one_r, (h - j) as nat);
        assert(((h - j) + (j - 1) + 1) as nat == h);
        lemma_tail_chain(tm, c0, (1 + j + 1) as nat, j, h, (h - j) as nat, h);
    }
}

/// **`mark_fwd` is tail-safe** for its `g + j + 1` steps when the tail enters at `H_0 = g+M+1`, and the
/// offset is driven to exactly `M − j` (the head lands on the master's LOWEST UNMARKED one, `M − j` cells
/// below the tail). Mirror of [`crate::tm_copy_refresh::lemma_mark_fwd`]: six L-segments (peel, temp-walk,
/// t2g, gap-seek, a2b, fives-walk), chained by [`lemma_tail_chain`]. NOT tight — `M − j ≥ 1`. The `j == 1`
/// branch stops at the a2b transition (no trailing fives-walk).
pub proof fn lemma_mark_fwd_tail_safe(
    tm: Tm, j: nat, big_m: nat, g: nat, out: nat,
    q_mh: nat, q_t: nat, q_a: nat, q_b: nat,
    i_peel: int, i_temp: int, i_t2g: int, i_gap: int, i_a2b: int, i_fives: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        1 <= j < big_m,
        g >= j + 2,
        0 <= i_peel < tm.quints.len(),
        0 <= i_temp < tm.quints.len(),
        0 <= i_t2g < tm.quints.len(),
        0 <= i_gap < tm.quints.len(),
        0 <= i_a2b < tm.quints.len(),
        0 <= i_fives < tm.quints.len(),
        tm.quints[i_peel] == mk_quint(q_mh, 0, 0, q_t, Dir::L),
        tm.quints[i_temp] == mk_quint(q_t, 1, 1, q_t, Dir::L),
        tm.quints[i_t2g] == mk_quint(q_t, 0, 0, q_a, Dir::L),
        tm.quints[i_gap] == mk_quint(q_a, 0, 0, q_a, Dir::L),
        tm.quints[i_a2b] == mk_quint(q_a, 5, 5, q_b, Dir::L),
        tm.quints[i_fives] == mk_quint(q_b, 5, 5, q_b, Dir::L),
    ensures
        tail_safe(tm, TmConfig { u: copy_u(j, big_m, g, tm.m), v: out, a: 0, q: q_mh },
            (g + j + 1) as nat, (g + big_m + 1) as nat),
        tail_end_h(tm, TmConfig { u: copy_u(j, big_m, g, tm.m), v: out, a: 0, q: q_mh },
            (g + j + 1) as nat, (g + big_m + 1) as nat) == (big_m - j) as nat,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let h0 = (g + big_m + 1) as nat;
    let ms = master_at(j, big_m, m);
    lemma_copy_u_master(j, big_m, g, m);   // copy_u(j) == R(j) + m^g·ms
    let c0 = TmConfig { u: copy_u(j, big_m, g, m), v: out, a: 0, q: q_mh };

    // ── S1: pivot-peel (L). offset h0 → g+M. ──
    lemma_repunit_step((j - 1) as nat, m);
    lemma_pow_nat_unfold(m, g);
    let u1 = repunit_m((j - 1) as nat, m) + pow_nat(m, (g - 1) as nat) * ms;
    assert(copy_u(j, big_m, g, m) == u1 * m + 1) by(nonlinear_arith)
        requires
            copy_u(j, big_m, g, m) == repunit_m(j, m) + pow_nat(m, g) * ms,
            repunit_m(j, m) == m * repunit_m((j - 1) as nat, m) + 1,
            pow_nat(m, g) == m * pow_nat(m, (g - 1) as nat),
            u1 == repunit_m((j - 1) as nat, m) + pow_nat(m, (g - 1) as nat) * ms;
    lemma_div_mod_step(u1, m, 1);
    lemma_tm_step_picks(tm, c0, i_peel);
    let c1 = apply_quint(tm.quints[i_peel], c0, m);
    assert(tm_step(tm, c0) == Some(c1));
    assert(c1.u == u1 && c1.v == out * m && c1.a == 1 && c1.q == q_t);
    assert(tm_run(tm, c1, 0) == c1);
    assert(tm_run(tm, c0, 1) == c1);
    assert(quint_matches(tm.quints[i_peel], c0));
    lemma_step_tail_safe(tm, c0, i_peel, h0);   // L, end g+M

    // ── S2: walk-left over temp (j steps), q_t. offset g+M → g+M-j. ──
    let w_a = pow_nat(m, (g - j) as nat) * ms;
    lemma_pow_nat_add(m, (j - 1) as nat, (g - j) as nat);
    assert(((j - 1) + (g - j)) as nat == (g - 1) as nat);
    assert(c1.u == repunit_m((j - 1) as nat, m) + pow_nat(m, (j - 1) as nat) * w_a) by(nonlinear_arith)
        requires
            c1.u == repunit_m((j - 1) as nat, m) + pow_nat(m, (g - 1) as nat) * ms,
            pow_nat(m, (g - 1) as nat) == pow_nat(m, (j - 1) as nat) * pow_nat(m, (g - j) as nat),
            w_a == pow_nat(m, (g - j) as nat) * ms;
    lemma_run_walk_left(tm, c1, q_t, 1, (j - 1) as nat, w_a, i_temp);
    lemma_pow_nat_unfold(m, (g - j) as nat);
    assert(w_a == (pow_nat(m, (g - j - 1) as nat) * ms) * m) by(nonlinear_arith)
        requires w_a == pow_nat(m, (g - j) as nat) * ms,
            pow_nat(m, (g - j) as nat) == m * pow_nat(m, (g - j - 1) as nat);
    lemma_div_mod_step(pow_nat(m, (g - j - 1) as nat) * ms, m, 0);
    let pile_temp = pile_sym(out * m, 1, j, m);
    let c2 = TmConfig { u: pow_nat(m, (g - j - 1) as nat) * ms, v: pile_temp, a: 0, q: q_t };
    assert(((j - 1) + 1) as nat == j);
    assert(tm_run(tm, c1, j) == c2);
    lemma_tm_run_split(tm, c0, 1, j);
    assert(tm_run(tm, c0, (1 + j) as nat) == c2);
    // companion (s=1): c1.u == 1·R(j-1) + m^(j-1)·w_a.
    assert(c1.u == 1 * repunit_m((j - 1) as nat, m) + pow_nat(m, (j - 1) as nat) * w_a)
        by(nonlinear_arith)
        requires c1.u == repunit_m((j - 1) as nat, m) + pow_nat(m, (j - 1) as nat) * w_a;
    lemma_run_walk_left_tail_safe(tm, c1, q_t, 1, (j - 1) as nat, w_a, i_temp, (g + big_m) as nat);
    assert(((g + big_m) - j) as nat == (g + big_m - j) as nat);
    lemma_tail_chain(tm, c0, 1, j, h0, (g + big_m) as nat, (g + big_m - j) as nat);

    // ── S3: temp→gap (L). offset g+M-j → g+M-j-1. ──
    lemma_pow_nat_unfold(m, (g - j - 1) as nat);
    assert(c2.u == (pow_nat(m, (g - j - 2) as nat) * ms) * m) by(nonlinear_arith)
        requires c2.u == pow_nat(m, (g - j - 1) as nat) * ms,
            pow_nat(m, (g - j - 1) as nat) == m * pow_nat(m, (g - j - 2) as nat);
    lemma_div_mod_step(pow_nat(m, (g - j - 2) as nat) * ms, m, 0);
    lemma_tm_step_picks(tm, c2, i_t2g);
    let c3 = apply_quint(tm.quints[i_t2g], c2, m);
    assert(tm_step(tm, c2) == Some(c3));
    assert(c3.u == pow_nat(m, (g - j - 2) as nat) * ms && c3.v == pile_temp * m && c3.a == 0
        && c3.q == q_a);
    assert(tm_run(tm, c3, 0) == c3);
    assert(tm_run(tm, c2, 1) == c3);
    lemma_tm_run_split(tm, c0, (1 + j) as nat, 1);
    assert(tm_run(tm, c0, (1 + j + 1) as nat) == c3);
    assert(quint_matches(tm.quints[i_t2g], c2));
    lemma_step_tail_safe(tm, c2, i_t2g, (g + big_m - j) as nat);   // L, end g+M-j-1
    assert(((g + big_m - j) - 1) as nat == (g + big_m - j - 1) as nat);
    lemma_tail_chain(tm, c0, (1 + j) as nat, 1, h0, (g + big_m - j) as nat, (g + big_m - j - 1) as nat);

    // ── S4: seek-left over the remaining gap (g-j-1 steps), q_a. offset g+M-j-1 → M. ──
    lemma_pow_nat_unfold(m, j);
    let ms_div = 5 * repunit_m((j - 1) as nat, m)
        + pow_nat(m, (j - 1) as nat) * repunit_m((big_m - j) as nat, m);
    assert(ms == ms_div * m + 5) by(nonlinear_arith)
        requires
            ms == 5 * repunit_m(j, m) + pow_nat(m, j) * repunit_m((big_m - j) as nat, m),
            repunit_m(j, m) == m * repunit_m((j - 1) as nat, m) + 1,
            pow_nat(m, j) == m * pow_nat(m, (j - 1) as nat),
            ms_div == 5 * repunit_m((j - 1) as nat, m)
                + pow_nat(m, (j - 1) as nat) * repunit_m((big_m - j) as nat, m);
    lemma_div_mod_step(ms_div, m, 5);   // ms%m==5, ms/m==ms_div
    assert(ms % m != 0);
    lemma_seek_left_blanks(tm, c3, q_a, (g - j - 2) as nat, ms, i_gap);
    lemma_pow_nat_unfold(m, (g - j) as nat);
    let c4 = TmConfig { u: ms_div, v: (pile_temp * m) * pow_nat(m, (g - j - 1) as nat), a: 5, q: q_a };
    assert(((g - j - 2) + 1) as nat == (g - j - 1) as nat);
    assert(tm_run(tm, c3, (g - j - 1) as nat) == c4);
    lemma_tm_run_split(tm, c0, (1 + j + 1) as nat, (g - j - 1) as nat);
    assert((1 + j + 1 + (g - j - 1)) as nat == (g + 1) as nat);
    assert(tm_run(tm, c0, (g + 1) as nat) == c4);
    let big_v = pile_temp * pow_nat(m, (g - j) as nat);
    assert((pile_temp * m) * pow_nat(m, (g - j - 1) as nat) == big_v) by(nonlinear_arith)
        requires big_v == pile_temp * pow_nat(m, (g - j) as nat),
            pow_nat(m, (g - j) as nat) == m * pow_nat(m, (g - j - 1) as nat);
    assert(c4.v == big_v);
    // tail_safe S4 + chain. seek companion: c3.u == m^(g-j-2)·ms, ms%m != 0.
    lemma_seek_left_tail_safe(tm, c3, q_a, (g - j - 2) as nat, ms, i_gap, (g + big_m - j - 1) as nat);
    assert(((g + big_m - j - 1) - (g - j - 1)) as nat == big_m);
    lemma_tail_chain(tm, c0, (1 + j + 1) as nat, (g - j - 1) as nat, h0, (g + big_m - j - 1) as nat,
        big_m);

    // ── S5: a2b transition (q_a, 5, 5, q_b, L). offset M → M-1. ──
    lemma_repunit_step((big_m - j - 1) as nat, m);
    assert(((big_m - j - 1) + 1) as nat == (big_m - j) as nat);
    assert(repunit_m((big_m - j) as nat, m) == repunit_m((big_m - j - 1) as nat, m) * m + 1)
        by(nonlinear_arith)
        requires repunit_m((big_m - j) as nat, m) == m * repunit_m((big_m - j - 1) as nat, m) + 1;
    lemma_div_mod_step(repunit_m((big_m - j - 1) as nat, m), m, 1);
    lemma_tm_step_picks(tm, c4, i_a2b);
    let c4b = apply_quint(tm.quints[i_a2b], c4, m);
    assert(tm_step(tm, c4) == Some(c4b));
    assert(c4b.u == ms_div / m && c4b.v == big_v * m + 5 && c4b.a == ms_div % m && c4b.q == q_b);
    assert(tm_run(tm, c4b, 0) == c4b);
    assert(tm_run(tm, c4, 1) == c4b);
    lemma_tm_run_split(tm, c0, (g + 1) as nat, 1);
    assert(tm_run(tm, c0, (g + 2) as nat) == c4b);
    assert(quint_matches(tm.quints[i_a2b], c4));
    lemma_step_tail_safe(tm, c4, i_a2b, big_m);   // L, end M-1
    lemma_tail_chain(tm, c0, (g + 1) as nat, 1, h0, big_m, (big_m - 1) as nat);

    let c5 = TmConfig {
        u: repunit_m((big_m - j - 1) as nat, m), v: pile_sym(big_v, 5, j, m), a: 1, q: q_b };
    assert(pile_sym(big_v, 5, 0, m) == big_v);
    assert(pile_sym(big_v, 5, 1, m) == pile_sym(big_v, 5, 0, m) * m + 5);
    if j == 1 {
        // a2b already lands on the lowest unmarked one; mark_fwd ends at c4b == c5, offset M-1 == M-j.
        lemma_repunit_zero(m);
        assert(pow_nat(m, 0) == 1);
        assert(ms_div == repunit_m((big_m - 1) as nat, m)) by(nonlinear_arith)
            requires
                ms_div == 5 * repunit_m((j - 1) as nat, m)
                    + pow_nat(m, (j - 1) as nat) * repunit_m((big_m - j) as nat, m),
                (j - 1) as nat == 0,
                repunit_m(0, m) == 0,
                pow_nat(m, 0) == 1,
                (big_m - j) as nat == (big_m - 1) as nat;
        assert((big_m - j - 1) as nat == (big_m - 1 - 1) as nat);
        assert(ms_div == repunit_m((big_m - 2) as nat, m) * m + 1) by(nonlinear_arith)
            requires
                ms_div == repunit_m((big_m - 1) as nat, m),
                repunit_m((big_m - 1) as nat, m) == m * repunit_m((big_m - 2) as nat, m) + 1;
        assert(c4b == c5);
        assert((g + 2) as nat == (g + j + 1) as nat);
        assert((big_m - 1) as nat == (big_m - j) as nat);
        // tail_safe already at (g+2, h0) ending M-1 == M-j; no S6.
    } else {
        // j ≥ 2: a2b lands on the 2nd five; walk the rest. offset M-1 → M-j.
        let ms_div2 = 5 * repunit_m((j - 2) as nat, m)
            + pow_nat(m, (j - 2) as nat) * repunit_m((big_m - j) as nat, m);
        lemma_repunit_step((j - 2) as nat, m);
        assert(((j - 2) + 1) as nat == (j - 1) as nat);
        lemma_pow_nat_unfold(m, (j - 1) as nat);
        assert(ms_div == ms_div2 * m + 5) by(nonlinear_arith)
            requires
                ms_div == 5 * repunit_m((j - 1) as nat, m)
                    + pow_nat(m, (j - 1) as nat) * repunit_m((big_m - j) as nat, m),
                repunit_m((j - 1) as nat, m) == m * repunit_m((j - 2) as nat, m) + 1,
                pow_nat(m, (j - 1) as nat) == m * pow_nat(m, (j - 2) as nat),
                ms_div2 == 5 * repunit_m((j - 2) as nat, m)
                    + pow_nat(m, (j - 2) as nat) * repunit_m((big_m - j) as nat, m);
        lemma_div_mod_step(ms_div2, m, 5);
        assert(c4b.u == ms_div2 && c4b.a == 5);
        lemma_run_walk_left(tm, c4b, q_b, 5, (j - 2) as nat, repunit_m((big_m - j) as nat, m), i_fives);
        lemma_pile_sym_shift(big_v, 5, (j - 1) as nat, m);
        assert(((j - 2) + 1) as nat == (j - 1) as nat);
        assert(((j - 1) + 1) as nat == j);
        assert(pile_sym(c4b.v, 5, ((j - 2) + 1) as nat, m) == pile_sym(big_v, 5, j, m));
        assert(tm_run(tm, c4b, ((j - 2) + 1) as nat) == c5);
        assert(tm_run(tm, c4b, (j - 1) as nat) == c5);
        lemma_tm_run_split(tm, c0, (g + 2) as nat, (j - 1) as nat);
        assert((g + 2 + (j - 1)) as nat == (g + j + 1) as nat);
        assert(tm_run(tm, c0, (g + j + 1) as nat) == c5);
        // companion (s=5): c4b.u == 5·R(j-2) + m^(j-2)·R(M-j).
        assert(c4b.u == 5 * repunit_m((j - 2) as nat, m)
            + pow_nat(m, (j - 2) as nat) * repunit_m((big_m - j) as nat, m)) by(nonlinear_arith)
            requires c4b.u == ms_div2,
                ms_div2 == 5 * repunit_m((j - 2) as nat, m)
                    + pow_nat(m, (j - 2) as nat) * repunit_m((big_m - j) as nat, m);
        lemma_run_walk_left_tail_safe(tm, c4b, q_b, 5, (j - 2) as nat,
            repunit_m((big_m - j) as nat, m), i_fives, (big_m - 1) as nat);
        assert(((big_m - 1) - ((j - 2) + 1)) as nat == (big_m - j) as nat);
        lemma_tail_chain(tm, c0, (g + 2) as nat, (j - 1) as nat, h0, (big_m - 1) as nat,
            (big_m - j) as nat);
        assert((g + 2 + (j - 1)) as nat == (g + j + 1) as nat);
    }
}

/// **`mark` is tail-safe** for its `2·(g + j + 1)` steps (general case `2 ≤ j < M`) when the tail enters
/// at `H_0 = g+M+1`, and the offset RETURNS to `H_0` (net displacement 0). The forward half is
/// [`lemma_mark_fwd_tail_safe`] (`H_0 → M−j`); the MARK turn and the entire return (S6–S10) are ALL
/// R-moves, so the offset lifts `M−j → H_0` unconditionally. Mirror of
/// [`crate::tm_copy_refresh::lemma_mark`].
pub proof fn lemma_mark_tail_safe(
    tm: Tm, j: nat, big_m: nat, g: nat, out: nat,
    q_mh: nat, q_t: nat, q_a: nat, q_b: nat, q_rf: nat, q_rg: nat, q_rt: nat,
    i_peel: int, i_temp: int, i_t2g: int, i_gap: int, i_a2b: int, i_fives: int, i_mark: int,
    i_rfives: int, i_rf2g: int, i_rgap: int, i_rg2t: int, i_rtemp: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        2 <= j < big_m,
        g >= j + 2,
        0 <= i_peel < tm.quints.len(),
        0 <= i_temp < tm.quints.len(),
        0 <= i_t2g < tm.quints.len(),
        0 <= i_gap < tm.quints.len(),
        0 <= i_a2b < tm.quints.len(),
        0 <= i_fives < tm.quints.len(),
        0 <= i_mark < tm.quints.len(),
        0 <= i_rfives < tm.quints.len(),
        0 <= i_rf2g < tm.quints.len(),
        0 <= i_rgap < tm.quints.len(),
        0 <= i_rg2t < tm.quints.len(),
        0 <= i_rtemp < tm.quints.len(),
        tm.quints[i_peel] == mk_quint(q_mh, 0, 0, q_t, Dir::L),
        tm.quints[i_temp] == mk_quint(q_t, 1, 1, q_t, Dir::L),
        tm.quints[i_t2g] == mk_quint(q_t, 0, 0, q_a, Dir::L),
        tm.quints[i_gap] == mk_quint(q_a, 0, 0, q_a, Dir::L),
        tm.quints[i_a2b] == mk_quint(q_a, 5, 5, q_b, Dir::L),
        tm.quints[i_fives] == mk_quint(q_b, 5, 5, q_b, Dir::L),
        tm.quints[i_mark] == mk_quint(q_b, 1, 5, q_rf, Dir::R),
        tm.quints[i_rfives] == mk_quint(q_rf, 5, 5, q_rf, Dir::R),
        tm.quints[i_rf2g] == mk_quint(q_rf, 0, 0, q_rg, Dir::R),
        tm.quints[i_rgap] == mk_quint(q_rg, 0, 0, q_rg, Dir::R),
        tm.quints[i_rg2t] == mk_quint(q_rg, 1, 1, q_rt, Dir::R),
        tm.quints[i_rtemp] == mk_quint(q_rt, 1, 1, q_rt, Dir::R),
    ensures
        tail_safe(tm, TmConfig { u: copy_u(j, big_m, g, tm.m), v: out, a: 0, q: q_mh },
            (2 * (g + j + 1)) as nat, (g + big_m + 1) as nat),
        tail_end_h(tm, TmConfig { u: copy_u(j, big_m, g, tm.m), v: out, a: 0, q: q_mh },
            (2 * (g + j + 1)) as nat, (g + big_m + 1) as nat) == (g + big_m + 1) as nat,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let h0 = (g + big_m + 1) as nat;
    let pile_temp = pile_sym(out * m, 1, j, m);
    let big_v = pile_temp * pow_nat(m, (g - j) as nat);
    let mm1 = repunit_m((big_m - j - 1) as nat, m);
    let ms_next = master_at((j + 1) as nat, big_m, m);
    let c0 = TmConfig { u: copy_u(j, big_m, g, m), v: out, a: 0, q: q_mh };

    // ── FORWARD: c0 → c5 (lowest unmarked one), g+j+1 steps. offset H_0 → M-j. ──
    lemma_mark_fwd(tm, j, big_m, g, out, q_mh, q_t, q_a, q_b,
        i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives);
    lemma_mark_fwd_tail_safe(tm, j, big_m, g, out, q_mh, q_t, q_a, q_b,
        i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives);
    let c5 = TmConfig { u: mm1, v: pile_sym(big_v, 5, j, m), a: 1, q: q_b };
    assert(tm_run(tm, c0, (g + j + 1) as nat) == c5);

    // ── MARK step (q_b, 1, 5, q_rf, R). offset M-j → M-j+1. ──
    lemma_pile_sym_div_mod(big_v, 5, j, m);
    lemma_tm_step_picks(tm, c5, i_mark);
    let c6 = apply_quint(tm.quints[i_mark], c5, m);
    assert(tm_step(tm, c5) == Some(c6));
    assert(c6.u == mm1 * m + 5 && c6.v == pile_sym(big_v, 5, (j - 1) as nat, m) && c6.a == 5
        && c6.q == q_rf);
    assert(tm_run(tm, c6, 0) == c6);
    assert(tm_run(tm, c5, 1) == c6);
    lemma_tm_run_split(tm, c0, (g + j + 1) as nat, 1);
    assert(tm_run(tm, c0, (g + j + 2) as nat) == c6);
    assert(quint_matches(tm.quints[i_mark], c5));
    lemma_step_tail_safe(tm, c5, i_mark, (big_m - j) as nat);   // R, end M-j+1
    assert(((big_m - j) + 1) as nat == (big_m - j + 1) as nat);
    lemma_tail_chain(tm, c0, (g + j + 1) as nat, 1, h0, (big_m - j) as nat, (big_m - j + 1) as nat);

    // ── S6: run_walk_right over fives (j steps), q_rf. offset M-j+1 → M+1. ──
    assert(pow_nat(m, 1) == m) by { lemma_pow_nat_unfold(m, 1); assert(pow_nat(m, 0) == 1); }
    assert(repunit_m(1, m) == 1) by { lemma_repunit_step(0, m); lemma_repunit_zero(m); }
    assert(c6.u == 5 * repunit_m(1, m) + pow_nat(m, 1) * mm1) by(nonlinear_arith)
        requires c6.u == mm1 * m + 5, repunit_m(1, m) == 1, pow_nat(m, 1) == m;
    lemma_run_walk_right(tm, c6, q_rf, 5, 1, (j - 1) as nat, big_v, mm1, i_rfives);
    assert((1 + (j - 1) + 1) as nat == (j + 1) as nat);
    assert((big_m - (j + 1)) as nat == (big_m - j - 1) as nat);
    assert(ms_next == 5 * repunit_m((j + 1) as nat, m) + pow_nat(m, (j + 1) as nat) * mm1);
    lemma_pow_nat_unfold(m, (g - j) as nat);
    assert(big_v == (pile_temp * pow_nat(m, (g - j - 1) as nat)) * m) by(nonlinear_arith)
        requires big_v == pile_temp * pow_nat(m, (g - j) as nat),
            pow_nat(m, (g - j) as nat) == m * pow_nat(m, (g - j - 1) as nat);
    lemma_div_mod_step(pile_temp * pow_nat(m, (g - j - 1) as nat), m, 0);
    let c7 = TmConfig { u: ms_next, v: pile_temp * pow_nat(m, (g - j - 1) as nat), a: 0, q: q_rf };
    assert(tm_run(tm, c6, j) == c7);
    lemma_tm_run_split(tm, c0, (g + j + 2) as nat, j);
    assert((g + j + 2 + j) as nat == (g + 2 * j + 2) as nat);
    assert(tm_run(tm, c0, (g + 2 * j + 2) as nat) == c7);
    lemma_run_walk_right_tail_safe(tm, c6, q_rf, 5, 1, (j - 1) as nat, big_v, mm1, i_rfives,
        (big_m - j + 1) as nat);
    assert(((big_m - j + 1) + (j - 1)) as nat == big_m);   // end (M-j+1)+(j-1)+1 == M+1
    assert(((big_m - j + 1) + (j - 1) + 1) as nat == (big_m + 1) as nat);
    lemma_tail_chain(tm, c0, (g + j + 2) as nat, j, h0, (big_m - j + 1) as nat, (big_m + 1) as nat);

    // ── S7: rf→gap transition (q_rf, 0, 0, q_rg, R). offset M+1 → M+2. ──
    lemma_pow_nat_unfold(m, (g - j - 1) as nat);
    assert(c7.v == (pile_temp * pow_nat(m, (g - j - 2) as nat)) * m) by(nonlinear_arith)
        requires c7.v == pile_temp * pow_nat(m, (g - j - 1) as nat),
            pow_nat(m, (g - j - 1) as nat) == m * pow_nat(m, (g - j - 2) as nat);
    lemma_div_mod_step(pile_temp * pow_nat(m, (g - j - 2) as nat), m, 0);
    lemma_tm_step_picks(tm, c7, i_rf2g);
    let c8 = apply_quint(tm.quints[i_rf2g], c7, m);
    assert(tm_step(tm, c7) == Some(c8));
    assert(c8.u == ms_next * m && c8.v == pile_temp * pow_nat(m, (g - j - 2) as nat) && c8.a == 0
        && c8.q == q_rg);
    assert(tm_run(tm, c8, 0) == c8);
    assert(tm_run(tm, c7, 1) == c8);
    lemma_tm_run_split(tm, c0, (g + 2 * j + 2) as nat, 1);
    assert(tm_run(tm, c0, (g + 2 * j + 3) as nat) == c8);
    assert(quint_matches(tm.quints[i_rf2g], c7));
    lemma_step_tail_safe(tm, c7, i_rf2g, (big_m + 1) as nat);   // R, end M+2
    assert(((big_m + 1) + 1) as nat == (big_m + 2) as nat);
    lemma_tail_chain(tm, c0, (g + 2 * j + 2) as nat, 1, h0, (big_m + 1) as nat, (big_m + 2) as nat);

    // ── S8: seek_right_blanks over the gap (g-j-1 steps), q_rg. offset M+2 → g+M-j+1. ──
    lemma_pile_sym_div_mod(out * m, 1, j, m);
    assert(c8.v == pow_nat(m, (g - j - 2) as nat) * pile_temp) by(nonlinear_arith)
        requires c8.v == pile_temp * pow_nat(m, (g - j - 2) as nat);
    lemma_seek_right_blanks(tm, c8, q_rg, (g - j - 2) as nat, pile_temp, i_rgap);
    let c9 = TmConfig { u: c8.u * pow_nat(m, (g - j - 1) as nat),
        v: pile_sym(out * m, 1, (j - 1) as nat, m), a: 1, q: q_rg };
    assert(((g - j - 2) + 1) as nat == (g - j - 1) as nat);
    assert(tm_run(tm, c8, (g - j - 1) as nat) == c9);
    lemma_tm_run_split(tm, c0, (g + 2 * j + 3) as nat, (g - j - 1) as nat);
    assert((g + 2 * j + 3 + (g - j - 1)) as nat == (2 * g + j + 2) as nat);
    assert(tm_run(tm, c0, (2 * g + j + 2) as nat) == c9);
    assert(c9.u == ms_next * pow_nat(m, (g - j) as nat)) by(nonlinear_arith)
        requires c9.u == (ms_next * m) * pow_nat(m, (g - j - 1) as nat),
            pow_nat(m, (g - j) as nat) == m * pow_nat(m, (g - j - 1) as nat);
    lemma_seek_right_tail_safe(tm, c8, q_rg, (g - j - 2) as nat, pile_temp, i_rgap, (big_m + 2) as nat);
    assert(((big_m + 2) + (g - j - 2) + 1) as nat == (g + big_m - j + 1) as nat);
    lemma_tail_chain(tm, c0, (g + 2 * j + 3) as nat, (g - j - 1) as nat, h0, (big_m + 2) as nat,
        (g + big_m - j + 1) as nat);

    // ── S9: rg→temp transition (q_rg, 1, 1, q_rt, R). offset g+M-j+1 → g+M-j+2. ──
    lemma_pile_sym_div_mod(out * m, 1, (j - 1) as nat, m);
    lemma_tm_step_picks(tm, c9, i_rg2t);
    let c10 = apply_quint(tm.quints[i_rg2t], c9, m);
    assert(tm_step(tm, c9) == Some(c10));
    assert(c10.u == c9.u * m + 1 && c10.v == pile_sym(out * m, 1, (j - 2) as nat, m) && c10.a == 1
        && c10.q == q_rt);
    assert(tm_run(tm, c10, 0) == c10);
    assert(tm_run(tm, c9, 1) == c10);
    lemma_tm_run_split(tm, c0, (2 * g + j + 2) as nat, 1);
    assert(tm_run(tm, c0, (2 * g + j + 3) as nat) == c10);
    assert(quint_matches(tm.quints[i_rg2t], c9));
    lemma_step_tail_safe(tm, c9, i_rg2t, (g + big_m - j + 1) as nat);   // R, end g+M-j+2
    assert(((g + big_m - j + 1) + 1) as nat == (g + big_m - j + 2) as nat);
    lemma_tail_chain(tm, c0, (2 * g + j + 2) as nat, 1, h0, (g + big_m - j + 1) as nat,
        (g + big_m - j + 2) as nat);

    // ── S10: run_walk_right over temp (j-1 steps), q_rt. offset g+M-j+2 → H_0. ──
    assert(c10.u == 1 * repunit_m(1, m) + pow_nat(m, 1) * c9.u) by(nonlinear_arith)
        requires c10.u == c9.u * m + 1, repunit_m(1, m) == 1, pow_nat(m, 1) == m;
    lemma_run_walk_right(tm, c10, q_rt, 1, 1, (j - 2) as nat, out * m, c9.u, i_rtemp);
    assert((1 + (j - 2) + 1) as nat == j);
    lemma_div_mod_step(out, m, 0);
    let c11 = TmConfig { u: repunit_m(j, m) + pow_nat(m, j) * c9.u, v: out, a: 0, q: q_rt };
    assert(tm_run(tm, c10, (j - 1) as nat) == c11);
    lemma_tm_run_split(tm, c0, (2 * g + j + 3) as nat, (j - 1) as nat);
    assert((2 * g + j + 3 + (j - 1)) as nat == (2 * (g + j + 1)) as nat);
    assert(tm_run(tm, c0, (2 * (g + j + 1)) as nat) == c11);
    lemma_run_walk_right_tail_safe(tm, c10, q_rt, 1, 1, (j - 2) as nat, out * m, c9.u, i_rtemp,
        (g + big_m - j + 2) as nat);
    assert(((g + big_m - j + 2) + (j - 2)) as nat == (g + big_m) as nat);   // end +(j-2)+1 == g+M+1
    assert(((g + big_m - j + 2) + (j - 2) + 1) as nat == (g + big_m + 1) as nat);
    lemma_tail_chain(tm, c0, (2 * g + j + 3) as nat, (j - 1) as nat, h0, (g + big_m - j + 2) as nat,
        h0);
    assert((2 * g + j + 3 + (j - 1)) as nat == (2 * (g + j + 1)) as nat);
}

/// **`copy_iter` is tail-safe** for its `2·(g+j+1) + (2·j+2)` steps (general `2 ≤ j < M`) when the tail
/// enters at `H_0 = g+M+1`, returning to `H_0` (both MARK and DEPOSIT are net-disp-0). Mirror of
/// [`crate::tm_copy_refresh::lemma_copy_iter`]: chain [`lemma_mark_tail_safe`] then
/// [`lemma_deposit_tail_safe`] at `H_0`.
pub proof fn lemma_copy_iter_tail_safe(
    tm: Tm, j: nat, big_m: nat, g: nat, out: nat,
    q_mh: nat, q_t: nat, q_a: nat, q_b: nat, q_rf: nat, q_rg: nat, q_rt: nat, q_dw: nat, q_bk: nat,
    i_peel: int, i_temp: int, i_t2g: int, i_gap: int, i_a2b: int, i_fives: int, i_mark: int,
    i_rfives: int, i_rf2g: int, i_rgap: int, i_rg2t: int, i_rtemp: int,
    i_dpeel: int, i_dtemp: int, i_dins: int, i_dwb: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        2 <= j < big_m,
        g >= j + 2,
        0 <= i_peel < tm.quints.len(),
        0 <= i_temp < tm.quints.len(),
        0 <= i_t2g < tm.quints.len(),
        0 <= i_gap < tm.quints.len(),
        0 <= i_a2b < tm.quints.len(),
        0 <= i_fives < tm.quints.len(),
        0 <= i_mark < tm.quints.len(),
        0 <= i_rfives < tm.quints.len(),
        0 <= i_rf2g < tm.quints.len(),
        0 <= i_rgap < tm.quints.len(),
        0 <= i_rg2t < tm.quints.len(),
        0 <= i_rtemp < tm.quints.len(),
        0 <= i_dpeel < tm.quints.len(),
        0 <= i_dtemp < tm.quints.len(),
        0 <= i_dins < tm.quints.len(),
        0 <= i_dwb < tm.quints.len(),
        tm.quints[i_peel] == mk_quint(q_mh, 0, 0, q_t, Dir::L),
        tm.quints[i_temp] == mk_quint(q_t, 1, 1, q_t, Dir::L),
        tm.quints[i_t2g] == mk_quint(q_t, 0, 0, q_a, Dir::L),
        tm.quints[i_gap] == mk_quint(q_a, 0, 0, q_a, Dir::L),
        tm.quints[i_a2b] == mk_quint(q_a, 5, 5, q_b, Dir::L),
        tm.quints[i_fives] == mk_quint(q_b, 5, 5, q_b, Dir::L),
        tm.quints[i_mark] == mk_quint(q_b, 1, 5, q_rf, Dir::R),
        tm.quints[i_rfives] == mk_quint(q_rf, 5, 5, q_rf, Dir::R),
        tm.quints[i_rf2g] == mk_quint(q_rf, 0, 0, q_rg, Dir::R),
        tm.quints[i_rgap] == mk_quint(q_rg, 0, 0, q_rg, Dir::R),
        tm.quints[i_rg2t] == mk_quint(q_rg, 1, 1, q_rt, Dir::R),
        tm.quints[i_rtemp] == mk_quint(q_rt, 1, 1, q_rt, Dir::R),
        tm.quints[i_dpeel] == mk_quint(q_rt, 0, 0, q_dw, Dir::L),
        tm.quints[i_dtemp] == mk_quint(q_dw, 1, 1, q_dw, Dir::L),
        tm.quints[i_dins] == mk_quint(q_dw, 0, 1, q_bk, Dir::R),
        tm.quints[i_dwb] == mk_quint(q_bk, 1, 1, q_bk, Dir::R),
    ensures
        tail_safe(tm, TmConfig { u: copy_u(j, big_m, g, tm.m), v: out, a: 0, q: q_mh },
            (2 * (g + j + 1) + (2 * j + 2)) as nat, (g + big_m + 1) as nat),
        tail_end_h(tm, TmConfig { u: copy_u(j, big_m, g, tm.m), v: out, a: 0, q: q_mh },
            (2 * (g + j + 1) + (2 * j + 2)) as nat, (g + big_m + 1) as nat) == (g + big_m + 1) as nat,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let h0 = (g + big_m + 1) as nat;
    let c0 = TmConfig { u: copy_u(j, big_m, g, m), v: out, a: 0, q: q_mh };
    let ms_next = master_at((j + 1) as nat, big_m, m);
    let w_dep = pow_nat(m, (g - j) as nat) * ms_next;

    // ── MARK: c0 → c_mid (= dec_u(j, w_dep)), 2·(g+j+1) steps. offset H_0 → H_0. ──
    lemma_mark(tm, j, big_m, g, out, q_mh, q_t, q_a, q_b, q_rf, q_rg, q_rt,
        i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives, i_mark, i_rfives, i_rf2g, i_rgap, i_rg2t, i_rtemp);
    lemma_copy_u_master(j, big_m, g, m);
    lemma_master_at_step(j, big_m, m);
    lemma_pow_nat_add(m, g, j);
    lemma_pow_nat_add(m, j, (g - j) as nat);
    assert((j + (g - j)) as nat == g);
    assert(copy_u(j, big_m, g, m) + 4 * pow_nat(m, (g + j) as nat) == dec_u(j, w_dep, m))
        by(nonlinear_arith)
        requires
            copy_u(j, big_m, g, m) == repunit_m(j, m) + pow_nat(m, g) * master_at(j, big_m, m),
            ms_next == master_at(j, big_m, m) + 4 * pow_nat(m, j),
            pow_nat(m, (g + j) as nat) == pow_nat(m, g) * pow_nat(m, j),
            pow_nat(m, g) == pow_nat(m, j) * pow_nat(m, (g - j) as nat),
            w_dep == pow_nat(m, (g - j) as nat) * ms_next,
            dec_u(j, w_dep, m) == repunit_m(j, m) + pow_nat(m, j) * w_dep;
    let c_mid = TmConfig { u: dec_u(j, w_dep, m), v: out, a: 0, q: q_rt };
    assert(tm_run(tm, c0, (2 * (g + j + 1)) as nat) == c_mid);
    lemma_mark_tail_safe(tm, j, big_m, g, out, q_mh, q_t, q_a, q_b, q_rf, q_rg, q_rt,
        i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives, i_mark, i_rfives, i_rf2g, i_rgap, i_rg2t, i_rtemp);

    // ── DEPOSIT (home state q_rt): c_mid → c_end, 2·j+2 steps. offset H_0 → H_0. w_dep%m==0. ──
    lemma_pow_nat_unfold(m, (g - j) as nat);
    assert(w_dep == (pow_nat(m, (g - j - 1) as nat) * ms_next) * m) by(nonlinear_arith)
        requires w_dep == pow_nat(m, (g - j) as nat) * ms_next,
            pow_nat(m, (g - j) as nat) == m * pow_nat(m, (g - j - 1) as nat);
    lemma_div_mod_step(pow_nat(m, (g - j - 1) as nat) * ms_next, m, 0);
    assert(w_dep % m == 0);
    lemma_deposit_tail_safe(tm, j, w_dep, out, q_rt, q_dw, q_bk,
        i_dpeel, i_dtemp, i_dins, i_dwb, h0);

    // ── chain DEPOSIT ∘ MARK at H_0. ──
    lemma_tail_chain(tm, c0, (2 * (g + j + 1)) as nat, (2 * j + 2) as nat, h0, h0, h0);
    assert((2 * (g + j + 1) + (2 * j + 2)) as nat == ((2 * (g + j + 1)) + (2 * j + 2)) as nat);
}

/// **`copy_loop_general` is tail-safe** for its `copy_loop_fuel(lo, hi, g)` steps (the general-iteration
/// middle loop `copy_u(lo) → copy_u(hi)`), with the tail entering and returning at `H_0 = g+M+1`. Mirror
/// of [`crate::tm_copy_refresh::lemma_copy_loop_general`]: induct on `hi`, chaining
/// [`lemma_copy_iter_tail_safe`] at each step `j = hi − 1` (every iter net-disp-0 at `H_0`).
pub proof fn lemma_copy_loop_general_tail_safe(
    tm: Tm, lo: nat, hi: nat, big_m: nat, g: nat, out: nat,
    q_home: nat, q_t: nat, q_a: nat, q_b: nat, q_rf: nat, q_rg: nat, q_rt: nat, q_dw: nat,
    i_peel: int, i_temp: int, i_t2g: int, i_gap: int, i_a2b: int, i_fives: int, i_mark: int,
    i_rfives: int, i_rf2g: int, i_rgap: int, i_rg2t: int, i_rtemp: int,
    i_dpeel: int, i_dtemp: int, i_dins: int, i_dwb: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        2 <= lo <= hi <= big_m,
        hi <= g - 1,
        0 <= i_peel < tm.quints.len(),
        0 <= i_temp < tm.quints.len(),
        0 <= i_t2g < tm.quints.len(),
        0 <= i_gap < tm.quints.len(),
        0 <= i_a2b < tm.quints.len(),
        0 <= i_fives < tm.quints.len(),
        0 <= i_mark < tm.quints.len(),
        0 <= i_rfives < tm.quints.len(),
        0 <= i_rf2g < tm.quints.len(),
        0 <= i_rgap < tm.quints.len(),
        0 <= i_rg2t < tm.quints.len(),
        0 <= i_rtemp < tm.quints.len(),
        0 <= i_dpeel < tm.quints.len(),
        0 <= i_dtemp < tm.quints.len(),
        0 <= i_dins < tm.quints.len(),
        0 <= i_dwb < tm.quints.len(),
        tm.quints[i_peel] == mk_quint(q_home, 0, 0, q_t, Dir::L),
        tm.quints[i_temp] == mk_quint(q_t, 1, 1, q_t, Dir::L),
        tm.quints[i_t2g] == mk_quint(q_t, 0, 0, q_a, Dir::L),
        tm.quints[i_gap] == mk_quint(q_a, 0, 0, q_a, Dir::L),
        tm.quints[i_a2b] == mk_quint(q_a, 5, 5, q_b, Dir::L),
        tm.quints[i_fives] == mk_quint(q_b, 5, 5, q_b, Dir::L),
        tm.quints[i_mark] == mk_quint(q_b, 1, 5, q_rf, Dir::R),
        tm.quints[i_rfives] == mk_quint(q_rf, 5, 5, q_rf, Dir::R),
        tm.quints[i_rf2g] == mk_quint(q_rf, 0, 0, q_rg, Dir::R),
        tm.quints[i_rgap] == mk_quint(q_rg, 0, 0, q_rg, Dir::R),
        tm.quints[i_rg2t] == mk_quint(q_rg, 1, 1, q_rt, Dir::R),
        tm.quints[i_rtemp] == mk_quint(q_rt, 1, 1, q_rt, Dir::R),
        tm.quints[i_dpeel] == mk_quint(q_rt, 0, 0, q_dw, Dir::L),
        tm.quints[i_dtemp] == mk_quint(q_dw, 1, 1, q_dw, Dir::L),
        tm.quints[i_dins] == mk_quint(q_dw, 0, 1, q_home, Dir::R),
        tm.quints[i_dwb] == mk_quint(q_home, 1, 1, q_home, Dir::R),
    ensures
        tail_safe(tm, TmConfig { u: copy_u(lo, big_m, g, tm.m), v: out, a: 0, q: q_home },
            copy_loop_fuel(lo, hi, g), (g + big_m + 1) as nat),
        tail_end_h(tm, TmConfig { u: copy_u(lo, big_m, g, tm.m), v: out, a: 0, q: q_home },
            copy_loop_fuel(lo, hi, g), (g + big_m + 1) as nat) == (g + big_m + 1) as nat,
    decreases hi,
{
    reveal(tm_wf);
    let m = tm.m;
    let h0 = (g + big_m + 1) as nat;
    let c_lo = TmConfig { u: copy_u(lo, big_m, g, m), v: out, a: 0, q: q_home };
    if hi == lo {
        assert(copy_loop_fuel(lo, hi, g) == 0);
        assert(tm_run(tm, c_lo, 0) == c_lo);
        // tail_safe(c_lo, 0, h0) == true; tail_end_h(c_lo, 0, h0) == h0.
    } else {
        // ── IH: copy_u(lo) → copy_u(hi-1), fuel copy_loop_fuel(lo, hi-1, g). offset H_0 → H_0. ──
        lemma_copy_loop_general(tm, lo, (hi - 1) as nat, big_m, g, out,
            q_home, q_t, q_a, q_b, q_rf, q_rg, q_rt, q_dw,
            i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives, i_mark, i_rfives, i_rf2g, i_rgap, i_rg2t,
            i_rtemp, i_dpeel, i_dtemp, i_dins, i_dwb);
        lemma_copy_loop_general_tail_safe(tm, lo, (hi - 1) as nat, big_m, g, out,
            q_home, q_t, q_a, q_b, q_rf, q_rg, q_rt, q_dw,
            i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives, i_mark, i_rfives, i_rf2g, i_rgap, i_rg2t,
            i_rtemp, i_dpeel, i_dtemp, i_dins, i_dwb);
        let c_mid = TmConfig { u: copy_u((hi - 1) as nat, big_m, g, m), v: out, a: 0, q: q_home };
        assert(tm_run(tm, c_lo, copy_loop_fuel(lo, (hi - 1) as nat, g)) == c_mid);

        // ── copy_iter(hi-1): copy_u(hi-1) → copy_u(hi). offset H_0 → H_0. ──
        lemma_copy_iter_tail_safe(tm, (hi - 1) as nat, big_m, g, out,
            q_home, q_t, q_a, q_b, q_rf, q_rg, q_rt, q_dw, q_home,
            i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives, i_mark, i_rfives, i_rf2g, i_rgap, i_rg2t,
            i_rtemp, i_dpeel, i_dtemp, i_dins, i_dwb);
        let step = (2 * (g + (hi - 1) + 1) + (2 * (hi - 1) + 2)) as nat;
        assert(((hi - 1) + 1) as nat == hi);
        // copy_iter_tail_safe gives tail_safe(c_mid, step, h0), end h0.

        // ── chain. ──
        lemma_tail_chain(tm, c_lo, copy_loop_fuel(lo, (hi - 1) as nat, g), step, h0, h0, h0);
        assert(copy_loop_fuel(lo, hi, g) == copy_loop_fuel(lo, (hi - 1) as nat, g) + step);
    }
}

/// **`mark_j1` is tail-safe** for its `2·(g+2)` steps, returning to `H_0` (net-disp-0). Forward via
/// [`lemma_mark_fwd_tail_safe`] (`j = 1`, `H_0 → M−1`); the MARK turn + return (S6–S9, lands on the pivot
/// directly, no S10) are ALL R-moves. Mirror of [`crate::tm_copy_refresh::lemma_mark_j1`].
pub proof fn lemma_mark_j1_tail_safe(
    tm: Tm, big_m: nat, g: nat, out: nat,
    q_mh: nat, q_t: nat, q_a: nat, q_b: nat, q_rf: nat, q_rg: nat, q_rt: nat,
    i_peel: int, i_temp: int, i_t2g: int, i_gap: int, i_a2b: int, i_fives: int, i_mark: int,
    i_rfives: int, i_rf2g: int, i_rgap: int, i_rg2t: int, i_rtemp: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        1 < big_m,
        g >= 3,
        0 <= i_peel < tm.quints.len(),
        0 <= i_temp < tm.quints.len(),
        0 <= i_t2g < tm.quints.len(),
        0 <= i_gap < tm.quints.len(),
        0 <= i_a2b < tm.quints.len(),
        0 <= i_fives < tm.quints.len(),
        0 <= i_mark < tm.quints.len(),
        0 <= i_rfives < tm.quints.len(),
        0 <= i_rf2g < tm.quints.len(),
        0 <= i_rgap < tm.quints.len(),
        0 <= i_rg2t < tm.quints.len(),
        0 <= i_rtemp < tm.quints.len(),
        tm.quints[i_peel] == mk_quint(q_mh, 0, 0, q_t, Dir::L),
        tm.quints[i_temp] == mk_quint(q_t, 1, 1, q_t, Dir::L),
        tm.quints[i_t2g] == mk_quint(q_t, 0, 0, q_a, Dir::L),
        tm.quints[i_gap] == mk_quint(q_a, 0, 0, q_a, Dir::L),
        tm.quints[i_a2b] == mk_quint(q_a, 5, 5, q_b, Dir::L),
        tm.quints[i_fives] == mk_quint(q_b, 5, 5, q_b, Dir::L),
        tm.quints[i_mark] == mk_quint(q_b, 1, 5, q_rf, Dir::R),
        tm.quints[i_rfives] == mk_quint(q_rf, 5, 5, q_rf, Dir::R),
        tm.quints[i_rf2g] == mk_quint(q_rf, 0, 0, q_rg, Dir::R),
        tm.quints[i_rgap] == mk_quint(q_rg, 0, 0, q_rg, Dir::R),
        tm.quints[i_rg2t] == mk_quint(q_rg, 1, 1, q_rt, Dir::R),
        tm.quints[i_rtemp] == mk_quint(q_rt, 1, 1, q_rt, Dir::R),
    ensures
        tail_safe(tm, TmConfig { u: copy_u(1, big_m, g, tm.m), v: out, a: 0, q: q_mh },
            (2 * (g + 2)) as nat, (g + big_m + 1) as nat),
        tail_end_h(tm, TmConfig { u: copy_u(1, big_m, g, tm.m), v: out, a: 0, q: q_mh },
            (2 * (g + 2)) as nat, (g + big_m + 1) as nat) == (g + big_m + 1) as nat,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let h0 = (g + big_m + 1) as nat;
    let pile_temp = pile_sym(out * m, 1, 1, m);
    let big_v = pile_temp * pow_nat(m, (g - 1) as nat);
    let mm1 = repunit_m((big_m - 2) as nat, m);
    let ms_next = master_at(2, big_m, m);
    let c0 = TmConfig { u: copy_u(1, big_m, g, m), v: out, a: 0, q: q_mh };

    // ── FORWARD: c0 → c5, g+2 steps. offset H_0 → M-1. ──
    lemma_mark_fwd(tm, 1, big_m, g, out, q_mh, q_t, q_a, q_b,
        i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives);
    lemma_mark_fwd_tail_safe(tm, 1, big_m, g, out, q_mh, q_t, q_a, q_b,
        i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives);
    assert((big_m - 1 - 1) as nat == (big_m - 2) as nat);
    let c5 = TmConfig { u: mm1, v: pile_sym(big_v, 5, 1, m), a: 1, q: q_b };
    assert(tm_run(tm, c0, (g + 1 + 1) as nat) == c5);
    assert((g + 1 + 1) as nat == (g + 2) as nat);
    assert((big_m - 1) as nat == (big_m - 1) as nat);

    // ── MARK step (q_b, 1, 5, q_rf, R). offset M-1 → M. ──
    lemma_pile_sym_div_mod(big_v, 5, 1, m);
    lemma_tm_step_picks(tm, c5, i_mark);
    let c6 = apply_quint(tm.quints[i_mark], c5, m);
    assert(tm_step(tm, c5) == Some(c6));
    assert(c6.u == mm1 * m + 5 && c6.v == big_v && c6.a == 5 && c6.q == q_rf);
    assert(tm_run(tm, c6, 0) == c6);
    assert(tm_run(tm, c5, 1) == c6);
    lemma_tm_run_split(tm, c0, (g + 2) as nat, 1);
    assert(tm_run(tm, c0, (g + 3) as nat) == c6);
    assert(quint_matches(tm.quints[i_mark], c5));
    lemma_step_tail_safe(tm, c5, i_mark, (big_m - 1) as nat);   // R, end M
    assert(((big_m - 1) + 1) as nat == big_m);
    lemma_tail_chain(tm, c0, (g + 2) as nat, 1, h0, (big_m - 1) as nat, big_m);

    // ── S6: run_walk_right over the single five (1 step), q_rf. offset M → M+1. ──
    assert(pow_nat(m, 1) == m) by { lemma_pow_nat_unfold(m, 1); assert(pow_nat(m, 0) == 1); }
    assert(repunit_m(1, m) == 1) by { lemma_repunit_step(0, m); lemma_repunit_zero(m); }
    assert(c6.u == 5 * repunit_m(1, m) + pow_nat(m, 1) * mm1) by(nonlinear_arith)
        requires c6.u == mm1 * m + 5, repunit_m(1, m) == 1, pow_nat(m, 1) == m;
    lemma_run_walk_right(tm, c6, q_rf, 5, 1, 0, big_v, mm1, i_rfives);
    assert((1 + 0 + 1) as nat == 2);
    assert(ms_next == 5 * repunit_m(2, m) + pow_nat(m, 2) * mm1);
    lemma_pow_nat_unfold(m, (g - 1) as nat);
    assert(big_v == (pile_temp * pow_nat(m, (g - 2) as nat)) * m) by(nonlinear_arith)
        requires big_v == pile_temp * pow_nat(m, (g - 1) as nat),
            pow_nat(m, (g - 1) as nat) == m * pow_nat(m, (g - 2) as nat);
    lemma_div_mod_step(pile_temp * pow_nat(m, (g - 2) as nat), m, 0);
    let c7 = TmConfig { u: ms_next, v: pile_temp * pow_nat(m, (g - 2) as nat), a: 0, q: q_rf };
    assert(tm_run(tm, c6, 1) == c7);
    lemma_tm_run_split(tm, c0, (g + 3) as nat, 1);
    assert(tm_run(tm, c0, (g + 4) as nat) == c7);
    lemma_run_walk_right_tail_safe(tm, c6, q_rf, 5, 1, 0, big_v, mm1, i_rfives, big_m);
    assert((big_m + 0 + 1) as nat == (big_m + 1) as nat);
    lemma_tail_chain(tm, c0, (g + 3) as nat, 1, h0, big_m, (big_m + 1) as nat);

    // ── S7: rf→gap transition (q_rf, 0, 0, q_rg, R). offset M+1 → M+2. ──
    lemma_pow_nat_unfold(m, (g - 2) as nat);
    assert(c7.v == (pile_temp * pow_nat(m, (g - 3) as nat)) * m) by(nonlinear_arith)
        requires c7.v == pile_temp * pow_nat(m, (g - 2) as nat),
            pow_nat(m, (g - 2) as nat) == m * pow_nat(m, (g - 3) as nat);
    lemma_div_mod_step(pile_temp * pow_nat(m, (g - 3) as nat), m, 0);
    lemma_tm_step_picks(tm, c7, i_rf2g);
    let c8 = apply_quint(tm.quints[i_rf2g], c7, m);
    assert(tm_step(tm, c7) == Some(c8));
    assert(c8.u == ms_next * m && c8.v == pile_temp * pow_nat(m, (g - 3) as nat) && c8.a == 0
        && c8.q == q_rg);
    assert(tm_run(tm, c8, 0) == c8);
    assert(tm_run(tm, c7, 1) == c8);
    lemma_tm_run_split(tm, c0, (g + 4) as nat, 1);
    assert(tm_run(tm, c0, (g + 5) as nat) == c8);
    assert(quint_matches(tm.quints[i_rf2g], c7));
    lemma_step_tail_safe(tm, c7, i_rf2g, (big_m + 1) as nat);   // R, end M+2
    assert(((big_m + 1) + 1) as nat == (big_m + 2) as nat);
    lemma_tail_chain(tm, c0, (g + 4) as nat, 1, h0, (big_m + 1) as nat, (big_m + 2) as nat);

    // ── S8: seek_right_blanks over the gap (g-2 steps), q_rg. offset M+2 → g+M. ──
    lemma_pile_sym_div_mod(out * m, 1, 1, m);
    assert(c8.v == pow_nat(m, (g - 3) as nat) * pile_temp) by(nonlinear_arith)
        requires c8.v == pile_temp * pow_nat(m, (g - 3) as nat);
    lemma_seek_right_blanks(tm, c8, q_rg, (g - 3) as nat, pile_temp, i_rgap);
    assert(pile_sym(out * m, 1, 0, m) == out * m);
    let c9 = TmConfig { u: c8.u * pow_nat(m, (g - 2) as nat), v: out * m, a: 1, q: q_rg };
    assert(((g - 3) + 1) as nat == (g - 2) as nat);
    assert(tm_run(tm, c8, (g - 2) as nat) == c9);
    lemma_tm_run_split(tm, c0, (g + 5) as nat, (g - 2) as nat);
    assert((g + 5 + (g - 2)) as nat == (2 * g + 3) as nat);
    assert(tm_run(tm, c0, (2 * g + 3) as nat) == c9);
    assert(c9.u == ms_next * pow_nat(m, (g - 1) as nat)) by(nonlinear_arith)
        requires c9.u == (ms_next * m) * pow_nat(m, (g - 2) as nat),
            pow_nat(m, (g - 1) as nat) == m * pow_nat(m, (g - 2) as nat);
    lemma_seek_right_tail_safe(tm, c8, q_rg, (g - 3) as nat, pile_temp, i_rgap, (big_m + 2) as nat);
    assert(((big_m + 2) + (g - 3) + 1) as nat == (g + big_m) as nat);
    lemma_tail_chain(tm, c0, (g + 5) as nat, (g - 2) as nat, h0, (big_m + 2) as nat, (g + big_m) as nat);

    // ── S9: rg→temp transition (q_rg, 1, 1, q_rt, R) lands on the pivot. offset g+M → H_0. ──
    lemma_div_mod_step(out, m, 0);
    lemma_tm_step_picks(tm, c9, i_rg2t);
    let c10 = apply_quint(tm.quints[i_rg2t], c9, m);
    assert(tm_step(tm, c9) == Some(c10));
    assert(c10.u == c9.u * m + 1 && c10.v == out && c10.a == 0 && c10.q == q_rt);
    assert(tm_run(tm, c10, 0) == c10);
    assert(tm_run(tm, c9, 1) == c10);
    lemma_tm_run_split(tm, c0, (2 * g + 3) as nat, 1);
    assert((2 * g + 3 + 1) as nat == (2 * (g + 2)) as nat);
    assert(tm_run(tm, c0, (2 * (g + 2)) as nat) == c10);
    assert(quint_matches(tm.quints[i_rg2t], c9));
    lemma_step_tail_safe(tm, c9, i_rg2t, (g + big_m) as nat);   // R, end g+M+1 == H_0
    assert(((g + big_m) + 1) as nat == h0);
    lemma_tail_chain(tm, c0, (2 * g + 3) as nat, 1, h0, (g + big_m) as nat, h0);
}

/// **`mark_j0` is tail-safe** for its `2·g + 2` steps (the deposit-first `j = 0` MARK, temp = 1, fives = 0)
/// when the tail enters at `H_0 = g+M+1`, returning to `H_0` (net-disp-0). Forward (S1–S4, `g+1` L-moves)
/// drives the offset `H_0 → M` (lands on the master's lowest one, `M ≥ 1` — not tight); the MARK turn +
/// return (S7–S9, lands on the pivot) are ALL R-moves. Mirror of
/// [`crate::tm_copy_refresh::lemma_mark_j0`].
pub proof fn lemma_mark_j0_tail_safe(
    tm: Tm, big_m: nat, g: nat, out: nat,
    q_mh0: nat, q_t0: nat, q_a0: nat, q_rf0: nat, q_rg0: nat, q_rt0: nat,
    i_peel: int, i_temp: int, i_t2g: int, i_gap: int, i_mark: int, i_rf2g: int, i_rgap: int, i_rg2t: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        1 <= big_m,
        g >= 3,
        0 <= i_peel < tm.quints.len(),
        0 <= i_temp < tm.quints.len(),
        0 <= i_t2g < tm.quints.len(),
        0 <= i_gap < tm.quints.len(),
        0 <= i_mark < tm.quints.len(),
        0 <= i_rf2g < tm.quints.len(),
        0 <= i_rgap < tm.quints.len(),
        0 <= i_rg2t < tm.quints.len(),
        tm.quints[i_peel] == mk_quint(q_mh0, 0, 0, q_t0, Dir::L),
        tm.quints[i_temp] == mk_quint(q_t0, 1, 1, q_t0, Dir::L),
        tm.quints[i_t2g] == mk_quint(q_t0, 0, 0, q_a0, Dir::L),
        tm.quints[i_gap] == mk_quint(q_a0, 0, 0, q_a0, Dir::L),
        tm.quints[i_mark] == mk_quint(q_a0, 1, 5, q_rf0, Dir::R),
        tm.quints[i_rf2g] == mk_quint(q_rf0, 0, 0, q_rg0, Dir::R),
        tm.quints[i_rgap] == mk_quint(q_rg0, 0, 0, q_rg0, Dir::R),
        tm.quints[i_rg2t] == mk_quint(q_rg0, 1, 1, q_rt0, Dir::R),
    ensures
        tail_safe(tm, TmConfig { u: (1 + pow_nat(tm.m, g) * repunit_m(big_m, tm.m)) as nat, v: out,
            a: 0, q: q_mh0 }, (2 * g + 2) as nat, (g + big_m + 1) as nat),
        tail_end_h(tm, TmConfig { u: (1 + pow_nat(tm.m, g) * repunit_m(big_m, tm.m)) as nat, v: out,
            a: 0, q: q_mh0 }, (2 * g + 2) as nat, (g + big_m + 1) as nat) == (g + big_m + 1) as nat,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let h0 = (g + big_m + 1) as nat;
    assert(repunit_m(1, m) == 1) by { lemma_repunit_step(0, m); lemma_repunit_zero(m); }
    lemma_pow_nat_unfold(m, 1);
    assert(pow_nat(m, 0) == 1);
    assert(pow_nat(m, 1) == m) by(nonlinear_arith)
        requires pow_nat(m, 1) == m * pow_nat(m, 0), pow_nat(m, 0) == 1;
    let rm = repunit_m(big_m, m);
    let dep0 = (1 + pow_nat(m, g) * rm) as nat;
    let pile_temp = pile_sym(out * m, 1, 1, m);
    let ms_next = master_at(1, big_m, m);
    assert(ms_next == 5 + m * repunit_m((big_m - 1) as nat, m)) by(nonlinear_arith)
        requires
            ms_next == 5 * repunit_m(1, m) + pow_nat(m, 1) * repunit_m((big_m - 1) as nat, m),
            repunit_m(1, m) == 1,
            pow_nat(m, 1) == m;
    let c0 = TmConfig { u: dep0, v: out, a: 0, q: q_mh0 };

    // ── S1: pivot-peel (L). offset H_0 → g+M. ──
    lemma_pow_nat_unfold(m, g);
    let u1 = pow_nat(m, (g - 1) as nat) * rm;
    assert(dep0 == u1 * m + 1) by(nonlinear_arith)
        requires dep0 == 1 + pow_nat(m, g) * rm, pow_nat(m, g) == m * pow_nat(m, (g - 1) as nat),
            u1 == pow_nat(m, (g - 1) as nat) * rm;
    lemma_div_mod_step(u1, m, 1);
    lemma_tm_step_picks(tm, c0, i_peel);
    let c1 = apply_quint(tm.quints[i_peel], c0, m);
    assert(tm_step(tm, c0) == Some(c1));
    assert(c1.u == u1 && c1.v == out * m && c1.a == 1 && c1.q == q_t0);
    assert(tm_run(tm, c1, 0) == c1);
    assert(tm_run(tm, c0, 1) == c1);
    assert(quint_matches(tm.quints[i_peel], c0));
    lemma_step_tail_safe(tm, c0, i_peel, h0);   // L, end g+M

    // ── S2: walk-left over the single temp one (1 step), q_t0. offset g+M → g+M-1. ──
    lemma_repunit_zero(m);
    assert(c1.u == 1 * repunit_m(0, m) + pow_nat(m, 0) * u1) by(nonlinear_arith)
        requires c1.u == u1, repunit_m(0, m) == 0, pow_nat(m, 0) == 1;
    lemma_run_walk_left(tm, c1, q_t0, 1, 0, u1, i_temp);
    lemma_pow_nat_unfold(m, (g - 1) as nat);
    assert(u1 == (pow_nat(m, (g - 2) as nat) * rm) * m) by(nonlinear_arith)
        requires u1 == pow_nat(m, (g - 1) as nat) * rm,
            pow_nat(m, (g - 1) as nat) == m * pow_nat(m, (g - 2) as nat);
    lemma_div_mod_step(pow_nat(m, (g - 2) as nat) * rm, m, 0);
    let c2 = TmConfig { u: pow_nat(m, (g - 2) as nat) * rm, v: pile_temp, a: 0, q: q_t0 };
    assert(pile_sym(out * m, 1, 1, m) == pile_temp);
    assert(tm_run(tm, c1, 1) == c2);
    lemma_tm_run_split(tm, c0, 1, 1);
    assert(tm_run(tm, c0, 2) == c2);
    lemma_run_walk_left_tail_safe(tm, c1, q_t0, 1, 0, u1, i_temp, (g + big_m) as nat);
    assert(((g + big_m) - 1) as nat == (g + big_m - 1) as nat);
    lemma_tail_chain(tm, c0, 1, 1, h0, (g + big_m) as nat, (g + big_m - 1) as nat);

    // ── S3: temp→gap transition (L). offset g+M-1 → g+M-2. ──
    lemma_pow_nat_unfold(m, (g - 2) as nat);
    assert(c2.u == (pow_nat(m, (g - 3) as nat) * rm) * m) by(nonlinear_arith)
        requires c2.u == pow_nat(m, (g - 2) as nat) * rm,
            pow_nat(m, (g - 2) as nat) == m * pow_nat(m, (g - 3) as nat);
    lemma_div_mod_step(pow_nat(m, (g - 3) as nat) * rm, m, 0);
    lemma_tm_step_picks(tm, c2, i_t2g);
    let c3 = apply_quint(tm.quints[i_t2g], c2, m);
    assert(tm_step(tm, c2) == Some(c3));
    assert(c3.u == pow_nat(m, (g - 3) as nat) * rm && c3.v == pile_temp * m && c3.a == 0
        && c3.q == q_a0);
    assert(tm_run(tm, c3, 0) == c3);
    assert(tm_run(tm, c2, 1) == c3);
    lemma_tm_run_split(tm, c0, 2, 1);
    assert(tm_run(tm, c0, 3) == c3);
    assert(quint_matches(tm.quints[i_t2g], c2));
    lemma_step_tail_safe(tm, c2, i_t2g, (g + big_m - 1) as nat);   // L, end g+M-2
    assert(((g + big_m - 1) - 1) as nat == (g + big_m - 2) as nat);
    lemma_tail_chain(tm, c0, 2, 1, h0, (g + big_m - 1) as nat, (g + big_m - 2) as nat);

    // ── S4: seek-left over the remaining gap (g-2 steps), q_a0. offset g+M-2 → M. ──
    lemma_repunit_step((big_m - 1) as nat, m);
    assert(((big_m - 1) + 1) as nat == big_m);
    assert(rm % m != 0) by {
        assert(rm == m * repunit_m((big_m - 1) as nat, m) + 1);
        lemma_div_mod_step(repunit_m((big_m - 1) as nat, m), m, 1);
    }
    lemma_seek_left_blanks(tm, c3, q_a0, (g - 3) as nat, rm, i_gap);
    assert(rm == repunit_m((big_m - 1) as nat, m) * m + 1) by(nonlinear_arith)
        requires rm == m * repunit_m((big_m - 1) as nat, m) + 1;
    lemma_div_mod_step(repunit_m((big_m - 1) as nat, m), m, 1);
    let c5 = TmConfig {
        u: repunit_m((big_m - 1) as nat, m),
        v: (pile_temp * m) * pow_nat(m, (g - 2) as nat), a: 1, q: q_a0 };
    assert(((g - 3) + 1) as nat == (g - 2) as nat);
    assert(tm_run(tm, c3, (g - 2) as nat) == c5);
    lemma_tm_run_split(tm, c0, 3, (g - 2) as nat);
    assert((3 + (g - 2)) as nat == (g + 1) as nat);
    assert(tm_run(tm, c0, (g + 1) as nat) == c5);
    lemma_pow_nat_unfold(m, (g - 1) as nat);
    let big_v = pile_temp * pow_nat(m, (g - 1) as nat);
    assert((pile_temp * m) * pow_nat(m, (g - 2) as nat) == big_v) by(nonlinear_arith)
        requires big_v == pile_temp * pow_nat(m, (g - 1) as nat),
            pow_nat(m, (g - 1) as nat) == m * pow_nat(m, (g - 2) as nat);
    assert(c5.v == big_v);
    lemma_seek_left_tail_safe(tm, c3, q_a0, (g - 3) as nat, rm, i_gap, (g + big_m - 2) as nat);
    assert(((g + big_m - 2) - (g - 2)) as nat == big_m);
    lemma_tail_chain(tm, c0, 3, (g - 2) as nat, h0, (g + big_m - 2) as nat, big_m);

    // ── MARK step (q_a0, 1, 5, q_rf0, R). offset M → M+1. ──
    assert(big_v == (pile_temp * pow_nat(m, (g - 2) as nat)) * m) by(nonlinear_arith)
        requires big_v == pile_temp * pow_nat(m, (g - 1) as nat),
            pow_nat(m, (g - 1) as nat) == m * pow_nat(m, (g - 2) as nat);
    lemma_div_mod_step(pile_temp * pow_nat(m, (g - 2) as nat), m, 0);
    lemma_tm_step_picks(tm, c5, i_mark);
    let c6 = apply_quint(tm.quints[i_mark], c5, m);
    assert(tm_step(tm, c5) == Some(c6));
    assert(c6.u == repunit_m((big_m - 1) as nat, m) * m + 5
        && c6.v == pile_temp * pow_nat(m, (g - 2) as nat) && c6.a == 0 && c6.q == q_rf0);
    assert(c6.u == ms_next) by(nonlinear_arith)
        requires c6.u == repunit_m((big_m - 1) as nat, m) * m + 5,
            ms_next == 5 + m * repunit_m((big_m - 1) as nat, m);
    assert(tm_run(tm, c6, 0) == c6);
    assert(tm_run(tm, c5, 1) == c6);
    lemma_tm_run_split(tm, c0, (g + 1) as nat, 1);
    assert(tm_run(tm, c0, (g + 2) as nat) == c6);
    assert(quint_matches(tm.quints[i_mark], c5));
    lemma_step_tail_safe(tm, c5, i_mark, big_m);   // R, end M+1
    assert((big_m + 1) as nat == (big_m + 1) as nat);
    lemma_tail_chain(tm, c0, (g + 1) as nat, 1, h0, big_m, (big_m + 1) as nat);

    // ── S7: rf→gap transition (q_rf0, 0, 0, q_rg0, R). offset M+1 → M+2. ──
    lemma_pow_nat_unfold(m, (g - 2) as nat);
    assert(c6.v == (pile_temp * pow_nat(m, (g - 3) as nat)) * m) by(nonlinear_arith)
        requires c6.v == pile_temp * pow_nat(m, (g - 2) as nat),
            pow_nat(m, (g - 2) as nat) == m * pow_nat(m, (g - 3) as nat);
    lemma_div_mod_step(pile_temp * pow_nat(m, (g - 3) as nat), m, 0);
    lemma_tm_step_picks(tm, c6, i_rf2g);
    let c7 = apply_quint(tm.quints[i_rf2g], c6, m);
    assert(tm_step(tm, c6) == Some(c7));
    assert(c7.u == ms_next * m && c7.v == pile_temp * pow_nat(m, (g - 3) as nat) && c7.a == 0
        && c7.q == q_rg0);
    assert(tm_run(tm, c7, 0) == c7);
    assert(tm_run(tm, c6, 1) == c7);
    lemma_tm_run_split(tm, c0, (g + 2) as nat, 1);
    assert(tm_run(tm, c0, (g + 3) as nat) == c7);
    assert(quint_matches(tm.quints[i_rf2g], c6));
    lemma_step_tail_safe(tm, c6, i_rf2g, (big_m + 1) as nat);   // R, end M+2
    assert(((big_m + 1) + 1) as nat == (big_m + 2) as nat);
    lemma_tail_chain(tm, c0, (g + 2) as nat, 1, h0, (big_m + 1) as nat, (big_m + 2) as nat);

    // ── S8: seek_right_blanks over the gap (g-2 steps), q_rg0. offset M+2 → g+M. ──
    lemma_pile_sym_div_mod(out * m, 1, 1, m);
    assert(c7.v == pow_nat(m, (g - 3) as nat) * pile_temp) by(nonlinear_arith)
        requires c7.v == pile_temp * pow_nat(m, (g - 3) as nat);
    lemma_seek_right_blanks(tm, c7, q_rg0, (g - 3) as nat, pile_temp, i_rgap);
    assert(pile_sym(out * m, 1, 0, m) == out * m);
    let c9 = TmConfig { u: c7.u * pow_nat(m, (g - 2) as nat), v: out * m, a: 1, q: q_rg0 };
    assert(((g - 3) + 1) as nat == (g - 2) as nat);
    assert(tm_run(tm, c7, (g - 2) as nat) == c9);
    lemma_tm_run_split(tm, c0, (g + 3) as nat, (g - 2) as nat);
    assert((g + 3 + (g - 2)) as nat == (2 * g + 1) as nat);
    assert(tm_run(tm, c0, (2 * g + 1) as nat) == c9);
    lemma_seek_right_tail_safe(tm, c7, q_rg0, (g - 3) as nat, pile_temp, i_rgap, (big_m + 2) as nat);
    assert(((big_m + 2) + (g - 3) + 1) as nat == (g + big_m) as nat);
    lemma_tail_chain(tm, c0, (g + 3) as nat, (g - 2) as nat, h0, (big_m + 2) as nat, (g + big_m) as nat);

    // ── S9: rg→temp transition (q_rg0, 1, 1, q_rt0, R) lands on the pivot. offset g+M → H_0. ──
    lemma_tm_step_picks(tm, c9, i_rg2t);
    let c10 = apply_quint(tm.quints[i_rg2t], c9, m);
    assert(tm_step(tm, c9) == Some(c10));
    assert(c10.q == q_rt0);
    assert(tm_run(tm, c10, 0) == c10);
    assert(tm_run(tm, c9, 1) == c10);
    lemma_tm_run_split(tm, c0, (2 * g + 1) as nat, 1);
    assert((2 * g + 1 + 1) as nat == (2 * g + 2) as nat);
    assert(tm_run(tm, c0, (2 * g + 2) as nat) == c10);
    assert(quint_matches(tm.quints[i_rg2t], c9));
    lemma_step_tail_safe(tm, c9, i_rg2t, (g + big_m) as nat);   // R, end H_0
    assert(((g + big_m) + 1) as nat == h0);
    lemma_tail_chain(tm, c0, (2 * g + 1) as nat, 1, h0, (g + big_m) as nat, h0);
}

} // verus!
