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
use crate::tm_two_counter::{repunit_m, lemma_repunit_zero};
use crate::tm_dstring::pow_nat;
use crate::tm_dec_master::{dec_u, lemma_walk_left_prefix, lemma_walk_back_prefix};
use crate::tm_block_loop::lemma_dec_u_step;
use crate::tm_walk::{pile_ones, lemma_pile_ones_div_mod};
use crate::tm_emit::pile_sym;
use crate::tm_run_lemmas::lemma_tm_run_split;
use crate::gap2_tail_lift::{tail_safe, tail_end_h, lemma_step_tail_safe, lemma_tail_chain};
use crate::gap2_tail_walks::{lemma_run_walk_left_tail_safe, lemma_run_walk_right_tail_safe};

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

} // verus!
