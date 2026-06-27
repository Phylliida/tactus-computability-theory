//! # GAP-2 G2-F — RIGHT-tail (α-block) safety of copy_refresh's PHASE 1 (`v`-side mirror)
//!
//! The `v`-side analog of [`crate::gap2_tail_phase1`]. The phase-1 gadgets (`deposit`/`mark`/`copy_iter`/
//! `copy_loop`) operate ENTIRELY left of the home pivot (mark/copy the master + build temp in `u`), never
//! touching the output/α-block in `v`. So on the `v`-side they are all **UNCONDITIONAL**, net-displacement-0:
//! every leftward excursion PUSHES onto `v` (the α-tail offset RISES, away from the α-block) and the return
//! POPS it back to the entry `h`. Parametric in the α-offset `h` (vs the `u`-side's fixed `H_0 = g+M+1`).
//!
//! Each leaf gadget (deposit/mark_fwd/mark/mark_j1/mark_j0) recomputes its offsets via the rising-during-L
//! relation `v_offset = h + (g+M+1) − u_offset`; each composite (copy_iter/copy_loop_general/copy_iter_j*/
//! copy_prefix/copy_loop/copy_refresh) is a constant-`h` chain. The source-gadget calls + value arithmetic
//! are copied verbatim. Fully verified, no verifier escape hatches.

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
    copy_loop_fuel, lemma_copy_loop_general, lemma_mark_j1, lemma_mark_j0, lemma_deposit,
    lemma_copy_u_start, lemma_copy_iter_j0, lemma_copy_prefix, full_copy_fuel,
    lemma_copy_loop, lemma_mark_terminate, lemma_unmark, copy_refresh_fuel};
use crate::gap2_tail_phase1::lemma_pile_ones_eq_pile_sym;
use crate::gap2_tail_phases_v::{lemma_mark_terminate_tail_safe_v, lemma_unmark_tail_safe_v};
use crate::gap2_tail_lift_v::{tail_safe_v, tail_end_h_v, lemma_step_tail_safe_v, lemma_tail_v_chain};
use crate::gap2_tail_walks_v::{lemma_run_walk_left_tail_safe_v, lemma_run_walk_right_tail_safe_v,
    lemma_seek_left_tail_safe_v, lemma_seek_right_tail_safe_v};

verus! {

/// **`deposit` is `v`-tail-safe** for its `2j + 2` steps — UNCONDITIONAL, net-disp-0. The leftward
/// peel/walk RAISE the offset (`h → h+1+j`), the insert/walk-back POP back to `h`. `v`-side mirror of
/// [`crate::gap2_tail_phase1::lemma_deposit_tail_safe`].
pub proof fn lemma_deposit_tail_safe_v(
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
    ensures
        tail_safe_v(tm, TmConfig { u: dec_u(j, w, tm.m), v: out, a: 0, q: q_dh }, (2 * j + 2) as nat, h),
        tail_end_h_v(tm, TmConfig { u: dec_u(j, w, tm.m), v: out, a: 0, q: q_dh }, (2 * j + 2) as nat, h)
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

    // ── S1: peel the pivot (L). offset h → h+1. ──
    lemma_tm_step_picks(tm, c0, i_pivot);
    let c_peel = apply_quint(tm.quints[i_pivot], c0, m);
    assert(tm_step(tm, c0) == Some(c_peel));
    assert(c_peel.v == v1);
    assert(c_peel.q == q_dw);
    assert(tm_run(tm, c_peel, 0) == c_peel);
    assert(tm_run(tm, c0, 1) == c_peel);
    assert(quint_matches(tm.quints[i_pivot], c0));
    lemma_step_tail_safe_v(tm, c0, i_pivot, h);   // L, end h+1

    if j == 0 {
        assert(dec_u(0, w, m) == w) by {
            lemma_repunit_zero(m);
            assert(pow_nat(m, 0) == 1);
            assert(dec_u(0, w, m) == repunit_m(0, m) + pow_nat(m, 0) * w);
            assert(1nat * w == w) by(nonlinear_arith);
        }
        assert(c_peel.u == w / m);
        assert(c_peel.a == 0);   // w % m == 0
        // ── S2 (j==0): INSERT directly (R). offset h+1 → h. ──
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
        assert(quint_matches(tm.quints[i_ins], c_peel));
        lemma_step_tail_safe_v(tm, c_peel, i_ins, (h + 1) as nat);   // R, end h
        assert(((h + 1) - 1) as nat == h);
        lemma_tail_v_chain(tm, c0, 1, 1, h, (h + 1) as nat, h);
    } else {
        lemma_dec_u_step(j, w, m);   // dec_u(j,w)%m==1, /m==dec_u(j-1,w)
        assert(c_peel.u == dec_u((j - 1) as nat, w, m));
        assert(c_peel.a == 1);

        // ── S2: walk-left over temp's ones (j steps). offset h+1 → h+1+j. ──
        lemma_walk_left_prefix(tm, c_peel, q_dw, (j - 1) as nat, w, i_one_l);
        let c_sep = TmConfig { u: w / m, v: pile_ones(v1, j, m), a: w % m, q: q_dw };
        assert(((j - 1) + 1) as nat == j);
        assert(tm_run(tm, c_peel, j) == c_sep);
        lemma_tm_run_split(tm, c0, 1, j);
        assert(tm_run(tm, c0, (1 + j) as nat) == c_sep);
        assert(c_peel.u == 1 * repunit_m((j - 1) as nat, m) + pow_nat(m, (j - 1) as nat) * w)
            by(nonlinear_arith)
            requires c_peel.u == dec_u((j - 1) as nat, w, m),
                dec_u((j - 1) as nat, w, m)
                    == repunit_m((j - 1) as nat, m) + pow_nat(m, (j - 1) as nat) * w;
        lemma_run_walk_left_tail_safe_v(tm, c_peel, q_dw, 1, (j - 1) as nat, w, i_one_l, (h + 1) as nat);
        assert(((h + 1) + j) as nat == (h + 1 + j) as nat);
        lemma_tail_v_chain(tm, c0, 1, j, h, (h + 1) as nat, (h + 1 + j) as nat);

        // ── S3: INSERT-turnaround (R). offset h+1+j → h+j. ──
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
        assert(quint_matches(tm.quints[i_ins], c_sep));
        lemma_step_tail_safe_v(tm, c_sep, i_ins, (h + 1 + j) as nat);   // R, end h+j
        assert(((h + 1 + j) - 1) as nat == (h + j) as nat);
        lemma_tail_v_chain(tm, c0, (1 + j) as nat, 1, h, (h + 1 + j) as nat, (h + j) as nat);

        // ── S4: walk-back (j steps). offset h+j → h. ──
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
        assert(c_ins.u == 1 * repunit_m(0, m) + pow_nat(m, 0) * (w + 1)) by(nonlinear_arith)
            requires c_ins.u == w + 1, repunit_m(0, m) == 0, pow_nat(m, 0) == 1;
        lemma_pile_ones_eq_pile_sym(v1, (j - 1) as nat, m);
        assert(c_ins.v == pile_sym(v1, 1, (j - 1) as nat, m));
        lemma_run_walk_right_tail_safe_v(tm, c_ins, q_bk, 1, 0, (j - 1) as nat, v1, (w + 1) as nat,
            i_one_r, (h + j) as nat);
        assert(((h + j) - ((j - 1) + 1)) as nat == h);
        lemma_tail_v_chain(tm, c0, (1 + j + 1) as nat, j, h, (h + j) as nat, h);
    }
}

/// **`mark_fwd` is `v`-tail-safe** for its `g + j + 1` steps — UNCONDITIONAL; the all-L forward sweep RAISES
/// the offset `h → h+g+j+1`. `v`-side mirror of [`crate::gap2_tail_phase1::lemma_mark_fwd_tail_safe`],
/// parametric in `h`.
pub proof fn lemma_mark_fwd_tail_safe_v(
    tm: Tm, j: nat, big_m: nat, g: nat, out: nat,
    q_mh: nat, q_t: nat, q_a: nat, q_b: nat,
    i_peel: int, i_temp: int, i_t2g: int, i_gap: int, i_a2b: int, i_fives: int, h: nat,
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
        tail_safe_v(tm, TmConfig { u: copy_u(j, big_m, g, tm.m), v: out, a: 0, q: q_mh },
            (g + j + 1) as nat, h),
        tail_end_h_v(tm, TmConfig { u: copy_u(j, big_m, g, tm.m), v: out, a: 0, q: q_mh },
            (g + j + 1) as nat, h) == (h + g + j + 1) as nat,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let ms = master_at(j, big_m, m);
    lemma_copy_u_master(j, big_m, g, m);   // copy_u(j) == R(j) + m^g·ms
    let c0 = TmConfig { u: copy_u(j, big_m, g, m), v: out, a: 0, q: q_mh };

    // ── S1: pivot-peel (L). offset h → h+1. ──
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
    lemma_step_tail_safe_v(tm, c0, i_peel, h);   // L, end h+1

    // ── S2: walk-left over temp (j steps). offset h+1 → h+1+j. ──
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
    assert(c1.u == 1 * repunit_m((j - 1) as nat, m) + pow_nat(m, (j - 1) as nat) * w_a)
        by(nonlinear_arith)
        requires c1.u == repunit_m((j - 1) as nat, m) + pow_nat(m, (j - 1) as nat) * w_a;
    lemma_run_walk_left_tail_safe_v(tm, c1, q_t, 1, (j - 1) as nat, w_a, i_temp, (h + 1) as nat);
    assert(((h + 1) + j) as nat == (h + 1 + j) as nat);
    lemma_tail_v_chain(tm, c0, 1, j, h, (h + 1) as nat, (h + 1 + j) as nat);

    // ── S3: temp→gap (L). offset h+1+j → h+2+j. ──
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
    lemma_step_tail_safe_v(tm, c2, i_t2g, (h + 1 + j) as nat);   // L, end h+2+j
    lemma_tail_v_chain(tm, c0, (1 + j) as nat, 1, h, (h + 1 + j) as nat, (h + 2 + j) as nat);

    // ── S4: seek-left over the remaining gap (g-j-1 steps), q_a. offset h+2+j → h+g+1. ──
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
    lemma_seek_left_tail_safe_v(tm, c3, q_a, (g - j - 2) as nat, ms, i_gap, (h + 2 + j) as nat);
    assert(((h + 2 + j) + (g - j - 2) + 1) as nat == (h + g + 1) as nat);
    lemma_tail_v_chain(tm, c0, (1 + j + 1) as nat, (g - j - 1) as nat, h, (h + 2 + j) as nat,
        (h + g + 1) as nat);

    // ── S5: a2b transition (L). offset h+g+1 → h+g+2. ──
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
    lemma_step_tail_safe_v(tm, c4, i_a2b, (h + g + 1) as nat);   // L, end h+g+2
    lemma_tail_v_chain(tm, c0, (g + 1) as nat, 1, h, (h + g + 1) as nat, (h + g + 2) as nat);

    let c5 = TmConfig {
        u: repunit_m((big_m - j - 1) as nat, m), v: pile_sym(big_v, 5, j, m), a: 1, q: q_b };
    assert(pile_sym(big_v, 5, 0, m) == big_v);
    assert(pile_sym(big_v, 5, 1, m) == pile_sym(big_v, 5, 0, m) * m + 5);
    if j == 1 {
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
        assert((h + g + 2) as nat == (h + g + j + 1) as nat);
        // tail_safe already at (g+2, h) ending h+g+2 == h+g+j+1; no S6.
    } else {
        // j ≥ 2: a2b lands on the 2nd five; walk the rest. offset h+g+2 → h+g+j+1.
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
        assert(c4b.u == 5 * repunit_m((j - 2) as nat, m)
            + pow_nat(m, (j - 2) as nat) * repunit_m((big_m - j) as nat, m)) by(nonlinear_arith)
            requires c4b.u == ms_div2,
                ms_div2 == 5 * repunit_m((j - 2) as nat, m)
                    + pow_nat(m, (j - 2) as nat) * repunit_m((big_m - j) as nat, m);
        lemma_run_walk_left_tail_safe_v(tm, c4b, q_b, 5, (j - 2) as nat,
            repunit_m((big_m - j) as nat, m), i_fives, (h + g + 2) as nat);
        assert(((h + g + 2) + (j - 2) + 1) as nat == (h + g + j + 1) as nat);
        lemma_tail_v_chain(tm, c0, (g + 2) as nat, (j - 1) as nat, h, (h + g + 2) as nat,
            (h + g + j + 1) as nat);
        assert((g + 2 + (j - 1)) as nat == (g + j + 1) as nat);
    }
}

/// **`mark` is `v`-tail-safe** for its `2·(g + j + 1)` steps (`2 ≤ j < M`) — UNCONDITIONAL, net-disp-0.
/// Forward = [`lemma_mark_fwd_tail_safe_v`] (`h → h+g+j+1`); the MARK turn + all-R return POP back to `h`.
/// `v`-side mirror of [`crate::gap2_tail_phase1::lemma_mark_tail_safe`].
pub proof fn lemma_mark_tail_safe_v(
    tm: Tm, j: nat, big_m: nat, g: nat, out: nat,
    q_mh: nat, q_t: nat, q_a: nat, q_b: nat, q_rf: nat, q_rg: nat, q_rt: nat,
    i_peel: int, i_temp: int, i_t2g: int, i_gap: int, i_a2b: int, i_fives: int, i_mark: int,
    i_rfives: int, i_rf2g: int, i_rgap: int, i_rg2t: int, i_rtemp: int, h: nat,
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
        tail_safe_v(tm, TmConfig { u: copy_u(j, big_m, g, tm.m), v: out, a: 0, q: q_mh },
            (2 * (g + j + 1)) as nat, h),
        tail_end_h_v(tm, TmConfig { u: copy_u(j, big_m, g, tm.m), v: out, a: 0, q: q_mh },
            (2 * (g + j + 1)) as nat, h) == h,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let pile_temp = pile_sym(out * m, 1, j, m);
    let big_v = pile_temp * pow_nat(m, (g - j) as nat);
    let mm1 = repunit_m((big_m - j - 1) as nat, m);
    let ms_next = master_at((j + 1) as nat, big_m, m);
    let c0 = TmConfig { u: copy_u(j, big_m, g, m), v: out, a: 0, q: q_mh };

    // ── FORWARD: c0 → c5, g+j+1 steps. offset h → h+g+j+1. ──
    lemma_mark_fwd(tm, j, big_m, g, out, q_mh, q_t, q_a, q_b,
        i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives);
    lemma_mark_fwd_tail_safe_v(tm, j, big_m, g, out, q_mh, q_t, q_a, q_b,
        i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives, h);
    let c5 = TmConfig { u: mm1, v: pile_sym(big_v, 5, j, m), a: 1, q: q_b };
    assert(tm_run(tm, c0, (g + j + 1) as nat) == c5);

    // ── MARK step (R). offset h+g+j+1 → h+g+j. ──
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
    lemma_step_tail_safe_v(tm, c5, i_mark, (h + g + j + 1) as nat);   // R, end h+g+j
    lemma_tail_v_chain(tm, c0, (g + j + 1) as nat, 1, h, (h + g + j + 1) as nat, (h + g + j) as nat);

    // ── S6: run_walk_right over fives (j steps). offset h+g+j → h+g. ──
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
    lemma_run_walk_right_tail_safe_v(tm, c6, q_rf, 5, 1, (j - 1) as nat, big_v, mm1, i_rfives,
        (h + g + j) as nat);
    assert(((h + g + j) - ((j - 1) + 1)) as nat == (h + g) as nat);
    lemma_tail_v_chain(tm, c0, (g + j + 2) as nat, j, h, (h + g + j) as nat, (h + g) as nat);

    // ── S7: rf→gap transition (R). offset h+g → h+g-1. ──
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
    lemma_step_tail_safe_v(tm, c7, i_rf2g, (h + g) as nat);   // R, end h+g-1
    lemma_tail_v_chain(tm, c0, (g + 2 * j + 2) as nat, 1, h, (h + g) as nat, (h + g - 1) as nat);

    // ── S8: seek_right_blanks over the gap (g-j-1 steps). offset h+g-1 → h+j. ──
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
    lemma_seek_right_tail_safe_v(tm, c8, q_rg, (g - j - 2) as nat, pile_temp, i_rgap, (h + g - 1) as nat);
    assert(((h + g - 1) - ((g - j - 2) + 1)) as nat == (h + j) as nat);
    lemma_tail_v_chain(tm, c0, (g + 2 * j + 3) as nat, (g - j - 1) as nat, h, (h + g - 1) as nat,
        (h + j) as nat);

    // ── S9: rg→temp transition (R). offset h+j → h+j-1. ──
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
    lemma_step_tail_safe_v(tm, c9, i_rg2t, (h + j) as nat);   // R, end h+j-1
    lemma_tail_v_chain(tm, c0, (2 * g + j + 2) as nat, 1, h, (h + j) as nat, (h + j - 1) as nat);

    // ── S10: run_walk_right over temp (j-1 steps). offset h+j-1 → h. ──
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
    lemma_run_walk_right_tail_safe_v(tm, c10, q_rt, 1, 1, (j - 2) as nat, out * m, c9.u, i_rtemp,
        (h + j - 1) as nat);
    assert(((h + j - 1) - ((j - 2) + 1)) as nat == h);
    lemma_tail_v_chain(tm, c0, (2 * g + j + 3) as nat, (j - 1) as nat, h, (h + j - 1) as nat, h);
    assert((2 * g + j + 3 + (j - 1)) as nat == (2 * (g + j + 1)) as nat);
}

/// **`copy_iter` is `v`-tail-safe** for its `2·(g+j+1) + (2·j+2)` steps (`2 ≤ j < M`) — UNCONDITIONAL,
/// net-disp-0: [`lemma_mark_tail_safe_v`] ∘ [`lemma_deposit_tail_safe_v`] at constant `h`. `v`-side mirror
/// of [`crate::gap2_tail_phase1::lemma_copy_iter_tail_safe`].
pub proof fn lemma_copy_iter_tail_safe_v(
    tm: Tm, j: nat, big_m: nat, g: nat, out: nat,
    q_mh: nat, q_t: nat, q_a: nat, q_b: nat, q_rf: nat, q_rg: nat, q_rt: nat, q_dw: nat, q_bk: nat,
    i_peel: int, i_temp: int, i_t2g: int, i_gap: int, i_a2b: int, i_fives: int, i_mark: int,
    i_rfives: int, i_rf2g: int, i_rgap: int, i_rg2t: int, i_rtemp: int,
    i_dpeel: int, i_dtemp: int, i_dins: int, i_dwb: int, h: nat,
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
        tail_safe_v(tm, TmConfig { u: copy_u(j, big_m, g, tm.m), v: out, a: 0, q: q_mh },
            (2 * (g + j + 1) + (2 * j + 2)) as nat, h),
        tail_end_h_v(tm, TmConfig { u: copy_u(j, big_m, g, tm.m), v: out, a: 0, q: q_mh },
            (2 * (g + j + 1) + (2 * j + 2)) as nat, h) == h,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let c0 = TmConfig { u: copy_u(j, big_m, g, m), v: out, a: 0, q: q_mh };
    let ms_next = master_at((j + 1) as nat, big_m, m);
    let w_dep = pow_nat(m, (g - j) as nat) * ms_next;

    // ── MARK: c0 → c_mid (= dec_u(j, w_dep)), 2·(g+j+1) steps. offset h → h. ──
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
    lemma_mark_tail_safe_v(tm, j, big_m, g, out, q_mh, q_t, q_a, q_b, q_rf, q_rg, q_rt,
        i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives, i_mark, i_rfives, i_rf2g, i_rgap, i_rg2t, i_rtemp, h);

    // ── DEPOSIT (home state q_rt): c_mid → c_end, 2·j+2 steps. offset h → h. w_dep%m==0. ──
    lemma_pow_nat_unfold(m, (g - j) as nat);
    assert(w_dep == (pow_nat(m, (g - j - 1) as nat) * ms_next) * m) by(nonlinear_arith)
        requires w_dep == pow_nat(m, (g - j) as nat) * ms_next,
            pow_nat(m, (g - j) as nat) == m * pow_nat(m, (g - j - 1) as nat);
    lemma_div_mod_step(pow_nat(m, (g - j - 1) as nat) * ms_next, m, 0);
    assert(w_dep % m == 0);
    lemma_deposit_tail_safe_v(tm, j, w_dep, out, q_rt, q_dw, q_bk,
        i_dpeel, i_dtemp, i_dins, i_dwb, h);

    // ── chain DEPOSIT ∘ MARK at h. ──
    lemma_tail_v_chain(tm, c0, (2 * (g + j + 1)) as nat, (2 * j + 2) as nat, h, h, h);
    assert((2 * (g + j + 1) + (2 * j + 2)) as nat == ((2 * (g + j + 1)) + (2 * j + 2)) as nat);
}

/// **`copy_loop_general` is `v`-tail-safe** for its `copy_loop_fuel(lo, hi, g)` steps — UNCONDITIONAL,
/// net-disp-0; induct on `hi`, chaining [`lemma_copy_iter_tail_safe_v`] at constant `h`. `v`-side mirror of
/// [`crate::gap2_tail_phase1::lemma_copy_loop_general_tail_safe`].
pub proof fn lemma_copy_loop_general_tail_safe_v(
    tm: Tm, lo: nat, hi: nat, big_m: nat, g: nat, out: nat,
    q_home: nat, q_t: nat, q_a: nat, q_b: nat, q_rf: nat, q_rg: nat, q_rt: nat, q_dw: nat,
    i_peel: int, i_temp: int, i_t2g: int, i_gap: int, i_a2b: int, i_fives: int, i_mark: int,
    i_rfives: int, i_rf2g: int, i_rgap: int, i_rg2t: int, i_rtemp: int,
    i_dpeel: int, i_dtemp: int, i_dins: int, i_dwb: int, h: nat,
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
        tail_safe_v(tm, TmConfig { u: copy_u(lo, big_m, g, tm.m), v: out, a: 0, q: q_home },
            copy_loop_fuel(lo, hi, g), h),
        tail_end_h_v(tm, TmConfig { u: copy_u(lo, big_m, g, tm.m), v: out, a: 0, q: q_home },
            copy_loop_fuel(lo, hi, g), h) == h,
    decreases hi,
{
    reveal(tm_wf);
    let m = tm.m;
    let c_lo = TmConfig { u: copy_u(lo, big_m, g, m), v: out, a: 0, q: q_home };
    if hi == lo {
        assert(copy_loop_fuel(lo, hi, g) == 0);
        assert(tm_run(tm, c_lo, 0) == c_lo);
    } else {
        lemma_copy_loop_general(tm, lo, (hi - 1) as nat, big_m, g, out,
            q_home, q_t, q_a, q_b, q_rf, q_rg, q_rt, q_dw,
            i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives, i_mark, i_rfives, i_rf2g, i_rgap, i_rg2t,
            i_rtemp, i_dpeel, i_dtemp, i_dins, i_dwb);
        lemma_copy_loop_general_tail_safe_v(tm, lo, (hi - 1) as nat, big_m, g, out,
            q_home, q_t, q_a, q_b, q_rf, q_rg, q_rt, q_dw,
            i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives, i_mark, i_rfives, i_rf2g, i_rgap, i_rg2t,
            i_rtemp, i_dpeel, i_dtemp, i_dins, i_dwb, h);
        let c_mid = TmConfig { u: copy_u((hi - 1) as nat, big_m, g, m), v: out, a: 0, q: q_home };
        assert(tm_run(tm, c_lo, copy_loop_fuel(lo, (hi - 1) as nat, g)) == c_mid);

        lemma_copy_iter_tail_safe_v(tm, (hi - 1) as nat, big_m, g, out,
            q_home, q_t, q_a, q_b, q_rf, q_rg, q_rt, q_dw, q_home,
            i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives, i_mark, i_rfives, i_rf2g, i_rgap, i_rg2t,
            i_rtemp, i_dpeel, i_dtemp, i_dins, i_dwb, h);
        let step = (2 * (g + (hi - 1) + 1) + (2 * (hi - 1) + 2)) as nat;
        assert(((hi - 1) + 1) as nat == hi);

        lemma_tail_v_chain(tm, c_lo, copy_loop_fuel(lo, (hi - 1) as nat, g), step, h, h, h);
        assert(copy_loop_fuel(lo, hi, g) == copy_loop_fuel(lo, (hi - 1) as nat, g) + step);
    }
}

/// **`mark_j1` is `v`-tail-safe** for its `2·(g+2)` steps — UNCONDITIONAL, net-disp-0. Forward via
/// [`lemma_mark_fwd_tail_safe_v`] (`j = 1`, `h → h+g+2`); MARK + all-R return POP back to `h`. `v`-side
/// mirror of [`crate::gap2_tail_phase1::lemma_mark_j1_tail_safe`].
pub proof fn lemma_mark_j1_tail_safe_v(
    tm: Tm, big_m: nat, g: nat, out: nat,
    q_mh: nat, q_t: nat, q_a: nat, q_b: nat, q_rf: nat, q_rg: nat, q_rt: nat,
    i_peel: int, i_temp: int, i_t2g: int, i_gap: int, i_a2b: int, i_fives: int, i_mark: int,
    i_rfives: int, i_rf2g: int, i_rgap: int, i_rg2t: int, i_rtemp: int, h: nat,
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
        tail_safe_v(tm, TmConfig { u: copy_u(1, big_m, g, tm.m), v: out, a: 0, q: q_mh },
            (2 * (g + 2)) as nat, h),
        tail_end_h_v(tm, TmConfig { u: copy_u(1, big_m, g, tm.m), v: out, a: 0, q: q_mh },
            (2 * (g + 2)) as nat, h) == h,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let pile_temp = pile_sym(out * m, 1, 1, m);
    let big_v = pile_temp * pow_nat(m, (g - 1) as nat);
    let mm1 = repunit_m((big_m - 2) as nat, m);
    let ms_next = master_at(2, big_m, m);
    let c0 = TmConfig { u: copy_u(1, big_m, g, m), v: out, a: 0, q: q_mh };

    // ── FORWARD: c0 → c5, g+2 steps. offset h → h+g+2. ──
    lemma_mark_fwd(tm, 1, big_m, g, out, q_mh, q_t, q_a, q_b,
        i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives);
    lemma_mark_fwd_tail_safe_v(tm, 1, big_m, g, out, q_mh, q_t, q_a, q_b,
        i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives, h);
    assert((big_m - 1 - 1) as nat == (big_m - 2) as nat);
    let c5 = TmConfig { u: mm1, v: pile_sym(big_v, 5, 1, m), a: 1, q: q_b };
    assert(tm_run(tm, c0, (g + 1 + 1) as nat) == c5);
    assert((g + 1 + 1) as nat == (g + 2) as nat);
    assert((h + g + 1 + 1) as nat == (h + g + 2) as nat);   // mark_fwd_v end for j=1

    // ── MARK step (R). offset h+g+2 → h+g+1. ──
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
    lemma_step_tail_safe_v(tm, c5, i_mark, (h + g + 2) as nat);   // R, end h+g+1
    lemma_tail_v_chain(tm, c0, (g + 2) as nat, 1, h, (h + g + 2) as nat, (h + g + 1) as nat);

    // ── S6: run_walk_right over the single five (1 step). offset h+g+1 → h+g. ──
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
    lemma_run_walk_right_tail_safe_v(tm, c6, q_rf, 5, 1, 0, big_v, mm1, i_rfives, (h + g + 1) as nat);
    assert(((h + g + 1) - (0 + 1)) as nat == (h + g) as nat);
    lemma_tail_v_chain(tm, c0, (g + 3) as nat, 1, h, (h + g + 1) as nat, (h + g) as nat);

    // ── S7: rf→gap transition (R). offset h+g → h+g-1. ──
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
    lemma_step_tail_safe_v(tm, c7, i_rf2g, (h + g) as nat);   // R, end h+g-1
    lemma_tail_v_chain(tm, c0, (g + 4) as nat, 1, h, (h + g) as nat, (h + g - 1) as nat);

    // ── S8: seek_right_blanks over the gap (g-2 steps). offset h+g-1 → h+1. ──
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
    lemma_seek_right_tail_safe_v(tm, c8, q_rg, (g - 3) as nat, pile_temp, i_rgap, (h + g - 1) as nat);
    assert(((h + g - 1) - ((g - 3) + 1)) as nat == (h + 1) as nat);
    lemma_tail_v_chain(tm, c0, (g + 5) as nat, (g - 2) as nat, h, (h + g - 1) as nat, (h + 1) as nat);

    // ── S9: rg→temp transition (R) lands on the pivot. offset h+1 → h. ──
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
    lemma_step_tail_safe_v(tm, c9, i_rg2t, (h + 1) as nat);   // R, end h
    lemma_tail_v_chain(tm, c0, (2 * g + 3) as nat, 1, h, (h + 1) as nat, h);
}

/// **`mark_j0` is `v`-tail-safe** for its `2·g + 2` steps — UNCONDITIONAL, net-disp-0. Forward (S1–S4,
/// `g+1` L-moves) RAISES `h → h+g+1`; MARK + all-R return POP back to `h`. `v`-side mirror of
/// [`crate::gap2_tail_phase1::lemma_mark_j0_tail_safe`].
pub proof fn lemma_mark_j0_tail_safe_v(
    tm: Tm, big_m: nat, g: nat, out: nat,
    q_mh0: nat, q_t0: nat, q_a0: nat, q_rf0: nat, q_rg0: nat, q_rt0: nat,
    i_peel: int, i_temp: int, i_t2g: int, i_gap: int, i_mark: int, i_rf2g: int, i_rgap: int, i_rg2t: int,
    h: nat,
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
        tail_safe_v(tm, TmConfig { u: (1 + pow_nat(tm.m, g) * repunit_m(big_m, tm.m)) as nat, v: out,
            a: 0, q: q_mh0 }, (2 * g + 2) as nat, h),
        tail_end_h_v(tm, TmConfig { u: (1 + pow_nat(tm.m, g) * repunit_m(big_m, tm.m)) as nat, v: out,
            a: 0, q: q_mh0 }, (2 * g + 2) as nat, h) == h,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
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

    // ── S1: pivot-peel (L). offset h → h+1. ──
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
    lemma_step_tail_safe_v(tm, c0, i_peel, h);   // L, end h+1

    // ── S2: walk-left over the single temp one (1 step). offset h+1 → h+2. ──
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
    lemma_run_walk_left_tail_safe_v(tm, c1, q_t0, 1, 0, u1, i_temp, (h + 1) as nat);
    assert(((h + 1) + 1) as nat == (h + 2) as nat);
    lemma_tail_v_chain(tm, c0, 1, 1, h, (h + 1) as nat, (h + 2) as nat);

    // ── S3: temp→gap transition (L). offset h+2 → h+3. ──
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
    lemma_step_tail_safe_v(tm, c2, i_t2g, (h + 2) as nat);   // L, end h+3
    lemma_tail_v_chain(tm, c0, 2, 1, h, (h + 2) as nat, (h + 3) as nat);

    // ── S4: seek-left over the remaining gap (g-2 steps). offset h+3 → h+g+1. ──
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
    lemma_seek_left_tail_safe_v(tm, c3, q_a0, (g - 3) as nat, rm, i_gap, (h + 3) as nat);
    assert(((h + 3) + (g - 3) + 1) as nat == (h + g + 1) as nat);
    lemma_tail_v_chain(tm, c0, 3, (g - 2) as nat, h, (h + 3) as nat, (h + g + 1) as nat);

    // ── MARK step (R). offset h+g+1 → h+g. ──
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
    lemma_step_tail_safe_v(tm, c5, i_mark, (h + g + 1) as nat);   // R, end h+g
    lemma_tail_v_chain(tm, c0, (g + 1) as nat, 1, h, (h + g + 1) as nat, (h + g) as nat);

    // ── S7: rf→gap transition (R). offset h+g → h+g-1. ──
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
    lemma_step_tail_safe_v(tm, c6, i_rf2g, (h + g) as nat);   // R, end h+g-1
    lemma_tail_v_chain(tm, c0, (g + 2) as nat, 1, h, (h + g) as nat, (h + g - 1) as nat);

    // ── S8: seek_right_blanks over the gap (g-2 steps). offset h+g-1 → h+1. ──
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
    lemma_seek_right_tail_safe_v(tm, c7, q_rg0, (g - 3) as nat, pile_temp, i_rgap, (h + g - 1) as nat);
    assert(((h + g - 1) - ((g - 3) + 1)) as nat == (h + 1) as nat);
    lemma_tail_v_chain(tm, c0, (g + 3) as nat, (g - 2) as nat, h, (h + g - 1) as nat, (h + 1) as nat);

    // ── S9: rg→temp transition (R) lands on the pivot. offset h+1 → h. ──
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
    lemma_step_tail_safe_v(tm, c9, i_rg2t, (h + 1) as nat);   // R, end h
    lemma_tail_v_chain(tm, c0, (2 * g + 1) as nat, 1, h, (h + 1) as nat, h);
}

/// **`copy_iter_j1` is `v`-tail-safe** for its `2·g + 8` steps — UNCONDITIONAL, net-disp-0:
/// [`lemma_mark_j1_tail_safe_v`] ∘ [`lemma_deposit_tail_safe_v`] at constant `h`. `v`-side mirror of
/// [`crate::gap2_tail_phase1::lemma_copy_iter_j1_tail_safe`].
pub proof fn lemma_copy_iter_j1_tail_safe_v(
    tm: Tm, big_m: nat, g: nat, out: nat,
    q_mh: nat, q_t: nat, q_a: nat, q_b: nat, q_rf: nat, q_rg: nat, q_rt: nat, q_dw: nat, q_bk: nat,
    i_peel: int, i_temp: int, i_t2g: int, i_gap: int, i_a2b: int, i_fives: int, i_mark: int,
    i_rfives: int, i_rf2g: int, i_rgap: int, i_rg2t: int, i_rtemp: int,
    i_dpeel: int, i_dtemp: int, i_dins: int, i_dwb: int, h: nat,
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
        tail_safe_v(tm, TmConfig { u: copy_u(1, big_m, g, tm.m), v: out, a: 0, q: q_mh },
            (2 * g + 8) as nat, h),
        tail_end_h_v(tm, TmConfig { u: copy_u(1, big_m, g, tm.m), v: out, a: 0, q: q_mh },
            (2 * g + 8) as nat, h) == h,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let c0 = TmConfig { u: copy_u(1, big_m, g, m), v: out, a: 0, q: q_mh };
    let ms_next = master_at(2, big_m, m);
    let w_dep = pow_nat(m, (g - 1) as nat) * ms_next;

    // ── MARK_j1: c0 → c_mid (= dec_u(1, w_dep)), 2·(g+2) steps. offset h → h. ──
    lemma_mark_j1(tm, big_m, g, out, q_mh, q_t, q_a, q_b, q_rf, q_rg, q_rt,
        i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives, i_mark, i_rfives, i_rf2g, i_rgap, i_rg2t, i_rtemp);
    lemma_copy_u_master(1, big_m, g, m);
    lemma_master_at_step(1, big_m, m);
    lemma_pow_nat_add(m, g, 1);
    lemma_pow_nat_add(m, 1, (g - 1) as nat);
    assert((1 + (g - 1)) as nat == g);
    assert(repunit_m(1, m) == 1) by { lemma_repunit_step(0, m); lemma_repunit_zero(m); }
    assert(pow_nat(m, 1) == m) by { lemma_pow_nat_unfold(m, 1); assert(pow_nat(m, 0) == 1); }
    assert(copy_u(1, big_m, g, m) + 4 * pow_nat(m, (g + 1) as nat) == dec_u(1, w_dep, m))
        by(nonlinear_arith)
        requires
            copy_u(1, big_m, g, m) == repunit_m(1, m) + pow_nat(m, g) * master_at(1, big_m, m),
            ms_next == master_at(1, big_m, m) + 4 * pow_nat(m, 1),
            pow_nat(m, (g + 1) as nat) == pow_nat(m, g) * pow_nat(m, 1),
            pow_nat(m, g) == pow_nat(m, 1) * pow_nat(m, (g - 1) as nat),
            pow_nat(m, 1) == m,
            repunit_m(1, m) == 1,
            w_dep == pow_nat(m, (g - 1) as nat) * ms_next,
            dec_u(1, w_dep, m) == repunit_m(1, m) + pow_nat(m, 1) * w_dep;
    let c_mid = TmConfig { u: dec_u(1, w_dep, m), v: out, a: 0, q: q_rt };
    assert(tm_run(tm, c0, (2 * (g + 2)) as nat) == c_mid);
    lemma_mark_j1_tail_safe_v(tm, big_m, g, out, q_mh, q_t, q_a, q_b, q_rf, q_rg, q_rt,
        i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives, i_mark, i_rfives, i_rf2g, i_rgap, i_rg2t, i_rtemp, h);

    // ── DEPOSIT (home q_rt): c_mid → c_end, 4 steps. offset h → h. w_dep%m==0 (g-1≥2). ──
    lemma_pow_nat_unfold(m, (g - 1) as nat);
    assert(w_dep == (pow_nat(m, (g - 2) as nat) * ms_next) * m) by(nonlinear_arith)
        requires w_dep == pow_nat(m, (g - 1) as nat) * ms_next,
            pow_nat(m, (g - 1) as nat) == m * pow_nat(m, (g - 2) as nat);
    lemma_div_mod_step(pow_nat(m, (g - 2) as nat) * ms_next, m, 0);
    assert(w_dep % m == 0);
    lemma_deposit_tail_safe_v(tm, 1, w_dep, out, q_rt, q_dw, q_bk, i_dpeel, i_dtemp, i_dins, i_dwb, h);

    // ── chain. ──
    lemma_tail_v_chain(tm, c0, (2 * (g + 2)) as nat, (2 * 1 + 2) as nat, h, h, h);
    assert((2 * (g + 2) + (2 * 1 + 2)) as nat == (2 * g + 8) as nat);
}

/// **`copy_iter_j0` is `v`-tail-safe** for its `2·g + 4` steps — UNCONDITIONAL, net-disp-0:
/// [`lemma_deposit_tail_safe_v`] (`j = 0`) ∘ [`lemma_mark_j0_tail_safe_v`] at constant `h`. `v`-side mirror
/// of [`crate::gap2_tail_phase1::lemma_copy_iter_j0_tail_safe`].
pub proof fn lemma_copy_iter_j0_tail_safe_v(
    tm: Tm, big_m: nat, g: nat, out: nat,
    q_dh0: nat, q_dw0: nat, q_bk0: nat, q_t0: nat, q_a0: nat, q_rf0: nat, q_rg0: nat, q_rt0: nat,
    i_dpeel: int, i_dtemp: int, i_dins: int, i_dwb: int,
    i_peel: int, i_temp: int, i_t2g: int, i_gap: int, i_mark: int, i_rf2g: int, i_rgap: int, i_rg2t: int,
    h: nat,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        1 <= big_m,
        g >= 3,
        0 <= i_dpeel < tm.quints.len(),
        0 <= i_dtemp < tm.quints.len(),
        0 <= i_dins < tm.quints.len(),
        0 <= i_dwb < tm.quints.len(),
        0 <= i_peel < tm.quints.len(),
        0 <= i_temp < tm.quints.len(),
        0 <= i_t2g < tm.quints.len(),
        0 <= i_gap < tm.quints.len(),
        0 <= i_mark < tm.quints.len(),
        0 <= i_rf2g < tm.quints.len(),
        0 <= i_rgap < tm.quints.len(),
        0 <= i_rg2t < tm.quints.len(),
        tm.quints[i_dpeel] == mk_quint(q_dh0, 0, 0, q_dw0, Dir::L),
        tm.quints[i_dtemp] == mk_quint(q_dw0, 1, 1, q_dw0, Dir::L),
        tm.quints[i_dins] == mk_quint(q_dw0, 0, 1, q_bk0, Dir::R),
        tm.quints[i_dwb] == mk_quint(q_bk0, 1, 1, q_bk0, Dir::R),
        tm.quints[i_peel] == mk_quint(q_bk0, 0, 0, q_t0, Dir::L),
        tm.quints[i_temp] == mk_quint(q_t0, 1, 1, q_t0, Dir::L),
        tm.quints[i_t2g] == mk_quint(q_t0, 0, 0, q_a0, Dir::L),
        tm.quints[i_gap] == mk_quint(q_a0, 0, 0, q_a0, Dir::L),
        tm.quints[i_mark] == mk_quint(q_a0, 1, 5, q_rf0, Dir::R),
        tm.quints[i_rf2g] == mk_quint(q_rf0, 0, 0, q_rg0, Dir::R),
        tm.quints[i_rgap] == mk_quint(q_rg0, 0, 0, q_rg0, Dir::R),
        tm.quints[i_rg2t] == mk_quint(q_rg0, 1, 1, q_rt0, Dir::R),
    ensures
        tail_safe_v(tm, TmConfig { u: copy_u(0, big_m, g, tm.m), v: out, a: 0, q: q_dh0 },
            (2 * g + 4) as nat, h),
        tail_end_h_v(tm, TmConfig { u: copy_u(0, big_m, g, tm.m), v: out, a: 0, q: q_dh0 },
            (2 * g + 4) as nat, h) == h,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let w = (pow_nat(m, g) * repunit_m(big_m, m)) as nat;
    lemma_copy_u_start(big_m, g, m);
    lemma_pow_nat_unfold(m, g);
    assert(w == (pow_nat(m, (g - 1) as nat) * repunit_m(big_m, m)) * m) by(nonlinear_arith)
        requires w == pow_nat(m, g) * repunit_m(big_m, m),
            pow_nat(m, g) == m * pow_nat(m, (g - 1) as nat);
    lemma_div_mod_step(pow_nat(m, (g - 1) as nat) * repunit_m(big_m, m), m, 0);
    assert(w % m == 0);
    assert(dec_u(0, w, m) == w) by {
        lemma_repunit_zero(m);
        assert(pow_nat(m, 0) == 1);
        assert(dec_u(0, w, m) == repunit_m(0, m) + pow_nat(m, 0) * w);
        assert(1nat * w == w) by(nonlinear_arith);
    }
    let c0 = TmConfig { u: copy_u(0, big_m, g, m), v: out, a: 0, q: q_dh0 };
    assert(c0.u == dec_u(0, w, m));

    // ── DEPOSIT (j=0): copy_u(0) → dep0 = w + 1, 2 steps. offset h → h. ──
    lemma_deposit(tm, 0, w, out, q_dh0, q_dw0, q_bk0, i_dpeel, i_dtemp, i_dins, i_dwb);
    assert(pow_nat(m, 0) == 1);
    let dep0 = (1 + pow_nat(m, g) * repunit_m(big_m, m)) as nat;
    assert((dec_u(0, w, m) + pow_nat(m, 0)) as nat == dep0) by {
        assert(dec_u(0, w, m) == w);
        assert(pow_nat(m, 0) == 1);
    }
    let c_dep = TmConfig { u: dep0, v: out, a: 0, q: q_bk0 };
    assert(tm_run(tm, c0, 2) == c_dep);
    lemma_deposit_tail_safe_v(tm, 0, w, out, q_dh0, q_dw0, q_bk0, i_dpeel, i_dtemp, i_dins, i_dwb, h);

    // ── MARK_j0: dep0 → copy_u(1), 2g+2 steps. offset h → h. ──
    lemma_mark_j0_tail_safe_v(tm, big_m, g, out, q_bk0, q_t0, q_a0, q_rf0, q_rg0, q_rt0,
        i_peel, i_temp, i_t2g, i_gap, i_mark, i_rf2g, i_rgap, i_rg2t, h);

    // ── chain DEPOSIT ∘ MARK_j0. ──
    lemma_tail_v_chain(tm, c0, 2, (2 * g + 2) as nat, h, h, h);
    assert((2 + (2 * g + 2)) as nat == (2 * g + 4) as nat);
}

/// **`copy_prefix` is `v`-tail-safe** for its `4·g + 12` steps — UNCONDITIONAL, net-disp-0:
/// [`lemma_copy_iter_j0_tail_safe_v`] ∘ [`lemma_copy_iter_j1_tail_safe_v`] at constant `h`. `v`-side mirror
/// of [`crate::gap2_tail_phase1::lemma_copy_prefix_tail_safe`].
pub proof fn lemma_copy_prefix_tail_safe_v(
    tm: Tm, big_m: nat, g: nat, out: nat,
    q_dh0: nat, q_dw0: nat, q_bk0: nat, q_t0: nat, q_a0: nat, q_rf0: nat, q_rg0: nat,
    q_home: nat, q_t: nat, q_a: nat, q_b: nat, q_rf: nat, q_rg: nat, q_rt: nat, q_dw: nat,
    i_dpeel0: int, i_dtemp0: int, i_dins0: int, i_dwb0: int,
    i_peel0: int, i_temp0: int, i_t2g0: int, i_gap0: int, i_mark0: int, i_rf2g0: int, i_rgap0: int,
    i_rg2t0: int,
    i_peel: int, i_temp: int, i_t2g: int, i_gap: int, i_a2b: int, i_fives: int, i_mark: int,
    i_rfives: int, i_rf2g: int, i_rgap: int, i_rg2t: int, i_rtemp: int,
    i_dpeel: int, i_dtemp: int, i_dins: int, i_dwb: int, h: nat,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        1 < big_m,
        g >= 3,
        0 <= i_dpeel0 < tm.quints.len(),
        0 <= i_dtemp0 < tm.quints.len(),
        0 <= i_dins0 < tm.quints.len(),
        0 <= i_dwb0 < tm.quints.len(),
        0 <= i_peel0 < tm.quints.len(),
        0 <= i_temp0 < tm.quints.len(),
        0 <= i_t2g0 < tm.quints.len(),
        0 <= i_gap0 < tm.quints.len(),
        0 <= i_mark0 < tm.quints.len(),
        0 <= i_rf2g0 < tm.quints.len(),
        0 <= i_rgap0 < tm.quints.len(),
        0 <= i_rg2t0 < tm.quints.len(),
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
        tm.quints[i_dpeel0] == mk_quint(q_dh0, 0, 0, q_dw0, Dir::L),
        tm.quints[i_dtemp0] == mk_quint(q_dw0, 1, 1, q_dw0, Dir::L),
        tm.quints[i_dins0] == mk_quint(q_dw0, 0, 1, q_bk0, Dir::R),
        tm.quints[i_dwb0] == mk_quint(q_bk0, 1, 1, q_bk0, Dir::R),
        tm.quints[i_peel0] == mk_quint(q_bk0, 0, 0, q_t0, Dir::L),
        tm.quints[i_temp0] == mk_quint(q_t0, 1, 1, q_t0, Dir::L),
        tm.quints[i_t2g0] == mk_quint(q_t0, 0, 0, q_a0, Dir::L),
        tm.quints[i_gap0] == mk_quint(q_a0, 0, 0, q_a0, Dir::L),
        tm.quints[i_mark0] == mk_quint(q_a0, 1, 5, q_rf0, Dir::R),
        tm.quints[i_rf2g0] == mk_quint(q_rf0, 0, 0, q_rg0, Dir::R),
        tm.quints[i_rgap0] == mk_quint(q_rg0, 0, 0, q_rg0, Dir::R),
        tm.quints[i_rg2t0] == mk_quint(q_rg0, 1, 1, q_home, Dir::R),
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
        tail_safe_v(tm, TmConfig { u: copy_u(0, big_m, g, tm.m), v: out, a: 0, q: q_dh0 },
            (4 * g + 12) as nat, h),
        tail_end_h_v(tm, TmConfig { u: copy_u(0, big_m, g, tm.m), v: out, a: 0, q: q_dh0 },
            (4 * g + 12) as nat, h) == h,
{
    reveal(tm_wf);
    let m = tm.m;
    let c0 = TmConfig { u: copy_u(0, big_m, g, m), v: out, a: 0, q: q_dh0 };

    // ── j=0: copy_u(0) → copy_u(1), ends q_home. offset h → h. ──
    lemma_copy_iter_j0(tm, big_m, g, out,
        q_dh0, q_dw0, q_bk0, q_t0, q_a0, q_rf0, q_rg0, q_home,
        i_dpeel0, i_dtemp0, i_dins0, i_dwb0,
        i_peel0, i_temp0, i_t2g0, i_gap0, i_mark0, i_rf2g0, i_rgap0, i_rg2t0);
    let c1 = TmConfig { u: copy_u(1, big_m, g, m), v: out, a: 0, q: q_home };
    assert(tm_run(tm, c0, (2 * g + 4) as nat) == c1);
    lemma_copy_iter_j0_tail_safe_v(tm, big_m, g, out,
        q_dh0, q_dw0, q_bk0, q_t0, q_a0, q_rf0, q_rg0, q_home,
        i_dpeel0, i_dtemp0, i_dins0, i_dwb0,
        i_peel0, i_temp0, i_t2g0, i_gap0, i_mark0, i_rf2g0, i_rgap0, i_rg2t0, h);

    // ── j=1: copy_u(1) → copy_u(2), home cycle. offset h → h. ──
    lemma_copy_iter_j1_tail_safe_v(tm, big_m, g, out,
        q_home, q_t, q_a, q_b, q_rf, q_rg, q_rt, q_dw, q_home,
        i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives, i_mark, i_rfives, i_rf2g, i_rgap, i_rg2t, i_rtemp,
        i_dpeel, i_dtemp, i_dins, i_dwb, h);

    // ── chain. ──
    lemma_tail_v_chain(tm, c0, (2 * g + 4) as nat, (2 * g + 8) as nat, h, h, h);
    assert(((2 * g + 4) + (2 * g + 8)) as nat == (4 * g + 12) as nat);
}

/// **`copy_loop` is `v`-tail-safe** for its `full_copy_fuel(M, g)` steps (phase-path `g ≥ M+1`) —
/// UNCONDITIONAL, net-disp-0: [`lemma_copy_prefix_tail_safe_v`] ∘ [`lemma_copy_loop_general_tail_safe_v`] at
/// constant `h`. `v`-side mirror of [`crate::gap2_tail_phase1::lemma_copy_loop_tail_safe`].
pub proof fn lemma_copy_loop_tail_safe_v(
    tm: Tm, big_m: nat, g: nat, out: nat,
    q_dh0: nat, q_dw0: nat, q_bk0: nat, q_t0: nat, q_a0: nat, q_rf0: nat, q_rg0: nat,
    q_home: nat, q_t: nat, q_a: nat, q_b: nat, q_rf: nat, q_rg: nat, q_rt: nat, q_dw: nat,
    i_dpeel0: int, i_dtemp0: int, i_dins0: int, i_dwb0: int,
    i_peel0: int, i_temp0: int, i_t2g0: int, i_gap0: int, i_mark0: int, i_rf2g0: int, i_rgap0: int,
    i_rg2t0: int,
    i_peel: int, i_temp: int, i_t2g: int, i_gap: int, i_a2b: int, i_fives: int, i_mark: int,
    i_rfives: int, i_rf2g: int, i_rgap: int, i_rg2t: int, i_rtemp: int,
    i_dpeel: int, i_dtemp: int, i_dins: int, i_dwb: int, h: nat,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        3 <= big_m,
        g >= big_m + 1,
        0 <= i_dpeel0 < tm.quints.len(),
        0 <= i_dtemp0 < tm.quints.len(),
        0 <= i_dins0 < tm.quints.len(),
        0 <= i_dwb0 < tm.quints.len(),
        0 <= i_peel0 < tm.quints.len(),
        0 <= i_temp0 < tm.quints.len(),
        0 <= i_t2g0 < tm.quints.len(),
        0 <= i_gap0 < tm.quints.len(),
        0 <= i_mark0 < tm.quints.len(),
        0 <= i_rf2g0 < tm.quints.len(),
        0 <= i_rgap0 < tm.quints.len(),
        0 <= i_rg2t0 < tm.quints.len(),
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
        tm.quints[i_dpeel0] == mk_quint(q_dh0, 0, 0, q_dw0, Dir::L),
        tm.quints[i_dtemp0] == mk_quint(q_dw0, 1, 1, q_dw0, Dir::L),
        tm.quints[i_dins0] == mk_quint(q_dw0, 0, 1, q_bk0, Dir::R),
        tm.quints[i_dwb0] == mk_quint(q_bk0, 1, 1, q_bk0, Dir::R),
        tm.quints[i_peel0] == mk_quint(q_bk0, 0, 0, q_t0, Dir::L),
        tm.quints[i_temp0] == mk_quint(q_t0, 1, 1, q_t0, Dir::L),
        tm.quints[i_t2g0] == mk_quint(q_t0, 0, 0, q_a0, Dir::L),
        tm.quints[i_gap0] == mk_quint(q_a0, 0, 0, q_a0, Dir::L),
        tm.quints[i_mark0] == mk_quint(q_a0, 1, 5, q_rf0, Dir::R),
        tm.quints[i_rf2g0] == mk_quint(q_rf0, 0, 0, q_rg0, Dir::R),
        tm.quints[i_rgap0] == mk_quint(q_rg0, 0, 0, q_rg0, Dir::R),
        tm.quints[i_rg2t0] == mk_quint(q_rg0, 1, 1, q_home, Dir::R),
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
        tail_safe_v(tm, TmConfig { u: copy_u(0, big_m, g, tm.m), v: out, a: 0, q: q_dh0 },
            full_copy_fuel(big_m, g), h),
        tail_end_h_v(tm, TmConfig { u: copy_u(0, big_m, g, tm.m), v: out, a: 0, q: q_dh0 },
            full_copy_fuel(big_m, g), h) == h,
{
    reveal(tm_wf);
    let m = tm.m;
    let c0 = TmConfig { u: copy_u(0, big_m, g, m), v: out, a: 0, q: q_dh0 };

    // ── PREFIX: copy_u(0) → copy_u(2), 4g+12 steps. offset h → h. ──
    lemma_copy_prefix(tm, big_m, g, out,
        q_dh0, q_dw0, q_bk0, q_t0, q_a0, q_rf0, q_rg0,
        q_home, q_t, q_a, q_b, q_rf, q_rg, q_rt, q_dw,
        i_dpeel0, i_dtemp0, i_dins0, i_dwb0,
        i_peel0, i_temp0, i_t2g0, i_gap0, i_mark0, i_rf2g0, i_rgap0, i_rg2t0,
        i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives, i_mark, i_rfives, i_rf2g, i_rgap, i_rg2t, i_rtemp,
        i_dpeel, i_dtemp, i_dins, i_dwb);
    let c2 = TmConfig { u: copy_u(2, big_m, g, m), v: out, a: 0, q: q_home };
    assert(tm_run(tm, c0, (4 * g + 12) as nat) == c2);
    lemma_copy_prefix_tail_safe_v(tm, big_m, g, out,
        q_dh0, q_dw0, q_bk0, q_t0, q_a0, q_rf0, q_rg0,
        q_home, q_t, q_a, q_b, q_rf, q_rg, q_rt, q_dw,
        i_dpeel0, i_dtemp0, i_dins0, i_dwb0,
        i_peel0, i_temp0, i_t2g0, i_gap0, i_mark0, i_rf2g0, i_rgap0, i_rg2t0,
        i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives, i_mark, i_rfives, i_rf2g, i_rgap, i_rg2t, i_rtemp,
        i_dpeel, i_dtemp, i_dins, i_dwb, h);

    // ── MIDDLE: copy_u(2) → copy_u(M), general. offset h → h. ──
    lemma_copy_loop_general_tail_safe_v(tm, 2, big_m, big_m, g, out,
        q_home, q_t, q_a, q_b, q_rf, q_rg, q_rt, q_dw,
        i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives, i_mark, i_rfives, i_rf2g, i_rgap, i_rg2t,
        i_rtemp, i_dpeel, i_dtemp, i_dins, i_dwb, h);

    // ── chain: prefix ∘ middle. ──
    assert(full_copy_fuel(big_m, g) == (4 * g + 12) as nat + copy_loop_fuel(2, big_m, g));
    lemma_tail_v_chain(tm, c0, (4 * g + 12) as nat, copy_loop_fuel(2, big_m, g), h, h, h);
}

/// **`copy_refresh` is `v`-tail-safe** for its `copy_refresh_fuel(M, g)` steps — UNCONDITIONAL, net-disp-0.
/// The capstone of GAP-2 phase-1 `v`-side: [`lemma_copy_loop_tail_safe_v`] (or
/// [`lemma_copy_prefix_tail_safe_v`] for `M == 2`) ∘ [`lemma_mark_terminate_tail_safe_v`] ∘
/// [`lemma_unmark_tail_safe_v`], all at constant `h`. `v`-side mirror of
/// [`crate::gap2_tail_phase1::lemma_copy_refresh_tail_safe`].
pub proof fn lemma_copy_refresh_tail_safe_v(
    tm: Tm, big_m: nat, g: nat, out: nat,
    q_dh0: nat, q_dw0: nat, q_bk0: nat, q_t0: nat, q_a0: nat, q_rf0: nat, q_rg0: nat,
    q_home: nat, q_t: nat, q_a: nat, q_b: nat, q_rf: nat, q_rg: nat, q_rt: nat, q_dw: nat,
    q_turn: nat, q_turng: nat, q_ret: nat,
    q_ut: nat, q_ua: nat, q_uf: nat, q_ur: nat, q_urg: nat, q_urt: nat,
    i_dpeel0: int, i_dtemp0: int, i_dins0: int, i_dwb0: int,
    i_peel0: int, i_temp0: int, i_t2g0: int, i_gap0: int, i_mark0: int, i_rf2g0: int, i_rgap0: int,
    i_rg2t0: int,
    i_peel: int, i_temp: int, i_t2g: int, i_gap: int, i_a2b: int, i_fives: int, i_mark: int,
    i_rfives: int, i_rf2g: int, i_rgap: int, i_rg2t: int, i_rtemp: int,
    i_dpeel: int, i_dtemp: int, i_dins: int, i_dwb: int,
    i_turn: int, i_master: int, i_tm2g: int, i_trgap: int, i_tg2t: int, i_trtemp: int,
    i_upeel: int, i_utemp: int, i_ut2g: int, i_ugap: int, i_uu1: int, i_uurest: int,
    i_uturn: int, i_umaster: int, i_um2g: int, i_urgap: int, i_ug2t: int, i_urtemp: int, h: nat,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        2 <= big_m,
        g >= big_m + 2,
        0 <= i_dpeel0 < tm.quints.len(),
        0 <= i_dtemp0 < tm.quints.len(),
        0 <= i_dins0 < tm.quints.len(),
        0 <= i_dwb0 < tm.quints.len(),
        0 <= i_peel0 < tm.quints.len(),
        0 <= i_temp0 < tm.quints.len(),
        0 <= i_t2g0 < tm.quints.len(),
        0 <= i_gap0 < tm.quints.len(),
        0 <= i_mark0 < tm.quints.len(),
        0 <= i_rf2g0 < tm.quints.len(),
        0 <= i_rgap0 < tm.quints.len(),
        0 <= i_rg2t0 < tm.quints.len(),
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
        0 <= i_turn < tm.quints.len(),
        0 <= i_master < tm.quints.len(),
        0 <= i_tm2g < tm.quints.len(),
        0 <= i_trgap < tm.quints.len(),
        0 <= i_tg2t < tm.quints.len(),
        0 <= i_trtemp < tm.quints.len(),
        0 <= i_upeel < tm.quints.len(),
        0 <= i_utemp < tm.quints.len(),
        0 <= i_ut2g < tm.quints.len(),
        0 <= i_ugap < tm.quints.len(),
        0 <= i_uu1 < tm.quints.len(),
        0 <= i_uurest < tm.quints.len(),
        0 <= i_uturn < tm.quints.len(),
        0 <= i_umaster < tm.quints.len(),
        0 <= i_um2g < tm.quints.len(),
        0 <= i_urgap < tm.quints.len(),
        0 <= i_ug2t < tm.quints.len(),
        0 <= i_urtemp < tm.quints.len(),
        tm.quints[i_dpeel0] == mk_quint(q_dh0, 0, 0, q_dw0, Dir::L),
        tm.quints[i_dtemp0] == mk_quint(q_dw0, 1, 1, q_dw0, Dir::L),
        tm.quints[i_dins0] == mk_quint(q_dw0, 0, 1, q_bk0, Dir::R),
        tm.quints[i_dwb0] == mk_quint(q_bk0, 1, 1, q_bk0, Dir::R),
        tm.quints[i_peel0] == mk_quint(q_bk0, 0, 0, q_t0, Dir::L),
        tm.quints[i_temp0] == mk_quint(q_t0, 1, 1, q_t0, Dir::L),
        tm.quints[i_t2g0] == mk_quint(q_t0, 0, 0, q_a0, Dir::L),
        tm.quints[i_gap0] == mk_quint(q_a0, 0, 0, q_a0, Dir::L),
        tm.quints[i_mark0] == mk_quint(q_a0, 1, 5, q_rf0, Dir::R),
        tm.quints[i_rf2g0] == mk_quint(q_rf0, 0, 0, q_rg0, Dir::R),
        tm.quints[i_rgap0] == mk_quint(q_rg0, 0, 0, q_rg0, Dir::R),
        tm.quints[i_rg2t0] == mk_quint(q_rg0, 1, 1, q_home, Dir::R),
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
        tm.quints[i_turn] == mk_quint(q_b, 0, 0, q_turn, Dir::R),
        tm.quints[i_master] == mk_quint(q_turn, 5, 5, q_turn, Dir::R),
        tm.quints[i_tm2g] == mk_quint(q_turn, 0, 0, q_turng, Dir::R),
        tm.quints[i_trgap] == mk_quint(q_turng, 0, 0, q_turng, Dir::R),
        tm.quints[i_tg2t] == mk_quint(q_turng, 1, 1, q_ret, Dir::R),
        tm.quints[i_trtemp] == mk_quint(q_ret, 1, 1, q_ret, Dir::R),
        tm.quints[i_upeel] == mk_quint(q_ret, 0, 0, q_ut, Dir::L),
        tm.quints[i_utemp] == mk_quint(q_ut, 1, 1, q_ut, Dir::L),
        tm.quints[i_ut2g] == mk_quint(q_ut, 0, 0, q_ua, Dir::L),
        tm.quints[i_ugap] == mk_quint(q_ua, 0, 0, q_ua, Dir::L),
        tm.quints[i_uu1] == mk_quint(q_ua, 5, 1, q_uf, Dir::L),
        tm.quints[i_uurest] == mk_quint(q_uf, 5, 1, q_uf, Dir::L),
        tm.quints[i_uturn] == mk_quint(q_uf, 0, 0, q_ur, Dir::R),
        tm.quints[i_umaster] == mk_quint(q_ur, 1, 1, q_ur, Dir::R),
        tm.quints[i_um2g] == mk_quint(q_ur, 0, 0, q_urg, Dir::R),
        tm.quints[i_urgap] == mk_quint(q_urg, 0, 0, q_urg, Dir::R),
        tm.quints[i_ug2t] == mk_quint(q_urg, 1, 1, q_urt, Dir::R),
        tm.quints[i_urtemp] == mk_quint(q_urt, 1, 1, q_urt, Dir::R),
    ensures
        tail_safe_v(tm, TmConfig { u: copy_u(0, big_m, g, tm.m), v: out, a: 0, q: q_dh0 },
            copy_refresh_fuel(big_m, g), h),
        tail_end_h_v(tm, TmConfig { u: copy_u(0, big_m, g, tm.m), v: out, a: 0, q: q_dh0 },
            copy_refresh_fuel(big_m, g), h) == h,
{
    reveal(tm_wf);
    let m = tm.m;
    let bounce = (2 * g + 2 * big_m + 2) as nat;
    let c0 = TmConfig { u: copy_u(0, big_m, g, m), v: out, a: 0, q: q_dh0 };
    let c_loop = TmConfig { u: copy_u(big_m, big_m, g, m), v: out, a: 0, q: q_home };

    // ── PHASE 1 — LOOP: copy_u(0) → copy_u(M), full_copy_fuel steps. offset h → h. ──
    if big_m == 2 {
        lemma_copy_prefix(tm, big_m, g, out,
            q_dh0, q_dw0, q_bk0, q_t0, q_a0, q_rf0, q_rg0,
            q_home, q_t, q_a, q_b, q_rf, q_rg, q_rt, q_dw,
            i_dpeel0, i_dtemp0, i_dins0, i_dwb0,
            i_peel0, i_temp0, i_t2g0, i_gap0, i_mark0, i_rf2g0, i_rgap0, i_rg2t0,
            i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives, i_mark, i_rfives, i_rf2g, i_rgap, i_rg2t,
            i_rtemp, i_dpeel, i_dtemp, i_dins, i_dwb);
        assert(copy_u(2, big_m, g, m) == copy_u(big_m, big_m, g, m));
        assert(copy_loop_fuel(2, big_m, g) == 0);
        assert(full_copy_fuel(big_m, g) == (4 * g + 12) as nat);
        assert(tm_run(tm, c0, full_copy_fuel(big_m, g)) == c_loop);
        lemma_copy_prefix_tail_safe_v(tm, big_m, g, out,
            q_dh0, q_dw0, q_bk0, q_t0, q_a0, q_rf0, q_rg0,
            q_home, q_t, q_a, q_b, q_rf, q_rg, q_rt, q_dw,
            i_dpeel0, i_dtemp0, i_dins0, i_dwb0,
            i_peel0, i_temp0, i_t2g0, i_gap0, i_mark0, i_rf2g0, i_rgap0, i_rg2t0,
            i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives, i_mark, i_rfives, i_rf2g, i_rgap, i_rg2t,
            i_rtemp, i_dpeel, i_dtemp, i_dins, i_dwb, h);
    } else {
        lemma_copy_loop(tm, big_m, g, out,
            q_dh0, q_dw0, q_bk0, q_t0, q_a0, q_rf0, q_rg0,
            q_home, q_t, q_a, q_b, q_rf, q_rg, q_rt, q_dw,
            i_dpeel0, i_dtemp0, i_dins0, i_dwb0,
            i_peel0, i_temp0, i_t2g0, i_gap0, i_mark0, i_rf2g0, i_rgap0, i_rg2t0,
            i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives, i_mark, i_rfives, i_rf2g, i_rgap, i_rg2t,
            i_rtemp, i_dpeel, i_dtemp, i_dins, i_dwb);
        assert(tm_run(tm, c0, full_copy_fuel(big_m, g)) == c_loop);
        lemma_copy_loop_tail_safe_v(tm, big_m, g, out,
            q_dh0, q_dw0, q_bk0, q_t0, q_a0, q_rf0, q_rg0,
            q_home, q_t, q_a, q_b, q_rf, q_rg, q_rt, q_dw,
            i_dpeel0, i_dtemp0, i_dins0, i_dwb0,
            i_peel0, i_temp0, i_t2g0, i_gap0, i_mark0, i_rf2g0, i_rgap0, i_rg2t0,
            i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives, i_mark, i_rfives, i_rf2g, i_rgap, i_rg2t,
            i_rtemp, i_dpeel, i_dtemp, i_dins, i_dwb, h);
    }

    // ── PHASE 2 — TERMINATE: copy_u(M)@q_home → copy_u(M)@q_ret, bounce steps. offset h → h. ──
    lemma_mark_terminate(tm, big_m, g, out,
        q_home, q_t, q_a, q_b, q_turn, q_turng, q_ret,
        i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives,
        i_turn, i_master, i_tm2g, i_trgap, i_tg2t, i_trtemp);
    let c_term = TmConfig { u: copy_u(big_m, big_m, g, m), v: out, a: 0, q: q_ret };
    assert(tm_run(tm, c_loop, bounce) == c_term);
    lemma_mark_terminate_tail_safe_v(tm, big_m, g, out,
        q_home, q_t, q_a, q_b, q_turn, q_turng, q_ret,
        i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives,
        i_turn, i_master, i_tm2g, i_trgap, i_tg2t, i_trtemp, h);

    // ── PHASE 3 — UNMARK: copy_u(M)@q_ret → result, bounce steps. offset h → h. ──
    lemma_unmark_tail_safe_v(tm, big_m, g, out,
        q_ret, q_ut, q_ua, q_uf, q_ur, q_urg, q_urt,
        i_upeel, i_utemp, i_ut2g, i_ugap, i_uu1, i_uurest,
        i_uturn, i_umaster, i_um2g, i_urgap, i_ug2t, i_urtemp, h);

    // ── chain: LOOP ∘ TERMINATE ∘ UNMARK at h. ──
    lemma_tm_run_split(tm, c0, full_copy_fuel(big_m, g), bounce);
    let mid = (full_copy_fuel(big_m, g) + bounce) as nat;
    assert(tm_run(tm, c0, mid) == c_term);
    lemma_tail_v_chain(tm, c0, full_copy_fuel(big_m, g), bounce, h, h, h);   // LOOP ∘ TERMINATE
    lemma_tail_v_chain(tm, c0, mid, bounce, h, h, h);                        // (·) ∘ UNMARK
    assert(copy_refresh_fuel(big_m, g) == (mid + bounce) as nat);
}

} // verus!
