//! # GAP-2 G2-F — tail-safety of copy_refresh's phases (composition layer)
//!
//! Discharges [`crate::gap2_tail_lift::tail_safe`] for the multi-segment gadgets of `tm_copy_refresh`, by
//! mirroring each gadget's segment decomposition and chaining the per-segment companions
//! ([`crate::gap2_tail_walks`]) with [`crate::gap2_tail_lift::lemma_tail_chain`]. Only the per-step
//! direction and the tail offset `h` are tracked; the value arithmetic is re-derived exactly as in the
//! source gadget (the companions' preconditions need the same segment-config forms).
//!
//! The **terminate forward** is the tightest path: the master-detecting fives-walk drives the offset to
//! exactly `0` at the blank above the master (entry `h = M`, length `M`), and the subsequent turn is an
//! R-move — so `h = 0` is reached only at an unconditional R-step. This is the one place the design's
//! single separator blank between master and tail is load-bearing, and it verifies.
//!
//! Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use crate::tm::{Tm, TmConfig, tm_wf, tm_run, tm_step, apply_quint, quint_matches};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};
use crate::tm_two_counter::{repunit_m, lemma_repunit_zero, lemma_repunit_step};
use crate::tm_dstring::{pow_nat, lemma_pow_nat_unfold};
use crate::tm_copy_refresh::{copy_u, lemma_copy_u_end, lemma_pow_nat_add,
    lemma_run_walk_left, lemma_seek_left_blanks, lemma_run_walk_right, lemma_seek_right_blanks,
    lemma_terminate_fwd, lemma_unmark_fwd, lemma_unmark_fives_left, lemma_pile_sym_div_mod};
use crate::tm_emit::{pile_sym, lemma_pile_sym_shift};
use crate::tm_run_lemmas::lemma_tm_run_split;
use verus_group_theory::word_numbering::lemma_div_mod_step;
use crate::gap2_tail_lift::{tail_safe, tail_end_h, lemma_step_tail_safe, lemma_tail_chain};
use crate::gap2_tail_walks::{lemma_seek_left_tail_safe, lemma_run_walk_left_tail_safe,
    lemma_unmark_fives_left_tail_safe, lemma_seek_right_tail_safe, lemma_run_walk_right_tail_safe};

verus! {

/// **`terminate_fwd` is tail-safe** for its `g+M+1` steps when the tail enters at `h = g+M+1` (one
/// separator blank above the master), and the offset is driven to exactly `0` (the head ends on the blank
/// above the all-fives master). Mirror of [`crate::tm_copy_refresh::lemma_terminate_fwd`]: six segments
/// (peel, temp-walk, t2g, gap-seek, a2b, fives-walk), chained by [`lemma_tail_chain`].
pub proof fn lemma_terminate_fwd_tail_safe(
    tm: Tm, big_m: nat, g: nat, out: nat,
    q_home: nat, q_t: nat, q_a: nat, q_b: nat,
    i_peel: int, i_temp: int, i_t2g: int, i_gap: int, i_a2b: int, i_fives: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        2 <= big_m,
        g >= big_m + 2,
        0 <= i_peel < tm.quints.len(),
        0 <= i_temp < tm.quints.len(),
        0 <= i_t2g < tm.quints.len(),
        0 <= i_gap < tm.quints.len(),
        0 <= i_a2b < tm.quints.len(),
        0 <= i_fives < tm.quints.len(),
        tm.quints[i_peel] == mk_quint(q_home, 0, 0, q_t, Dir::L),
        tm.quints[i_temp] == mk_quint(q_t, 1, 1, q_t, Dir::L),
        tm.quints[i_t2g] == mk_quint(q_t, 0, 0, q_a, Dir::L),
        tm.quints[i_gap] == mk_quint(q_a, 0, 0, q_a, Dir::L),
        tm.quints[i_a2b] == mk_quint(q_a, 5, 5, q_b, Dir::L),
        tm.quints[i_fives] == mk_quint(q_b, 5, 5, q_b, Dir::L),
    ensures
        tail_safe(tm, TmConfig { u: copy_u(big_m, big_m, g, tm.m), v: out, a: 0, q: q_home },
            (g + big_m + 1) as nat, (g + big_m + 1) as nat),
        tail_end_h(tm, TmConfig { u: copy_u(big_m, big_m, g, tm.m), v: out, a: 0, q: q_home },
            (g + big_m + 1) as nat, (g + big_m + 1) as nat) == 0,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let h0 = (g + big_m + 1) as nat;
    let rm = repunit_m(big_m, m);
    let fives = (5 * rm) as nat;
    lemma_copy_u_end(big_m, g, m);
    assert(copy_u(big_m, big_m, g, m) == rm + pow_nat(m, g) * fives) by(nonlinear_arith)
        requires copy_u(big_m, big_m, g, m) == rm + pow_nat(m, g) * (5 * rm), fives == 5 * rm;
    let c0 = TmConfig { u: copy_u(big_m, big_m, g, m), v: out, a: 0, q: q_home };
    assert(c0.u == rm + pow_nat(m, g) * fives);

    // ── S1: pivot-peel (L). offset h0 → h0-1 == g+M. ──
    lemma_repunit_step((big_m - 1) as nat, m);
    assert(((big_m - 1) + 1) as nat == big_m);
    lemma_pow_nat_unfold(m, g);
    let u1 = repunit_m((big_m - 1) as nat, m) + pow_nat(m, (g - 1) as nat) * fives;
    assert(c0.u == u1 * m + 1) by(nonlinear_arith)
        requires
            c0.u == rm + pow_nat(m, g) * fives,
            rm == m * repunit_m((big_m - 1) as nat, m) + 1,
            pow_nat(m, g) == m * pow_nat(m, (g - 1) as nat),
            u1 == repunit_m((big_m - 1) as nat, m) + pow_nat(m, (g - 1) as nat) * fives;
    lemma_div_mod_step(u1, m, 1);
    lemma_tm_step_picks(tm, c0, i_peel);
    let c1 = apply_quint(tm.quints[i_peel], c0, m);
    assert(tm_step(tm, c0) == Some(c1));
    assert(c1.u == u1 && c1.v == out * m && c1.a == 1 && c1.q == q_t);
    assert(tm_run(tm, c1, 0) == c1);
    assert(tm_run(tm, c0, 1) == c1);
    // tail_safe S1:
    assert(quint_matches(tm.quints[i_peel], c0));
    lemma_step_tail_safe(tm, c0, i_peel, h0);   // tail_safe(c0,1,h0), end == h0-1

    // ── S2: walk-left over temp (M steps). offset g+M → g. ──
    let w_a = (pow_nat(m, (g - big_m) as nat) * fives) as nat;
    lemma_pow_nat_add(m, (big_m - 1) as nat, (g - big_m) as nat);
    assert(((big_m - 1) + (g - big_m)) as nat == (g - 1) as nat);
    assert(c1.u == repunit_m((big_m - 1) as nat, m) + pow_nat(m, (big_m - 1) as nat) * w_a)
        by(nonlinear_arith)
        requires
            c1.u == repunit_m((big_m - 1) as nat, m) + pow_nat(m, (g - 1) as nat) * fives,
            pow_nat(m, (g - 1) as nat) == pow_nat(m, (big_m - 1) as nat) * pow_nat(m, (g - big_m) as nat),
            w_a == pow_nat(m, (g - big_m) as nat) * fives;
    lemma_run_walk_left(tm, c1, q_t, 1, (big_m - 1) as nat, w_a, i_temp);
    lemma_pow_nat_unfold(m, (g - big_m) as nat);
    assert(w_a == (pow_nat(m, (g - big_m - 1) as nat) * fives) * m) by(nonlinear_arith)
        requires w_a == pow_nat(m, (g - big_m) as nat) * fives,
            pow_nat(m, (g - big_m) as nat) == m * pow_nat(m, (g - big_m - 1) as nat);
    lemma_div_mod_step(pow_nat(m, (g - big_m - 1) as nat) * fives, m, 0);
    let p_t = pile_sym(out * m, 1, big_m, m);
    let c2 = TmConfig { u: pow_nat(m, (g - big_m - 1) as nat) * fives, v: p_t, a: 0, q: q_t };
    assert(((big_m - 1) + 1) as nat == big_m);
    assert(tm_run(tm, c1, big_m) == c2);
    lemma_tm_run_split(tm, c0, 1, big_m);
    assert(tm_run(tm, c0, (1 + big_m) as nat) == c2);
    // tail_safe S2 + chain S1·S2:
    lemma_run_walk_left_tail_safe(tm, c1, q_t, 1, (big_m - 1) as nat, w_a, i_temp, (g + big_m) as nat);
    lemma_tail_chain(tm, c0, 1, big_m, h0, (g + big_m) as nat, g);

    // ── S3: temp→gap (L). offset g → g-1. ──
    lemma_pow_nat_unfold(m, (g - big_m - 1) as nat);
    assert(c2.u == (pow_nat(m, (g - big_m - 2) as nat) * fives) * m) by(nonlinear_arith)
        requires c2.u == pow_nat(m, (g - big_m - 1) as nat) * fives,
            pow_nat(m, (g - big_m - 1) as nat) == m * pow_nat(m, (g - big_m - 2) as nat);
    lemma_div_mod_step(pow_nat(m, (g - big_m - 2) as nat) * fives, m, 0);
    lemma_tm_step_picks(tm, c2, i_t2g);
    let c3 = apply_quint(tm.quints[i_t2g], c2, m);
    assert(tm_step(tm, c2) == Some(c3));
    assert(c3.u == pow_nat(m, (g - big_m - 2) as nat) * fives && c3.v == p_t * m && c3.a == 0
        && c3.q == q_a);
    assert(tm_run(tm, c3, 0) == c3);
    assert(tm_run(tm, c2, 1) == c3);
    lemma_tm_run_split(tm, c0, (1 + big_m) as nat, 1);
    assert(tm_run(tm, c0, (1 + big_m + 1) as nat) == c3);
    // tail_safe S3 + chain:
    assert(quint_matches(tm.quints[i_t2g], c2));
    lemma_step_tail_safe(tm, c2, i_t2g, g);
    lemma_tail_chain(tm, c0, (1 + big_m) as nat, 1, h0, g, (g - 1) as nat);

    // ── S4: seek-left over the remaining gap (g-M-1 steps). offset g-1 → M. ──
    lemma_div_mod_step((5 * repunit_m((big_m - 1) as nat, m)) as nat, m, 5);
    assert(fives == (5 * repunit_m((big_m - 1) as nat, m)) * m + 5) by(nonlinear_arith)
        requires fives == 5 * rm, rm == m * repunit_m((big_m - 1) as nat, m) + 1;
    assert(fives % m == 5) by {
        lemma_div_mod_step((5 * repunit_m((big_m - 1) as nat, m)) as nat, m, 5);
        assert(fives == (5 * repunit_m((big_m - 1) as nat, m)) * m + 5);
    }
    assert(fives % m != 0);
    lemma_seek_left_blanks(tm, c3, q_a, (g - big_m - 2) as nat, fives, i_gap);
    let p_g = (p_t * pow_nat(m, (g - big_m) as nat)) as nat;
    let c4 = TmConfig { u: fives / m, v: (p_t * m) * pow_nat(m, (g - big_m - 1) as nat), a: 5, q: q_a };
    assert(((g - big_m - 2) + 1) as nat == (g - big_m - 1) as nat);
    assert(tm_run(tm, c3, (g - big_m - 1) as nat) == c4);
    lemma_tm_run_split(tm, c0, (1 + big_m + 1) as nat, (g - big_m - 1) as nat);
    assert((1 + big_m + 1 + (g - big_m - 1)) as nat == (g + 1) as nat);
    assert(tm_run(tm, c0, (g + 1) as nat) == c4);
    assert(fives / m == 5 * repunit_m((big_m - 1) as nat, m)) by {
        lemma_div_mod_step((5 * repunit_m((big_m - 1) as nat, m)) as nat, m, 5);
        assert(fives == (5 * repunit_m((big_m - 1) as nat, m)) * m + 5);
    }
    // tail_safe S4 + chain. seek companion needs c3.u == m^(g-M-2)·fives, fives%m != 0.
    lemma_seek_left_tail_safe(tm, c3, q_a, (g - big_m - 2) as nat, fives, i_gap, (g - 1) as nat);
    assert(((g - 1) - (g - big_m - 1)) as nat == big_m);
    lemma_tail_chain(tm, c0, (1 + big_m + 1) as nat, (g - big_m - 1) as nat, h0, (g - 1) as nat, big_m);

    // c4.v regroups to p_g·m^(g-M-1)·m form: (p_t·m)·m^(g-M-1) == p_g.
    assert((p_t * m) * pow_nat(m, (g - big_m - 1) as nat) == p_g) by(nonlinear_arith)
        requires p_g == p_t * pow_nat(m, (g - big_m) as nat),
            pow_nat(m, (g - big_m) as nat) == m * pow_nat(m, (g - big_m - 1) as nat);

    // ── S5: a2b (L) — enter q_b on the lowest master five. offset M → M-1. ──
    lemma_repunit_step((big_m - 2) as nat, m);
    assert(((big_m - 2) + 1) as nat == (big_m - 1) as nat);
    let c4u_div = (5 * repunit_m((big_m - 2) as nat, m)) as nat;
    assert(c4.u == c4u_div * m + 5) by(nonlinear_arith)
        requires c4.u == 5 * repunit_m((big_m - 1) as nat, m),
            repunit_m((big_m - 1) as nat, m) == m * repunit_m((big_m - 2) as nat, m) + 1,
            c4u_div == 5 * repunit_m((big_m - 2) as nat, m);
    lemma_div_mod_step(c4u_div, m, 5);
    lemma_tm_step_picks(tm, c4, i_a2b);
    let c5 = apply_quint(tm.quints[i_a2b], c4, m);
    assert(tm_step(tm, c4) == Some(c5));
    assert(c5.u == c4u_div && c5.v == p_g * m + 5 && c5.a == 5 && c5.q == q_b);
    assert(tm_run(tm, c5, 0) == c5);
    assert(tm_run(tm, c4, 1) == c5);
    lemma_tm_run_split(tm, c0, (g + 1) as nat, 1);
    assert(tm_run(tm, c0, (g + 2) as nat) == c5);
    // tail_safe S5 + chain:
    assert(quint_matches(tm.quints[i_a2b], c4));
    lemma_step_tail_safe(tm, c4, i_a2b, big_m);
    lemma_tail_chain(tm, c0, (g + 1) as nat, 1, h0, big_m, (big_m - 1) as nat);

    // ── S6: walk-left over the remaining M-1 fives (q_b). offset M-1 → 0 (TIGHT). ──
    lemma_repunit_zero(m);
    assert(pow_nat(m, 0) == 1);
    assert(c5.u == 5 * repunit_m((big_m - 2) as nat, m) + pow_nat(m, (big_m - 2) as nat) * 0)
        by(nonlinear_arith)
        requires c5.u == 5 * repunit_m((big_m - 2) as nat, m);
    lemma_run_walk_left(tm, c5, q_b, 5, (big_m - 2) as nat, 0, i_fives);
    lemma_pile_sym_shift(p_g, 5, (big_m - 1) as nat, m);
    assert(((big_m - 2) + 1) as nat == (big_m - 1) as nat);
    assert(((big_m - 1) + 1) as nat == big_m);
    let c6 = TmConfig { u: 0, v: pile_sym(p_g, 5, big_m, m), a: 0, q: q_b };
    assert(pile_sym(c5.v, 5, ((big_m - 2) + 1) as nat, m) == pile_sym(p_g, 5, big_m, m));
    assert(tm_run(tm, c5, ((big_m - 2) + 1) as nat) == c6);
    assert(tm_run(tm, c5, (big_m - 1) as nat) == c6);
    lemma_tm_run_split(tm, c0, (g + 2) as nat, (big_m - 1) as nat);
    assert((g + 2 + (big_m - 1)) as nat == (g + big_m + 1) as nat);
    assert(tm_run(tm, c0, (g + big_m + 1) as nat) == c6);
    // tail_safe S6 + chain. walk_fives companion: entry h = M-1 == len+1 == (M-2)+1 (TIGHT), end 0.
    lemma_run_walk_left_tail_safe(tm, c5, q_b, 5, (big_m - 2) as nat, 0, i_fives, (big_m - 1) as nat);
    assert(((big_m - 1) - ((big_m - 2) + 1)) as nat == 0);
    lemma_tail_chain(tm, c0, (g + 2) as nat, (big_m - 1) as nat, h0, (big_m - 1) as nat, 0);
    assert((g + 2 + (big_m - 1)) as nat == (g + big_m + 1) as nat);
}

/// **`mark_terminate` is tail-safe** for its `2g+2M+2` steps when the tail enters at `h = g+M+1`, and the
/// offset RETURNS to `g+M+1` (the head returns to the home pivot, net displacement 0). The forward half is
/// [`lemma_terminate_fwd_tail_safe`] (offset `H_0 → 0`); the return (S7–S12) is ALL R-moves, so it lifts
/// the offset `0 → H_0` unconditionally. Mirror of [`crate::tm_copy_refresh::lemma_mark_terminate`].
pub proof fn lemma_mark_terminate_tail_safe(
    tm: Tm, big_m: nat, g: nat, out: nat,
    q_home: nat, q_t: nat, q_a: nat, q_b: nat, q_turn: nat, q_turng: nat, q_ret: nat,
    i_peel: int, i_temp: int, i_t2g: int, i_gap: int, i_a2b: int, i_fives: int,
    i_turn: int, i_master: int, i_m2g: int, i_rgap: int, i_g2t: int, i_rtemp: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        2 <= big_m,
        g >= big_m + 2,
        0 <= i_peel < tm.quints.len(),
        0 <= i_temp < tm.quints.len(),
        0 <= i_t2g < tm.quints.len(),
        0 <= i_gap < tm.quints.len(),
        0 <= i_a2b < tm.quints.len(),
        0 <= i_fives < tm.quints.len(),
        0 <= i_turn < tm.quints.len(),
        0 <= i_master < tm.quints.len(),
        0 <= i_m2g < tm.quints.len(),
        0 <= i_rgap < tm.quints.len(),
        0 <= i_g2t < tm.quints.len(),
        0 <= i_rtemp < tm.quints.len(),
        tm.quints[i_peel] == mk_quint(q_home, 0, 0, q_t, Dir::L),
        tm.quints[i_temp] == mk_quint(q_t, 1, 1, q_t, Dir::L),
        tm.quints[i_t2g] == mk_quint(q_t, 0, 0, q_a, Dir::L),
        tm.quints[i_gap] == mk_quint(q_a, 0, 0, q_a, Dir::L),
        tm.quints[i_a2b] == mk_quint(q_a, 5, 5, q_b, Dir::L),
        tm.quints[i_fives] == mk_quint(q_b, 5, 5, q_b, Dir::L),
        tm.quints[i_turn] == mk_quint(q_b, 0, 0, q_turn, Dir::R),
        tm.quints[i_master] == mk_quint(q_turn, 5, 5, q_turn, Dir::R),
        tm.quints[i_m2g] == mk_quint(q_turn, 0, 0, q_turng, Dir::R),
        tm.quints[i_rgap] == mk_quint(q_turng, 0, 0, q_turng, Dir::R),
        tm.quints[i_g2t] == mk_quint(q_turng, 1, 1, q_ret, Dir::R),
        tm.quints[i_rtemp] == mk_quint(q_ret, 1, 1, q_ret, Dir::R),
    ensures
        tail_safe(tm, TmConfig { u: copy_u(big_m, big_m, g, tm.m), v: out, a: 0, q: q_home },
            (2 * g + 2 * big_m + 2) as nat, (g + big_m + 1) as nat),
        tail_end_h(tm, TmConfig { u: copy_u(big_m, big_m, g, tm.m), v: out, a: 0, q: q_home },
            (2 * g + 2 * big_m + 2) as nat, (g + big_m + 1) as nat) == (g + big_m + 1) as nat,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let h0 = (g + big_m + 1) as nat;
    let rm = repunit_m(big_m, m);
    let fives5 = (5 * rm) as nat;
    let p_t = pile_sym(out * m, 1, big_m, m);
    let p_g = (p_t * pow_nat(m, (g - big_m) as nat)) as nat;
    let big_pile = pile_sym(p_g, 5, big_m, m);
    let c0 = TmConfig { u: copy_u(big_m, big_m, g, m), v: out, a: 0, q: q_home };

    // ── FORWARD: c0 → c6 (blank above the all-fives master), g+M+1 steps. offset H_0 → 0. ──
    lemma_terminate_fwd(tm, big_m, g, out, q_home, q_t, q_a, q_b,
        i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives);
    lemma_terminate_fwd_tail_safe(tm, big_m, g, out, q_home, q_t, q_a, q_b,
        i_peel, i_temp, i_t2g, i_gap, i_a2b, i_fives);
    let c6 = TmConfig { u: 0, v: big_pile, a: 0, q: q_b };
    assert(tm_run(tm, c0, (g + big_m + 1) as nat) == c6);

    // ── S7: TURN (R) onto the master's high five. offset 0 → 1 (UNCONDITIONAL — the load-bearing step). ──
    lemma_pile_sym_div_mod(p_g, 5, big_m, m);
    assert(c6.v % m == 5);
    assert(c6.v / m == pile_sym(p_g, 5, (big_m - 1) as nat, m));
    assert(c6.u * m == 0) by(nonlinear_arith) requires c6.u == 0;
    lemma_tm_step_picks(tm, c6, i_turn);
    let c7 = apply_quint(tm.quints[i_turn], c6, m);
    assert(tm_step(tm, c6) == Some(c7));
    assert(c7.q == q_turn && c7.u == 0 && c7.a == 5 && c7.v == pile_sym(p_g, 5, (big_m - 1) as nat, m));
    assert(tm_run(tm, c7, 0) == c7);
    assert(tm_run(tm, c6, 1) == c7);
    lemma_tm_run_split(tm, c0, (g + big_m + 1) as nat, 1);
    assert(tm_run(tm, c0, (g + big_m + 2) as nat) == c7);
    assert(quint_matches(tm.quints[i_turn], c6));
    lemma_step_tail_safe(tm, c6, i_turn, 0);
    lemma_tail_chain(tm, c0, (g + big_m + 1) as nat, 1, h0, 0, 1);

    // ── S8: master-walk-right (M steps), PRESERVING 5s. offset 1 → 1+M. ──
    lemma_repunit_zero(m);
    assert(pow_nat(m, 0) == 1);
    assert(c7.u == 5 * repunit_m(0, m) + pow_nat(m, 0) * 0) by(nonlinear_arith)
        requires c7.u == 0, repunit_m(0, m) == 0, pow_nat(m, 0) == 1;
    lemma_run_walk_right(tm, c7, q_turn, 5, 0, (big_m - 1) as nat, p_g, 0, i_master);
    assert((0 + (big_m - 1) + 1) as nat == big_m);
    assert(5 * repunit_m(big_m, m) + pow_nat(m, big_m) * 0 == fives5) by(nonlinear_arith)
        requires fives5 == 5 * rm, rm == repunit_m(big_m, m);
    lemma_pow_nat_unfold(m, (g - big_m) as nat);
    assert(p_g == (p_t * pow_nat(m, (g - big_m - 1) as nat)) * m) by(nonlinear_arith)
        requires p_g == p_t * pow_nat(m, (g - big_m) as nat),
            pow_nat(m, (g - big_m) as nat) == m * pow_nat(m, (g - big_m - 1) as nat);
    lemma_div_mod_step(p_t * pow_nat(m, (g - big_m - 1) as nat), m, 0);
    let c8 = TmConfig { u: fives5, v: p_t * pow_nat(m, (g - big_m - 1) as nat), a: 0, q: q_turn };
    assert(tm_run(tm, c7, big_m) == c8);
    lemma_tm_run_split(tm, c0, (g + big_m + 2) as nat, big_m);
    assert((g + big_m + 2 + big_m) as nat == (g + 2 * big_m + 2) as nat);
    assert(tm_run(tm, c0, (g + 2 * big_m + 2) as nat) == c8);
    lemma_run_walk_right_tail_safe(tm, c7, q_turn, 5, 0, (big_m - 1) as nat, p_g, 0, i_master, 1);
    assert((1 + (big_m - 1)) as nat == big_m);
    lemma_tail_chain(tm, c0, (g + big_m + 2) as nat, big_m, h0, 1, (1 + big_m) as nat);

    // ── S9: m2g (R). offset 1+M → 2+M. ──
    lemma_pow_nat_unfold(m, (g - big_m - 1) as nat);
    assert(c8.v == (p_t * pow_nat(m, (g - big_m - 2) as nat)) * m) by(nonlinear_arith)
        requires c8.v == p_t * pow_nat(m, (g - big_m - 1) as nat),
            pow_nat(m, (g - big_m - 1) as nat) == m * pow_nat(m, (g - big_m - 2) as nat);
    lemma_div_mod_step(p_t * pow_nat(m, (g - big_m - 2) as nat), m, 0);
    lemma_tm_step_picks(tm, c8, i_m2g);
    let c9 = apply_quint(tm.quints[i_m2g], c8, m);
    assert(tm_step(tm, c8) == Some(c9));
    assert(c9.u == fives5 * m && c9.v == p_t * pow_nat(m, (g - big_m - 2) as nat) && c9.a == 0
        && c9.q == q_turng);
    assert(tm_run(tm, c9, 0) == c9);
    assert(tm_run(tm, c8, 1) == c9);
    lemma_tm_run_split(tm, c0, (g + 2 * big_m + 2) as nat, 1);
    assert(tm_run(tm, c0, (g + 2 * big_m + 3) as nat) == c9);
    assert(quint_matches(tm.quints[i_m2g], c8));
    lemma_step_tail_safe(tm, c8, i_m2g, (1 + big_m) as nat);
    lemma_tail_chain(tm, c0, (g + 2 * big_m + 2) as nat, 1, h0, (1 + big_m) as nat, (2 + big_m) as nat);

    // ── S10: gap-seek-right (g-M-1 steps). offset 2+M → g+1. ──
    lemma_pile_sym_div_mod(out * m, 1, big_m, m);
    assert(c9.v == pow_nat(m, (g - big_m - 2) as nat) * p_t) by(nonlinear_arith)
        requires c9.v == p_t * pow_nat(m, (g - big_m - 2) as nat);
    lemma_seek_right_blanks(tm, c9, q_turng, (g - big_m - 2) as nat, p_t, i_rgap);
    let c10 = TmConfig { u: c9.u * pow_nat(m, (g - big_m - 1) as nat),
        v: pile_sym(out * m, 1, (big_m - 1) as nat, m), a: 1, q: q_turng };
    assert(((g - big_m - 2) + 1) as nat == (g - big_m - 1) as nat);
    assert(tm_run(tm, c9, (g - big_m - 1) as nat) == c10);
    lemma_tm_run_split(tm, c0, (g + 2 * big_m + 3) as nat, (g - big_m - 1) as nat);
    assert((g + 2 * big_m + 3 + (g - big_m - 1)) as nat == (2 * g + big_m + 2) as nat);
    assert(tm_run(tm, c0, (2 * g + big_m + 2) as nat) == c10);
    assert(c10.u == fives5 * pow_nat(m, (g - big_m) as nat)) by(nonlinear_arith)
        requires c10.u == (fives5 * m) * pow_nat(m, (g - big_m - 1) as nat),
            pow_nat(m, (g - big_m) as nat) == m * pow_nat(m, (g - big_m - 1) as nat);
    lemma_seek_right_tail_safe(tm, c9, q_turng, (g - big_m - 2) as nat, p_t, i_rgap, (2 + big_m) as nat);
    assert((2 + big_m + (g - big_m - 1)) as nat == (g + 1) as nat);
    lemma_tail_chain(tm, c0, (g + 2 * big_m + 3) as nat, (g - big_m - 1) as nat, h0, (2 + big_m) as nat,
        (g + 1) as nat);

    // ── S11: g2t (R). offset g+1 → g+2. ──
    lemma_pile_sym_div_mod(out * m, 1, (big_m - 1) as nat, m);
    lemma_tm_step_picks(tm, c10, i_g2t);
    let c11 = apply_quint(tm.quints[i_g2t], c10, m);
    assert(tm_step(tm, c10) == Some(c11));
    assert(c11.u == c10.u * m + 1 && c11.v == pile_sym(out * m, 1, (big_m - 2) as nat, m) && c11.a == 1
        && c11.q == q_ret);
    assert(tm_run(tm, c11, 0) == c11);
    assert(tm_run(tm, c10, 1) == c11);
    lemma_tm_run_split(tm, c0, (2 * g + big_m + 2) as nat, 1);
    assert(tm_run(tm, c0, (2 * g + big_m + 3) as nat) == c11);
    assert(quint_matches(tm.quints[i_g2t], c10));
    lemma_step_tail_safe(tm, c10, i_g2t, (g + 1) as nat);
    lemma_tail_chain(tm, c0, (2 * g + big_m + 2) as nat, 1, h0, (g + 1) as nat, (g + 2) as nat);

    // ── S12: temp-walk-right (M-1 steps). offset g+2 → g+M+1 == H_0. ──
    assert(pow_nat(m, 1) == m) by { lemma_pow_nat_unfold(m, 1); assert(pow_nat(m, 0) == 1); }
    assert(repunit_m(1, m) == 1) by { lemma_repunit_step(0, m); lemma_repunit_zero(m); }
    assert(c11.u == 1 * repunit_m(1, m) + pow_nat(m, 1) * (fives5 * pow_nat(m, (g - big_m) as nat)))
        by(nonlinear_arith)
        requires c11.u == (fives5 * pow_nat(m, (g - big_m) as nat)) * m + 1, repunit_m(1, m) == 1,
            pow_nat(m, 1) == m;
    lemma_run_walk_right(tm, c11, q_ret, 1, 1, (big_m - 2) as nat, out * m,
        (fives5 * pow_nat(m, (g - big_m) as nat)) as nat, i_rtemp);
    assert((1 + (big_m - 2) + 1) as nat == big_m);
    lemma_div_mod_step(out, m, 0);
    let c12 = TmConfig {
        u: repunit_m(big_m, m) + pow_nat(m, big_m) * (fives5 * pow_nat(m, (g - big_m) as nat)),
        v: out, a: 0, q: q_ret };
    assert(tm_run(tm, c11, (big_m - 1) as nat) == c12);
    lemma_tm_run_split(tm, c0, (2 * g + big_m + 3) as nat, (big_m - 1) as nat);
    assert((2 * g + big_m + 3 + (big_m - 1)) as nat == (2 * g + 2 * big_m + 2) as nat);
    assert(tm_run(tm, c0, (2 * g + 2 * big_m + 2) as nat) == c12);
    lemma_run_walk_right_tail_safe(tm, c11, q_ret, 1, 1, (big_m - 2) as nat, out * m,
        (fives5 * pow_nat(m, (g - big_m) as nat)) as nat, i_rtemp, (g + 2) as nat);
    assert((g + 2 + (big_m - 1)) as nat == (g + big_m + 1) as nat);
    lemma_tail_chain(tm, c0, (2 * g + big_m + 3) as nat, (big_m - 1) as nat, h0, (g + 2) as nat,
        (g + big_m + 1) as nat);
}

/// **`unmark_fwd` is tail-safe** for its `g+M+1` steps, offset `H_0 → 0`. Structural twin of
/// [`lemma_terminate_fwd_tail_safe`]: S1–S4 identical, S5/S6 convert `5→1` (still L-moves) via the
/// `unmark_fives_left` companion. Mirror of [`crate::tm_copy_refresh::lemma_unmark_fwd`].
pub proof fn lemma_unmark_fwd_tail_safe(
    tm: Tm, big_m: nat, g: nat, out: nat,
    q_uh: nat, q_ut: nat, q_ua: nat, q_uf: nat,
    i_peel: int, i_temp: int, i_t2g: int, i_gap: int, i_u1: int, i_urest: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        2 <= big_m,
        g >= big_m + 2,
        0 <= i_peel < tm.quints.len(),
        0 <= i_temp < tm.quints.len(),
        0 <= i_t2g < tm.quints.len(),
        0 <= i_gap < tm.quints.len(),
        0 <= i_u1 < tm.quints.len(),
        0 <= i_urest < tm.quints.len(),
        tm.quints[i_peel] == mk_quint(q_uh, 0, 0, q_ut, Dir::L),
        tm.quints[i_temp] == mk_quint(q_ut, 1, 1, q_ut, Dir::L),
        tm.quints[i_t2g] == mk_quint(q_ut, 0, 0, q_ua, Dir::L),
        tm.quints[i_gap] == mk_quint(q_ua, 0, 0, q_ua, Dir::L),
        tm.quints[i_u1] == mk_quint(q_ua, 5, 1, q_uf, Dir::L),
        tm.quints[i_urest] == mk_quint(q_uf, 5, 1, q_uf, Dir::L),
    ensures
        tail_safe(tm, TmConfig { u: copy_u(big_m, big_m, g, tm.m), v: out, a: 0, q: q_uh },
            (g + big_m + 1) as nat, (g + big_m + 1) as nat),
        tail_end_h(tm, TmConfig { u: copy_u(big_m, big_m, g, tm.m), v: out, a: 0, q: q_uh },
            (g + big_m + 1) as nat, (g + big_m + 1) as nat) == 0,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let h0 = (g + big_m + 1) as nat;
    let rm = repunit_m(big_m, m);
    let fives = (5 * rm) as nat;
    lemma_copy_u_end(big_m, g, m);
    assert(copy_u(big_m, big_m, g, m) == rm + pow_nat(m, g) * fives) by(nonlinear_arith)
        requires copy_u(big_m, big_m, g, m) == rm + pow_nat(m, g) * (5 * rm), fives == 5 * rm;
    let c0 = TmConfig { u: copy_u(big_m, big_m, g, m), v: out, a: 0, q: q_uh };
    assert(c0.u == rm + pow_nat(m, g) * fives);

    // ── S1: pivot-peel (L). offset h0 → g+M. ──
    lemma_repunit_step((big_m - 1) as nat, m);
    assert(((big_m - 1) + 1) as nat == big_m);
    lemma_pow_nat_unfold(m, g);
    let u1 = repunit_m((big_m - 1) as nat, m) + pow_nat(m, (g - 1) as nat) * fives;
    assert(c0.u == u1 * m + 1) by(nonlinear_arith)
        requires
            c0.u == rm + pow_nat(m, g) * fives,
            rm == m * repunit_m((big_m - 1) as nat, m) + 1,
            pow_nat(m, g) == m * pow_nat(m, (g - 1) as nat),
            u1 == repunit_m((big_m - 1) as nat, m) + pow_nat(m, (g - 1) as nat) * fives;
    lemma_div_mod_step(u1, m, 1);
    lemma_tm_step_picks(tm, c0, i_peel);
    let c1 = apply_quint(tm.quints[i_peel], c0, m);
    assert(tm_step(tm, c0) == Some(c1));
    assert(c1.u == u1 && c1.v == out * m && c1.a == 1 && c1.q == q_ut);
    assert(tm_run(tm, c1, 0) == c1);
    assert(tm_run(tm, c0, 1) == c1);
    assert(quint_matches(tm.quints[i_peel], c0));
    lemma_step_tail_safe(tm, c0, i_peel, h0);

    // ── S2: walk-left over temp (M steps). offset g+M → g. ──
    let w_a = (pow_nat(m, (g - big_m) as nat) * fives) as nat;
    lemma_pow_nat_add(m, (big_m - 1) as nat, (g - big_m) as nat);
    assert(((big_m - 1) + (g - big_m)) as nat == (g - 1) as nat);
    assert(c1.u == repunit_m((big_m - 1) as nat, m) + pow_nat(m, (big_m - 1) as nat) * w_a)
        by(nonlinear_arith)
        requires
            c1.u == repunit_m((big_m - 1) as nat, m) + pow_nat(m, (g - 1) as nat) * fives,
            pow_nat(m, (g - 1) as nat) == pow_nat(m, (big_m - 1) as nat) * pow_nat(m, (g - big_m) as nat),
            w_a == pow_nat(m, (g - big_m) as nat) * fives;
    lemma_run_walk_left(tm, c1, q_ut, 1, (big_m - 1) as nat, w_a, i_temp);
    lemma_pow_nat_unfold(m, (g - big_m) as nat);
    assert(w_a == (pow_nat(m, (g - big_m - 1) as nat) * fives) * m) by(nonlinear_arith)
        requires w_a == pow_nat(m, (g - big_m) as nat) * fives,
            pow_nat(m, (g - big_m) as nat) == m * pow_nat(m, (g - big_m - 1) as nat);
    lemma_div_mod_step(pow_nat(m, (g - big_m - 1) as nat) * fives, m, 0);
    let p_t = pile_sym(out * m, 1, big_m, m);
    let c2 = TmConfig { u: pow_nat(m, (g - big_m - 1) as nat) * fives, v: p_t, a: 0, q: q_ut };
    assert(((big_m - 1) + 1) as nat == big_m);
    assert(tm_run(tm, c1, big_m) == c2);
    lemma_tm_run_split(tm, c0, 1, big_m);
    assert(tm_run(tm, c0, (1 + big_m) as nat) == c2);
    lemma_run_walk_left_tail_safe(tm, c1, q_ut, 1, (big_m - 1) as nat, w_a, i_temp, (g + big_m) as nat);
    lemma_tail_chain(tm, c0, 1, big_m, h0, (g + big_m) as nat, g);

    // ── S3: temp→gap (L). offset g → g-1. ──
    lemma_pow_nat_unfold(m, (g - big_m - 1) as nat);
    assert(c2.u == (pow_nat(m, (g - big_m - 2) as nat) * fives) * m) by(nonlinear_arith)
        requires c2.u == pow_nat(m, (g - big_m - 1) as nat) * fives,
            pow_nat(m, (g - big_m - 1) as nat) == m * pow_nat(m, (g - big_m - 2) as nat);
    lemma_div_mod_step(pow_nat(m, (g - big_m - 2) as nat) * fives, m, 0);
    lemma_tm_step_picks(tm, c2, i_t2g);
    let c3 = apply_quint(tm.quints[i_t2g], c2, m);
    assert(tm_step(tm, c2) == Some(c3));
    assert(c3.u == pow_nat(m, (g - big_m - 2) as nat) * fives && c3.v == p_t * m && c3.a == 0
        && c3.q == q_ua);
    assert(tm_run(tm, c3, 0) == c3);
    assert(tm_run(tm, c2, 1) == c3);
    lemma_tm_run_split(tm, c0, (1 + big_m) as nat, 1);
    assert(tm_run(tm, c0, (1 + big_m + 1) as nat) == c3);
    assert(quint_matches(tm.quints[i_t2g], c2));
    lemma_step_tail_safe(tm, c2, i_t2g, g);
    lemma_tail_chain(tm, c0, (1 + big_m) as nat, 1, h0, g, (g - 1) as nat);

    // ── S4: seek-left over the remaining gap (g-M-1 steps). offset g-1 → M. ──
    lemma_div_mod_step((5 * repunit_m((big_m - 1) as nat, m)) as nat, m, 5);
    assert(fives == (5 * repunit_m((big_m - 1) as nat, m)) * m + 5) by(nonlinear_arith)
        requires fives == 5 * rm, rm == m * repunit_m((big_m - 1) as nat, m) + 1;
    assert(fives % m == 5) by {
        lemma_div_mod_step((5 * repunit_m((big_m - 1) as nat, m)) as nat, m, 5);
        assert(fives == (5 * repunit_m((big_m - 1) as nat, m)) * m + 5);
    }
    assert(fives % m != 0);
    lemma_seek_left_blanks(tm, c3, q_ua, (g - big_m - 2) as nat, fives, i_gap);
    let p_g = (p_t * pow_nat(m, (g - big_m) as nat)) as nat;
    let c4 = TmConfig { u: fives / m, v: (p_t * m) * pow_nat(m, (g - big_m - 1) as nat), a: 5, q: q_ua };
    assert(((g - big_m - 2) + 1) as nat == (g - big_m - 1) as nat);
    assert(tm_run(tm, c3, (g - big_m - 1) as nat) == c4);
    lemma_tm_run_split(tm, c0, (1 + big_m + 1) as nat, (g - big_m - 1) as nat);
    assert((1 + big_m + 1 + (g - big_m - 1)) as nat == (g + 1) as nat);
    assert(tm_run(tm, c0, (g + 1) as nat) == c4);
    assert((p_t * m) * pow_nat(m, (g - big_m - 1) as nat) == p_g) by(nonlinear_arith)
        requires p_g == p_t * pow_nat(m, (g - big_m) as nat),
            pow_nat(m, (g - big_m) as nat) == m * pow_nat(m, (g - big_m - 1) as nat);
    assert(fives / m == 5 * repunit_m((big_m - 1) as nat, m)) by {
        lemma_div_mod_step((5 * repunit_m((big_m - 1) as nat, m)) as nat, m, 5);
        assert(fives == (5 * repunit_m((big_m - 1) as nat, m)) * m + 5);
    }
    lemma_seek_left_tail_safe(tm, c3, q_ua, (g - big_m - 2) as nat, fives, i_gap, (g - 1) as nat);
    assert(((g - 1) - (g - big_m - 1)) as nat == big_m);
    lemma_tail_chain(tm, c0, (1 + big_m + 1) as nat, (g - big_m - 1) as nat, h0, (g - 1) as nat, big_m);

    // ── S5: unmark-first (q_ua,5,1,q_uf,L). offset M → M-1. ──
    lemma_repunit_step((big_m - 2) as nat, m);
    assert(((big_m - 2) + 1) as nat == (big_m - 1) as nat);
    let c4u_div = (5 * repunit_m((big_m - 2) as nat, m)) as nat;
    assert(c4.u == c4u_div * m + 5) by(nonlinear_arith)
        requires c4.u == 5 * repunit_m((big_m - 1) as nat, m),
            repunit_m((big_m - 1) as nat, m) == m * repunit_m((big_m - 2) as nat, m) + 1,
            c4u_div == 5 * repunit_m((big_m - 2) as nat, m);
    lemma_div_mod_step(c4u_div, m, 5);
    lemma_tm_step_picks(tm, c4, i_u1);
    let c5 = apply_quint(tm.quints[i_u1], c4, m);
    assert(tm_step(tm, c4) == Some(c5));
    assert(c5.u == c4u_div && c5.v == p_g * m + 1 && c5.a == 5 && c5.q == q_uf);
    assert(tm_run(tm, c5, 0) == c5);
    assert(tm_run(tm, c4, 1) == c5);
    lemma_tm_run_split(tm, c0, (g + 1) as nat, 1);
    assert(tm_run(tm, c0, (g + 2) as nat) == c5);
    assert(quint_matches(tm.quints[i_u1], c4));
    lemma_step_tail_safe(tm, c4, i_u1, big_m);
    lemma_tail_chain(tm, c0, (g + 1) as nat, 1, h0, big_m, (big_m - 1) as nat);

    // ── S6: unmark-rest (q_uf,5,1,q_uf,L), M-1 fives. offset M-1 → 0 (TIGHT). ──
    lemma_repunit_zero(m);
    assert(pow_nat(m, 0) == 1);
    assert(c5.u == 5 * repunit_m((big_m - 2) as nat, m) + pow_nat(m, (big_m - 2) as nat) * 0)
        by(nonlinear_arith)
        requires c5.u == 5 * repunit_m((big_m - 2) as nat, m);
    lemma_unmark_fives_left(tm, c5, q_uf, (big_m - 2) as nat, 0, i_urest);
    lemma_pile_sym_shift(p_g, 1, (big_m - 1) as nat, m);
    assert(((big_m - 2) + 1) as nat == (big_m - 1) as nat);
    assert(((big_m - 1) + 1) as nat == big_m);
    let c6 = TmConfig { u: 0, v: pile_sym(p_g, 1, big_m, m), a: 0, q: q_uf };
    assert(tm_run(tm, c5, (big_m - 1) as nat) == c6);
    lemma_tm_run_split(tm, c0, (g + 2) as nat, (big_m - 1) as nat);
    assert((g + 2 + (big_m - 1)) as nat == (g + big_m + 1) as nat);
    assert(tm_run(tm, c0, (g + big_m + 1) as nat) == c6);
    lemma_unmark_fives_left_tail_safe(tm, c5, q_uf, (big_m - 2) as nat, 0, i_urest, (big_m - 1) as nat);
    assert(((big_m - 1) - ((big_m - 2) + 1)) as nat == 0);
    lemma_tail_chain(tm, c0, (g + 2) as nat, (big_m - 1) as nat, h0, (big_m - 1) as nat, 0);
    assert((g + 2 + (big_m - 1)) as nat == (g + big_m + 1) as nat);
}

/// **`unmark` is tail-safe** for its `2g+2M+2` steps, offset returning to `H_0` (net displacement 0).
/// Forward = [`lemma_unmark_fwd_tail_safe`] (`H_0 → 0`); the all-R return (S7–S12, master-walk now over
/// `1`s) lifts `0 → H_0`. Mirror of [`crate::tm_copy_refresh::lemma_unmark`].
pub proof fn lemma_unmark_tail_safe(
    tm: Tm, big_m: nat, g: nat, out: nat,
    q_uh: nat, q_ut: nat, q_ua: nat, q_uf: nat, q_ur: nat, q_urg: nat, q_urt: nat,
    i_peel: int, i_temp: int, i_t2g: int, i_gap: int, i_u1: int, i_urest: int,
    i_turn: int, i_master: int, i_m2g: int, i_rgap: int, i_g2t: int, i_rtemp: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        2 <= big_m,
        g >= big_m + 2,
        0 <= i_peel < tm.quints.len(),
        0 <= i_temp < tm.quints.len(),
        0 <= i_t2g < tm.quints.len(),
        0 <= i_gap < tm.quints.len(),
        0 <= i_u1 < tm.quints.len(),
        0 <= i_urest < tm.quints.len(),
        0 <= i_turn < tm.quints.len(),
        0 <= i_master < tm.quints.len(),
        0 <= i_m2g < tm.quints.len(),
        0 <= i_rgap < tm.quints.len(),
        0 <= i_g2t < tm.quints.len(),
        0 <= i_rtemp < tm.quints.len(),
        tm.quints[i_peel] == mk_quint(q_uh, 0, 0, q_ut, Dir::L),
        tm.quints[i_temp] == mk_quint(q_ut, 1, 1, q_ut, Dir::L),
        tm.quints[i_t2g] == mk_quint(q_ut, 0, 0, q_ua, Dir::L),
        tm.quints[i_gap] == mk_quint(q_ua, 0, 0, q_ua, Dir::L),
        tm.quints[i_u1] == mk_quint(q_ua, 5, 1, q_uf, Dir::L),
        tm.quints[i_urest] == mk_quint(q_uf, 5, 1, q_uf, Dir::L),
        tm.quints[i_turn] == mk_quint(q_uf, 0, 0, q_ur, Dir::R),
        tm.quints[i_master] == mk_quint(q_ur, 1, 1, q_ur, Dir::R),
        tm.quints[i_m2g] == mk_quint(q_ur, 0, 0, q_urg, Dir::R),
        tm.quints[i_rgap] == mk_quint(q_urg, 0, 0, q_urg, Dir::R),
        tm.quints[i_g2t] == mk_quint(q_urg, 1, 1, q_urt, Dir::R),
        tm.quints[i_rtemp] == mk_quint(q_urt, 1, 1, q_urt, Dir::R),
    ensures
        tail_safe(tm, TmConfig { u: copy_u(big_m, big_m, g, tm.m), v: out, a: 0, q: q_uh },
            (2 * g + 2 * big_m + 2) as nat, (g + big_m + 1) as nat),
        tail_end_h(tm, TmConfig { u: copy_u(big_m, big_m, g, tm.m), v: out, a: 0, q: q_uh },
            (2 * g + 2 * big_m + 2) as nat, (g + big_m + 1) as nat) == (g + big_m + 1) as nat,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let h0 = (g + big_m + 1) as nat;
    let rm = repunit_m(big_m, m);
    let p_t = pile_sym(out * m, 1, big_m, m);
    let p_g = (p_t * pow_nat(m, (g - big_m) as nat)) as nat;
    let big_pile = pile_sym(p_g, 1, big_m, m);
    let c0 = TmConfig { u: copy_u(big_m, big_m, g, m), v: out, a: 0, q: q_uh };

    // ── FORWARD: c0 → c6, g+M+1 steps. offset H_0 → 0. ──
    lemma_unmark_fwd(tm, big_m, g, out, q_uh, q_ut, q_ua, q_uf,
        i_peel, i_temp, i_t2g, i_gap, i_u1, i_urest);
    lemma_unmark_fwd_tail_safe(tm, big_m, g, out, q_uh, q_ut, q_ua, q_uf,
        i_peel, i_temp, i_t2g, i_gap, i_u1, i_urest);
    let c6 = TmConfig { u: 0, v: big_pile, a: 0, q: q_uf };
    assert(tm_run(tm, c0, (g + big_m + 1) as nat) == c6);

    // ── S7: TURN (R) onto the master's high one. offset 0 → 1 (unconditional). ──
    lemma_pile_sym_div_mod(p_g, 1, big_m, m);
    assert(c6.v % m == 1);
    assert(c6.v / m == pile_sym(p_g, 1, (big_m - 1) as nat, m));
    assert(c6.u * m == 0) by(nonlinear_arith) requires c6.u == 0;
    lemma_tm_step_picks(tm, c6, i_turn);
    let c7 = apply_quint(tm.quints[i_turn], c6, m);
    assert(tm_step(tm, c6) == Some(c7));
    assert(c7.q == q_ur && c7.u == 0 && c7.a == 1 && c7.v == pile_sym(p_g, 1, (big_m - 1) as nat, m));
    assert(tm_run(tm, c7, 0) == c7);
    assert(tm_run(tm, c6, 1) == c7);
    lemma_tm_run_split(tm, c0, (g + big_m + 1) as nat, 1);
    assert(tm_run(tm, c0, (g + big_m + 2) as nat) == c7);
    assert(quint_matches(tm.quints[i_turn], c6));
    lemma_step_tail_safe(tm, c6, i_turn, 0);
    lemma_tail_chain(tm, c0, (g + big_m + 1) as nat, 1, h0, 0, 1);

    // ── S8: master-walk-right over M ones. offset 1 → 1+M. ──
    lemma_repunit_zero(m);
    assert(pow_nat(m, 0) == 1);
    assert(c7.u == 1 * repunit_m(0, m) + pow_nat(m, 0) * 0) by(nonlinear_arith)
        requires c7.u == 0, repunit_m(0, m) == 0, pow_nat(m, 0) == 1;
    lemma_run_walk_right(tm, c7, q_ur, 1, 0, (big_m - 1) as nat, p_g, 0, i_master);
    assert((0 + (big_m - 1) + 1) as nat == big_m);
    assert(1 * repunit_m(big_m, m) + pow_nat(m, big_m) * 0 == rm) by(nonlinear_arith)
        requires rm == repunit_m(big_m, m);
    lemma_pow_nat_unfold(m, (g - big_m) as nat);
    assert(p_g == (p_t * pow_nat(m, (g - big_m - 1) as nat)) * m) by(nonlinear_arith)
        requires p_g == p_t * pow_nat(m, (g - big_m) as nat),
            pow_nat(m, (g - big_m) as nat) == m * pow_nat(m, (g - big_m - 1) as nat);
    lemma_div_mod_step(p_t * pow_nat(m, (g - big_m - 1) as nat), m, 0);
    let c8 = TmConfig { u: rm, v: p_t * pow_nat(m, (g - big_m - 1) as nat), a: 0, q: q_ur };
    assert(tm_run(tm, c7, big_m) == c8);
    lemma_tm_run_split(tm, c0, (g + big_m + 2) as nat, big_m);
    assert((g + big_m + 2 + big_m) as nat == (g + 2 * big_m + 2) as nat);
    assert(tm_run(tm, c0, (g + 2 * big_m + 2) as nat) == c8);
    lemma_run_walk_right_tail_safe(tm, c7, q_ur, 1, 0, (big_m - 1) as nat, p_g, 0, i_master, 1);
    assert((1 + (big_m - 1)) as nat == big_m);
    lemma_tail_chain(tm, c0, (g + big_m + 2) as nat, big_m, h0, 1, (1 + big_m) as nat);

    // ── S9: m2g (R). offset 1+M → 2+M. ──
    lemma_pow_nat_unfold(m, (g - big_m - 1) as nat);
    assert(c8.v == (p_t * pow_nat(m, (g - big_m - 2) as nat)) * m) by(nonlinear_arith)
        requires c8.v == p_t * pow_nat(m, (g - big_m - 1) as nat),
            pow_nat(m, (g - big_m - 1) as nat) == m * pow_nat(m, (g - big_m - 2) as nat);
    lemma_div_mod_step(p_t * pow_nat(m, (g - big_m - 2) as nat), m, 0);
    lemma_tm_step_picks(tm, c8, i_m2g);
    let c9 = apply_quint(tm.quints[i_m2g], c8, m);
    assert(tm_step(tm, c8) == Some(c9));
    assert(c9.u == rm * m && c9.v == p_t * pow_nat(m, (g - big_m - 2) as nat) && c9.a == 0
        && c9.q == q_urg);
    assert(tm_run(tm, c9, 0) == c9);
    assert(tm_run(tm, c8, 1) == c9);
    lemma_tm_run_split(tm, c0, (g + 2 * big_m + 2) as nat, 1);
    assert(tm_run(tm, c0, (g + 2 * big_m + 3) as nat) == c9);
    assert(quint_matches(tm.quints[i_m2g], c8));
    lemma_step_tail_safe(tm, c8, i_m2g, (1 + big_m) as nat);
    lemma_tail_chain(tm, c0, (g + 2 * big_m + 2) as nat, 1, h0, (1 + big_m) as nat, (2 + big_m) as nat);

    // ── S10: gap-seek-right (g-M-1 steps). offset 2+M → g+1. ──
    lemma_pile_sym_div_mod(out * m, 1, big_m, m);
    assert(c9.v == pow_nat(m, (g - big_m - 2) as nat) * p_t) by(nonlinear_arith)
        requires c9.v == p_t * pow_nat(m, (g - big_m - 2) as nat);
    lemma_seek_right_blanks(tm, c9, q_urg, (g - big_m - 2) as nat, p_t, i_rgap);
    let c10 = TmConfig { u: c9.u * pow_nat(m, (g - big_m - 1) as nat),
        v: pile_sym(out * m, 1, (big_m - 1) as nat, m), a: 1, q: q_urg };
    assert(((g - big_m - 2) + 1) as nat == (g - big_m - 1) as nat);
    assert(tm_run(tm, c9, (g - big_m - 1) as nat) == c10);
    lemma_tm_run_split(tm, c0, (g + 2 * big_m + 3) as nat, (g - big_m - 1) as nat);
    assert((g + 2 * big_m + 3 + (g - big_m - 1)) as nat == (2 * g + big_m + 2) as nat);
    assert(tm_run(tm, c0, (2 * g + big_m + 2) as nat) == c10);
    assert(c10.u == rm * pow_nat(m, (g - big_m) as nat)) by(nonlinear_arith)
        requires c10.u == (rm * m) * pow_nat(m, (g - big_m - 1) as nat),
            pow_nat(m, (g - big_m) as nat) == m * pow_nat(m, (g - big_m - 1) as nat);
    lemma_seek_right_tail_safe(tm, c9, q_urg, (g - big_m - 2) as nat, p_t, i_rgap, (2 + big_m) as nat);
    assert((2 + big_m + (g - big_m - 1)) as nat == (g + 1) as nat);
    lemma_tail_chain(tm, c0, (g + 2 * big_m + 3) as nat, (g - big_m - 1) as nat, h0, (2 + big_m) as nat,
        (g + 1) as nat);

    // ── S11: g2t (R). offset g+1 → g+2. ──
    lemma_pile_sym_div_mod(out * m, 1, (big_m - 1) as nat, m);
    lemma_tm_step_picks(tm, c10, i_g2t);
    let c11 = apply_quint(tm.quints[i_g2t], c10, m);
    assert(tm_step(tm, c10) == Some(c11));
    assert(c11.u == c10.u * m + 1 && c11.v == pile_sym(out * m, 1, (big_m - 2) as nat, m) && c11.a == 1
        && c11.q == q_urt);
    assert(tm_run(tm, c11, 0) == c11);
    assert(tm_run(tm, c10, 1) == c11);
    lemma_tm_run_split(tm, c0, (2 * g + big_m + 2) as nat, 1);
    assert(tm_run(tm, c0, (2 * g + big_m + 3) as nat) == c11);
    assert(quint_matches(tm.quints[i_g2t], c10));
    lemma_step_tail_safe(tm, c10, i_g2t, (g + 1) as nat);
    lemma_tail_chain(tm, c0, (2 * g + big_m + 2) as nat, 1, h0, (g + 1) as nat, (g + 2) as nat);

    // ── S12: temp-walk-right (M-1 steps). offset g+2 → H_0. ──
    assert(pow_nat(m, 1) == m) by { lemma_pow_nat_unfold(m, 1); assert(pow_nat(m, 0) == 1); }
    assert(repunit_m(1, m) == 1) by { lemma_repunit_step(0, m); lemma_repunit_zero(m); }
    assert(c11.u == 1 * repunit_m(1, m) + pow_nat(m, 1) * (rm * pow_nat(m, (g - big_m) as nat)))
        by(nonlinear_arith)
        requires c11.u == (rm * pow_nat(m, (g - big_m) as nat)) * m + 1, repunit_m(1, m) == 1,
            pow_nat(m, 1) == m;
    lemma_run_walk_right(tm, c11, q_urt, 1, 1, (big_m - 2) as nat, out * m,
        (rm * pow_nat(m, (g - big_m) as nat)) as nat, i_rtemp);
    assert((1 + (big_m - 2) + 1) as nat == big_m);
    lemma_div_mod_step(out, m, 0);
    let c12 = TmConfig {
        u: repunit_m(big_m, m) + pow_nat(m, big_m) * (rm * pow_nat(m, (g - big_m) as nat)),
        v: out, a: 0, q: q_urt };
    assert(tm_run(tm, c11, (big_m - 1) as nat) == c12);
    lemma_tm_run_split(tm, c0, (2 * g + big_m + 3) as nat, (big_m - 1) as nat);
    assert((2 * g + big_m + 3 + (big_m - 1)) as nat == (2 * g + 2 * big_m + 2) as nat);
    assert(tm_run(tm, c0, (2 * g + 2 * big_m + 2) as nat) == c12);
    lemma_run_walk_right_tail_safe(tm, c11, q_urt, 1, 1, (big_m - 2) as nat, out * m,
        (rm * pow_nat(m, (g - big_m) as nat)) as nat, i_rtemp, (g + 2) as nat);
    assert((g + 2 + (big_m - 1)) as nat == (g + big_m + 1) as nat);
    lemma_tail_chain(tm, c0, (2 * g + big_m + 3) as nat, (big_m - 1) as nat, h0, (g + 2) as nat,
        (g + big_m + 1) as nat);
}

} // verus!
