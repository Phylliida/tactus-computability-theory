//! # GAP-2 G2-F — tail-safety of `copy_refresh`'s `M = 1` path (`g ≥ 3`)
//!
//! The `M = 1` analog of [`crate::gap2_tail_phase1`]. `copy_refresh_m1` is the shallow specialisation
//! used when the master is a single repunit (`b = 0` ⟹ `M = b+1 = 1`); the per-`M-1` sub-walks vanish.
//! Three phases at the constant home offset `H_0 = g + 2 = g + M + 1`, each net-displacement-0:
//!   - PHASE 1 — single `copy_iter_j0` (reuses [`crate::gap2_tail_phase1::lemma_copy_iter_j0_tail_safe`]
//!     at `big_m = 1`),
//!   - PHASE 2 — [`lemma_mark_terminate_m1_tail_safe`] (single master five crossed, no fives-walk),
//!   - PHASE 3 — [`lemma_unmark_m1_tail_safe`] (single five → one, no temp-walk-back).
//!
//! Both phase-2/3 companions share an identical offset skeleton: 5 L-moves drive the offset
//! `H_0 → 0` (the head ends one blank above the single master five — the tightest point), then 5 R-moves
//! lift it back `0 → H_0`. Mirror-and-chain of the source gadgets; only the per-step direction and the
//! tail offset are tracked. Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use crate::tm::{Tm, TmConfig, tm_wf, tm_run, tm_step, apply_quint, quint_matches};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};
use crate::tm_two_counter::{repunit_m, lemma_repunit_zero, lemma_repunit_step};
use crate::tm_dstring::{pow_nat, lemma_pow_nat_unfold};
use crate::tm_copy_refresh::{copy_u, lemma_copy_u_end,
    lemma_run_walk_left, lemma_seek_left_blanks, lemma_run_walk_right, lemma_seek_right_blanks,
    lemma_pile_sym_div_mod, lemma_copy_iter_j0, lemma_mark_terminate_m1, lemma_unmark_m1};
use crate::tm_emit::pile_sym;
use crate::tm_run_lemmas::{lemma_tm_run_split};
use verus_group_theory::word_numbering::lemma_div_mod_step;
use crate::gap2_tail_lift::{tail_safe, tail_end_h, lemma_step_tail_safe, lemma_tail_chain};
use crate::gap2_tail_walks::{lemma_seek_left_tail_safe, lemma_run_walk_left_tail_safe,
    lemma_seek_right_tail_safe, lemma_run_walk_right_tail_safe};
use crate::gap2_tail_phase1::lemma_copy_iter_j0_tail_safe;

verus! {

/// **`mark_terminate_m1` is tail-safe** for its `2g+4` steps, offset returning to `H_0 = g+2` (net
/// displacement 0). The forward five L-moves (peel, temp-walk, t2g, gap-seek, a2b) drive the offset to
/// exactly `0`; the return five R-moves (turn, master-walk, m2g, gap-seek, g2t) lift it back. Mirror of
/// [`crate::tm_copy_refresh::lemma_mark_terminate_m1`].
pub proof fn lemma_mark_terminate_m1_tail_safe(
    tm: Tm, g: nat, out: nat,
    q_home: nat, q_t: nat, q_a: nat, q_b: nat, q_turn: nat, q_turng: nat, q_ret: nat,
    i_peel: int, i_temp: int, i_t2g: int, i_gap: int, i_a2b: int,
    i_turn: int, i_master: int, i_m2g: int, i_rgap: int, i_g2t: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        g >= 3,
        0 <= i_peel < tm.quints.len(),
        0 <= i_temp < tm.quints.len(),
        0 <= i_t2g < tm.quints.len(),
        0 <= i_gap < tm.quints.len(),
        0 <= i_a2b < tm.quints.len(),
        0 <= i_turn < tm.quints.len(),
        0 <= i_master < tm.quints.len(),
        0 <= i_m2g < tm.quints.len(),
        0 <= i_rgap < tm.quints.len(),
        0 <= i_g2t < tm.quints.len(),
        tm.quints[i_peel] == mk_quint(q_home, 0, 0, q_t, Dir::L),
        tm.quints[i_temp] == mk_quint(q_t, 1, 1, q_t, Dir::L),
        tm.quints[i_t2g] == mk_quint(q_t, 0, 0, q_a, Dir::L),
        tm.quints[i_gap] == mk_quint(q_a, 0, 0, q_a, Dir::L),
        tm.quints[i_a2b] == mk_quint(q_a, 5, 5, q_b, Dir::L),
        tm.quints[i_turn] == mk_quint(q_b, 0, 0, q_turn, Dir::R),
        tm.quints[i_master] == mk_quint(q_turn, 5, 5, q_turn, Dir::R),
        tm.quints[i_m2g] == mk_quint(q_turn, 0, 0, q_turng, Dir::R),
        tm.quints[i_rgap] == mk_quint(q_turng, 0, 0, q_turng, Dir::R),
        tm.quints[i_g2t] == mk_quint(q_turng, 1, 1, q_ret, Dir::R),
    ensures
        tail_safe(tm, TmConfig { u: copy_u(1, 1nat, g, tm.m), v: out, a: 0, q: q_home },
            (2 * g + 4) as nat, (g + 2) as nat),
        tail_end_h(tm, TmConfig { u: copy_u(1, 1nat, g, tm.m), v: out, a: 0, q: q_home },
            (2 * g + 4) as nat, (g + 2) as nat) == (g + 2) as nat,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let h0 = (g + 2) as nat;
    assert(repunit_m(1, m) == 1) by { lemma_repunit_step(0, m); lemma_repunit_zero(m); }
    assert(pow_nat(m, 0) == 1);
    lemma_repunit_zero(m);
    let pile_temp = pile_sym(out * m, 1, 1, m);
    let p_g = (pile_temp * pow_nat(m, (g - 1) as nat)) as nat;
    lemma_copy_u_end(1, g, m);
    let c0 = TmConfig { u: copy_u(1, 1nat, g, m), v: out, a: 0, q: q_home };
    assert(c0.u == 1 + pow_nat(m, g) * 5) by(nonlinear_arith)
        requires c0.u == repunit_m(1, m) + pow_nat(m, g) * (5 * repunit_m(1, m)), repunit_m(1, m) == 1;

    // ── S1: pivot-peel (L). offset h0 → g+1. ──
    lemma_pow_nat_unfold(m, g);
    let u1 = (pow_nat(m, (g - 1) as nat) * 5) as nat;
    assert(c0.u == u1 * m + 1) by(nonlinear_arith)
        requires c0.u == 1 + pow_nat(m, g) * 5, pow_nat(m, g) == m * pow_nat(m, (g - 1) as nat),
            u1 == pow_nat(m, (g - 1) as nat) * 5;
    lemma_div_mod_step(u1, m, 1);
    lemma_tm_step_picks(tm, c0, i_peel);
    let c1 = apply_quint(tm.quints[i_peel], c0, m);
    assert(tm_step(tm, c0) == Some(c1));
    assert(c1.u == u1 && c1.v == out * m && c1.a == 1 && c1.q == q_t);
    assert(tm_run(tm, c1, 0) == c1);
    assert(tm_run(tm, c0, 1) == c1);
    assert(quint_matches(tm.quints[i_peel], c0));
    lemma_step_tail_safe(tm, c0, i_peel, h0);

    // ── S2: walk-left over the single temp one (1 step). offset g+1 → g. ──
    assert(c1.u == 1 * repunit_m(0, m) + pow_nat(m, 0) * u1) by(nonlinear_arith)
        requires c1.u == u1, repunit_m(0, m) == 0, pow_nat(m, 0) == 1;
    lemma_run_walk_left(tm, c1, q_t, 1, 0, u1, i_temp);
    lemma_pow_nat_unfold(m, (g - 1) as nat);
    assert(u1 == (pow_nat(m, (g - 2) as nat) * 5) * m) by(nonlinear_arith)
        requires u1 == pow_nat(m, (g - 1) as nat) * 5,
            pow_nat(m, (g - 1) as nat) == m * pow_nat(m, (g - 2) as nat);
    lemma_div_mod_step((pow_nat(m, (g - 2) as nat) * 5) as nat, m, 0);
    let c2 = TmConfig { u: (pow_nat(m, (g - 2) as nat) * 5) as nat, v: pile_temp, a: 0, q: q_t };
    assert(tm_run(tm, c1, 1) == c2);
    lemma_tm_run_split(tm, c0, 1, 1);
    assert(tm_run(tm, c0, 2nat) == c2);
    lemma_run_walk_left_tail_safe(tm, c1, q_t, 1, 0, u1, i_temp, (g + 1) as nat);
    lemma_tail_chain(tm, c0, 1, 1, h0, (g + 1) as nat, g);

    // ── S3: temp→gap transition (L). offset g → g-1. ──
    lemma_pow_nat_unfold(m, (g - 2) as nat);
    assert(c2.u == (pow_nat(m, (g - 3) as nat) * 5) * m) by(nonlinear_arith)
        requires c2.u == pow_nat(m, (g - 2) as nat) * 5,
            pow_nat(m, (g - 2) as nat) == m * pow_nat(m, (g - 3) as nat);
    lemma_div_mod_step((pow_nat(m, (g - 3) as nat) * 5) as nat, m, 0);
    lemma_tm_step_picks(tm, c2, i_t2g);
    let c3 = apply_quint(tm.quints[i_t2g], c2, m);
    assert(tm_step(tm, c2) == Some(c3));
    assert(c3.u == pow_nat(m, (g - 3) as nat) * 5 && c3.v == pile_temp * m && c3.a == 0 && c3.q == q_a);
    assert(tm_run(tm, c3, 0) == c3);
    assert(tm_run(tm, c2, 1) == c3);
    lemma_tm_run_split(tm, c0, 2nat, 1);
    assert(tm_run(tm, c0, 3nat) == c3);
    assert(quint_matches(tm.quints[i_t2g], c2));
    lemma_step_tail_safe(tm, c2, i_t2g, g);
    lemma_tail_chain(tm, c0, 2nat, 1, h0, g, (g - 1) as nat);

    // ── S4: gap-seek-left (g-2 steps), lands on the single master five. offset g-1 → 1. ──
    lemma_div_mod_step(0, m, 5);
    assert(0 * m + 5 == 5) by(nonlinear_arith);
    assert((5nat) / m == 0 && (5nat) % m == 5);
    assert((5nat) % m != 0);
    assert(c3.u == pow_nat(m, (g - 3) as nat) * 5);
    lemma_seek_left_blanks(tm, c3, q_a, (g - 3) as nat, 5nat, i_gap);
    assert(((g - 3) + 1) as nat == (g - 2) as nat);
    assert((pile_temp * m) * pow_nat(m, (g - 2) as nat) == p_g) by(nonlinear_arith)
        requires p_g == pile_temp * pow_nat(m, (g - 1) as nat),
            pow_nat(m, (g - 1) as nat) == m * pow_nat(m, (g - 2) as nat);
    let c4 = TmConfig { u: 0, v: p_g, a: 5, q: q_a };
    assert(tm_run(tm, c3, (g - 2) as nat) == c4);
    lemma_tm_run_split(tm, c0, 3nat, (g - 2) as nat);
    assert((3 + (g - 2)) as nat == (g + 1) as nat);
    assert(tm_run(tm, c0, (g + 1) as nat) == c4);
    lemma_seek_left_tail_safe(tm, c3, q_a, (g - 3) as nat, 5nat, i_gap, (g - 1) as nat);
    assert(((g - 1) - (g - 2)) as nat == 1);
    lemma_tail_chain(tm, c0, 3nat, (g - 2) as nat, h0, (g - 1) as nat, 1);

    // ── S5: a2b (q_a, 5, 5, q_b, L), single five crossed, lands above master. offset 1 → 0 (TIGHT). ──
    lemma_tm_step_picks(tm, c4, i_a2b);
    let c5 = apply_quint(tm.quints[i_a2b], c4, m);
    assert(tm_step(tm, c4) == Some(c5));
    assert(c5.u == 0 && c5.v == p_g * m + 5 && c5.a == 0 && c5.q == q_b) by {
        assert((0nat) / m == 0);
        assert((0nat) % m == 0);
    }
    assert(tm_run(tm, c5, 0) == c5);
    assert(tm_run(tm, c4, 1) == c5);
    lemma_tm_run_split(tm, c0, (g + 1) as nat, 1);
    assert(tm_run(tm, c0, (g + 2) as nat) == c5);
    assert(quint_matches(tm.quints[i_a2b], c4));
    lemma_step_tail_safe(tm, c4, i_a2b, 1);
    lemma_tail_chain(tm, c0, (g + 1) as nat, 1, h0, 1, 0);

    // ── S7: TURN (q_b, 0, 0, q_turn, R) onto the master five. offset 0 → 1 (unconditional). ──
    assert(c5.v == pile_sym(p_g, 5, 1, m)) by {
        assert(pile_sym(p_g, 5, 0, m) == p_g);
        assert(pile_sym(p_g, 5, 1, m) == pile_sym(p_g, 5, 0, m) * m + 5);
    }
    lemma_pile_sym_div_mod(p_g, 5, 1, m);
    assert(c5.u * m == 0) by(nonlinear_arith) requires c5.u == 0;
    lemma_tm_step_picks(tm, c5, i_turn);
    let c6 = apply_quint(tm.quints[i_turn], c5, m);
    assert(tm_step(tm, c5) == Some(c6));
    assert(c6.u == 0 && c6.a == 5 && c6.v == p_g && c6.q == q_turn) by {
        assert(pile_sym(p_g, 5, 0, m) == p_g);
    }
    assert(tm_run(tm, c6, 0) == c6);
    assert(tm_run(tm, c5, 1) == c6);
    lemma_tm_run_split(tm, c0, (g + 2) as nat, 1);
    assert(tm_run(tm, c0, (g + 3) as nat) == c6);
    assert(quint_matches(tm.quints[i_turn], c5));
    lemma_step_tail_safe(tm, c5, i_turn, 0);
    lemma_tail_chain(tm, c0, (g + 2) as nat, 1, h0, 0, 1);

    // ── S8: master-walk-right (1 step, PRESERVE 5). offset 1 → 2. ──
    assert(c6.u == 5 * repunit_m(0, m) + pow_nat(m, 0) * 0) by(nonlinear_arith)
        requires c6.u == 0, repunit_m(0, m) == 0, pow_nat(m, 0) == 1;
    assert(c6.v == pile_sym(p_g, 5, 0, m)) by { assert(pile_sym(p_g, 5, 0, m) == p_g); }
    lemma_run_walk_right(tm, c6, q_turn, 5, 0, 0, p_g, 0, i_master);
    assert((0 + 0 + 1) as nat == 1nat);
    assert(5 * repunit_m(1, m) + pow_nat(m, 1) * 0 == 5) by(nonlinear_arith)
        requires repunit_m(1, m) == 1;
    assert(p_g == (pile_temp * pow_nat(m, (g - 2) as nat)) * m) by(nonlinear_arith)
        requires p_g == pile_temp * pow_nat(m, (g - 1) as nat),
            pow_nat(m, (g - 1) as nat) == m * pow_nat(m, (g - 2) as nat);
    lemma_div_mod_step((pile_temp * pow_nat(m, (g - 2) as nat)) as nat, m, 0);
    let c7 = TmConfig { u: 5, v: (pile_temp * pow_nat(m, (g - 2) as nat)) as nat, a: 0, q: q_turn };
    assert(tm_run(tm, c6, 1) == c7);
    lemma_tm_run_split(tm, c0, (g + 3) as nat, 1);
    assert(tm_run(tm, c0, (g + 4) as nat) == c7);
    lemma_run_walk_right_tail_safe(tm, c6, q_turn, 5, 0, 0, p_g, 0, i_master, 1);
    lemma_tail_chain(tm, c0, (g + 3) as nat, 1, h0, 1, 2);

    // ── S9: m2g transition (q_turn, 0, 0, q_turng, R). offset 2 → 3. ──
    lemma_pow_nat_unfold(m, (g - 2) as nat);
    assert(c7.v == (pile_temp * pow_nat(m, (g - 3) as nat)) * m) by(nonlinear_arith)
        requires c7.v == pile_temp * pow_nat(m, (g - 2) as nat),
            pow_nat(m, (g - 2) as nat) == m * pow_nat(m, (g - 3) as nat);
    lemma_div_mod_step((pile_temp * pow_nat(m, (g - 3) as nat)) as nat, m, 0);
    lemma_tm_step_picks(tm, c7, i_m2g);
    let c8 = apply_quint(tm.quints[i_m2g], c7, m);
    assert(tm_step(tm, c7) == Some(c8));
    assert(c8.u == 5 * m + 0 && c8.v == c7.v / m && c8.a == 0 && c8.q == q_turng);
    assert(c8.u == 5 * m) by(nonlinear_arith) requires c8.u == 5 * m + 0;
    assert(c8.v == pile_temp * pow_nat(m, (g - 3) as nat));
    assert(tm_run(tm, c8, 0) == c8);
    assert(tm_run(tm, c7, 1) == c8);
    lemma_tm_run_split(tm, c0, (g + 4) as nat, 1);
    assert(tm_run(tm, c0, (g + 5) as nat) == c8);
    assert(quint_matches(tm.quints[i_m2g], c7));
    lemma_step_tail_safe(tm, c7, i_m2g, 2);
    lemma_tail_chain(tm, c0, (g + 4) as nat, 1, h0, 2, 3);

    // ── S10: gap-seek-right (g-2 steps). offset 3 → g+1. ──
    lemma_pile_sym_div_mod(out * m, 1, 1, m);
    assert(c8.v == pow_nat(m, (g - 3) as nat) * pile_temp) by(nonlinear_arith)
        requires c8.v == pile_temp * pow_nat(m, (g - 3) as nat);
    lemma_seek_right_blanks(tm, c8, q_turng, (g - 3) as nat, pile_temp, i_rgap);
    assert(((g - 3) + 1) as nat == (g - 2) as nat);
    let c9 = TmConfig { u: (c8.u * pow_nat(m, (g - 2) as nat)) as nat, v: out * m, a: 1, q: q_turng };
    assert(pile_sym(out * m, 1, 0, m) == out * m);
    assert(tm_run(tm, c8, (g - 2) as nat) == c9);
    lemma_tm_run_split(tm, c0, (g + 5) as nat, (g - 2) as nat);
    assert((g + 5 + (g - 2)) as nat == (2 * g + 3) as nat);
    assert(tm_run(tm, c0, (2 * g + 3) as nat) == c9);
    lemma_seek_right_tail_safe(tm, c8, q_turng, (g - 3) as nat, pile_temp, i_rgap, 3);
    assert((3 + (g - 2)) as nat == (g + 1) as nat);
    lemma_tail_chain(tm, c0, (g + 5) as nat, (g - 2) as nat, h0, 3, (g + 1) as nat);

    // ── S11: g2t transition (q_turng, 1, 1, q_ret, R) lands DIRECTLY on the pivot. offset g+1 → g+2. ──
    lemma_div_mod_step(out, m, 0);
    assert(out * m + 0 == out * m) by(nonlinear_arith);
    lemma_tm_step_picks(tm, c9, i_g2t);
    let c10 = apply_quint(tm.quints[i_g2t], c9, m);
    assert(tm_step(tm, c9) == Some(c10));
    assert(c10.u == c9.u * m + 1 && c10.v == (out * m) / m && c10.a == (out * m) % m && c10.q == q_ret);
    assert(c10.v == out && c10.a == 0);
    assert(tm_run(tm, c10, 0) == c10);
    assert(tm_run(tm, c9, 1) == c10);
    lemma_tm_run_split(tm, c0, (2 * g + 3) as nat, 1);
    assert(tm_run(tm, c0, (2 * g + 4) as nat) == c10);
    assert(quint_matches(tm.quints[i_g2t], c9));
    lemma_step_tail_safe(tm, c9, i_g2t, (g + 1) as nat);
    lemma_tail_chain(tm, c0, (2 * g + 3) as nat, 1, h0, (g + 1) as nat, (g + 2) as nat);
}

/// **`unmark_m1` is tail-safe** for its `2g+4` steps, offset returning to `H_0 = g+2` (net displacement
/// 0). Structural twin of [`lemma_mark_terminate_m1_tail_safe`]: identical offset skeleton; S5 converts
/// the single master five to a one (still an L-move), and the master-walk-right (S8) crosses the resulting
/// one. Mirror of [`crate::tm_copy_refresh::lemma_unmark_m1`].
pub proof fn lemma_unmark_m1_tail_safe(
    tm: Tm, g: nat, out: nat,
    q_uh: nat, q_ut: nat, q_ua: nat, q_uf: nat, q_ur: nat, q_urg: nat, q_urt: nat,
    i_peel: int, i_temp: int, i_t2g: int, i_gap: int, i_u1: int,
    i_turn: int, i_master: int, i_m2g: int, i_rgap: int, i_g2t: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        g >= 3,
        0 <= i_peel < tm.quints.len(),
        0 <= i_temp < tm.quints.len(),
        0 <= i_t2g < tm.quints.len(),
        0 <= i_gap < tm.quints.len(),
        0 <= i_u1 < tm.quints.len(),
        0 <= i_turn < tm.quints.len(),
        0 <= i_master < tm.quints.len(),
        0 <= i_m2g < tm.quints.len(),
        0 <= i_rgap < tm.quints.len(),
        0 <= i_g2t < tm.quints.len(),
        tm.quints[i_peel] == mk_quint(q_uh, 0, 0, q_ut, Dir::L),
        tm.quints[i_temp] == mk_quint(q_ut, 1, 1, q_ut, Dir::L),
        tm.quints[i_t2g] == mk_quint(q_ut, 0, 0, q_ua, Dir::L),
        tm.quints[i_gap] == mk_quint(q_ua, 0, 0, q_ua, Dir::L),
        tm.quints[i_u1] == mk_quint(q_ua, 5, 1, q_uf, Dir::L),
        tm.quints[i_turn] == mk_quint(q_uf, 0, 0, q_ur, Dir::R),
        tm.quints[i_master] == mk_quint(q_ur, 1, 1, q_ur, Dir::R),
        tm.quints[i_m2g] == mk_quint(q_ur, 0, 0, q_urg, Dir::R),
        tm.quints[i_rgap] == mk_quint(q_urg, 0, 0, q_urg, Dir::R),
        tm.quints[i_g2t] == mk_quint(q_urg, 1, 1, q_urt, Dir::R),
    ensures
        tail_safe(tm, TmConfig { u: copy_u(1, 1nat, g, tm.m), v: out, a: 0, q: q_uh },
            (2 * g + 4) as nat, (g + 2) as nat),
        tail_end_h(tm, TmConfig { u: copy_u(1, 1nat, g, tm.m), v: out, a: 0, q: q_uh },
            (2 * g + 4) as nat, (g + 2) as nat) == (g + 2) as nat,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let h0 = (g + 2) as nat;
    assert(repunit_m(1, m) == 1) by { lemma_repunit_step(0, m); lemma_repunit_zero(m); }
    assert(pow_nat(m, 0) == 1);
    lemma_repunit_zero(m);
    let pile_temp = pile_sym(out * m, 1, 1, m);
    let p_g = (pile_temp * pow_nat(m, (g - 1) as nat)) as nat;
    lemma_copy_u_end(1, g, m);
    let c0 = TmConfig { u: copy_u(1, 1nat, g, m), v: out, a: 0, q: q_uh };
    assert(c0.u == 1 + pow_nat(m, g) * 5) by(nonlinear_arith)
        requires c0.u == repunit_m(1, m) + pow_nat(m, g) * (5 * repunit_m(1, m)), repunit_m(1, m) == 1;

    // ── S1: pivot-peel (L). offset h0 → g+1. ──
    lemma_pow_nat_unfold(m, g);
    let u1 = (pow_nat(m, (g - 1) as nat) * 5) as nat;
    assert(c0.u == u1 * m + 1) by(nonlinear_arith)
        requires c0.u == 1 + pow_nat(m, g) * 5, pow_nat(m, g) == m * pow_nat(m, (g - 1) as nat),
            u1 == pow_nat(m, (g - 1) as nat) * 5;
    lemma_div_mod_step(u1, m, 1);
    lemma_tm_step_picks(tm, c0, i_peel);
    let c1 = apply_quint(tm.quints[i_peel], c0, m);
    assert(tm_step(tm, c0) == Some(c1));
    assert(c1.u == u1 && c1.v == out * m && c1.a == 1 && c1.q == q_ut);
    assert(tm_run(tm, c1, 0) == c1);
    assert(tm_run(tm, c0, 1) == c1);
    assert(quint_matches(tm.quints[i_peel], c0));
    lemma_step_tail_safe(tm, c0, i_peel, h0);

    // ── S2: walk-left over the single temp one (1 step). offset g+1 → g. ──
    assert(c1.u == 1 * repunit_m(0, m) + pow_nat(m, 0) * u1) by(nonlinear_arith)
        requires c1.u == u1, repunit_m(0, m) == 0, pow_nat(m, 0) == 1;
    lemma_run_walk_left(tm, c1, q_ut, 1, 0, u1, i_temp);
    lemma_pow_nat_unfold(m, (g - 1) as nat);
    assert(u1 == (pow_nat(m, (g - 2) as nat) * 5) * m) by(nonlinear_arith)
        requires u1 == pow_nat(m, (g - 1) as nat) * 5,
            pow_nat(m, (g - 1) as nat) == m * pow_nat(m, (g - 2) as nat);
    lemma_div_mod_step((pow_nat(m, (g - 2) as nat) * 5) as nat, m, 0);
    let c2 = TmConfig { u: (pow_nat(m, (g - 2) as nat) * 5) as nat, v: pile_temp, a: 0, q: q_ut };
    assert(tm_run(tm, c1, 1) == c2);
    lemma_tm_run_split(tm, c0, 1, 1);
    assert(tm_run(tm, c0, 2nat) == c2);
    lemma_run_walk_left_tail_safe(tm, c1, q_ut, 1, 0, u1, i_temp, (g + 1) as nat);
    lemma_tail_chain(tm, c0, 1, 1, h0, (g + 1) as nat, g);

    // ── S3: temp→gap transition (L). offset g → g-1. ──
    lemma_pow_nat_unfold(m, (g - 2) as nat);
    assert(c2.u == (pow_nat(m, (g - 3) as nat) * 5) * m) by(nonlinear_arith)
        requires c2.u == pow_nat(m, (g - 2) as nat) * 5,
            pow_nat(m, (g - 2) as nat) == m * pow_nat(m, (g - 3) as nat);
    lemma_div_mod_step((pow_nat(m, (g - 3) as nat) * 5) as nat, m, 0);
    lemma_tm_step_picks(tm, c2, i_t2g);
    let c3 = apply_quint(tm.quints[i_t2g], c2, m);
    assert(tm_step(tm, c2) == Some(c3));
    assert(c3.u == pow_nat(m, (g - 3) as nat) * 5 && c3.v == pile_temp * m && c3.a == 0 && c3.q == q_ua);
    assert(tm_run(tm, c3, 0) == c3);
    assert(tm_run(tm, c2, 1) == c3);
    lemma_tm_run_split(tm, c0, 2nat, 1);
    assert(tm_run(tm, c0, 3nat) == c3);
    assert(quint_matches(tm.quints[i_t2g], c2));
    lemma_step_tail_safe(tm, c2, i_t2g, g);
    lemma_tail_chain(tm, c0, 2nat, 1, h0, g, (g - 1) as nat);

    // ── S4: gap-seek-left (g-2 steps), lands on the single master five. offset g-1 → 1. ──
    lemma_div_mod_step(0, m, 5);
    assert(0 * m + 5 == 5) by(nonlinear_arith);
    assert((5nat) / m == 0 && (5nat) % m == 5);
    assert((5nat) % m != 0);
    assert(c3.u == pow_nat(m, (g - 3) as nat) * 5);
    lemma_seek_left_blanks(tm, c3, q_ua, (g - 3) as nat, 5nat, i_gap);
    assert(((g - 3) + 1) as nat == (g - 2) as nat);
    assert((pile_temp * m) * pow_nat(m, (g - 2) as nat) == p_g) by(nonlinear_arith)
        requires p_g == pile_temp * pow_nat(m, (g - 1) as nat),
            pow_nat(m, (g - 1) as nat) == m * pow_nat(m, (g - 2) as nat);
    let c4 = TmConfig { u: 0, v: p_g, a: 5, q: q_ua };
    assert(tm_run(tm, c3, (g - 2) as nat) == c4);
    lemma_tm_run_split(tm, c0, 3nat, (g - 2) as nat);
    assert((3 + (g - 2)) as nat == (g + 1) as nat);
    assert(tm_run(tm, c0, (g + 1) as nat) == c4);
    lemma_seek_left_tail_safe(tm, c3, q_ua, (g - 3) as nat, 5nat, i_gap, (g - 1) as nat);
    assert(((g - 1) - (g - 2)) as nat == 1);
    lemma_tail_chain(tm, c0, 3nat, (g - 2) as nat, h0, (g - 1) as nat, 1);

    // ── S5: unmark-first (q_ua, 5, 1, q_uf, L). Single five → one. offset 1 → 0 (TIGHT). ──
    lemma_tm_step_picks(tm, c4, i_u1);
    let c5 = apply_quint(tm.quints[i_u1], c4, m);
    assert(tm_step(tm, c4) == Some(c5));
    assert(c5.u == 0 && c5.v == p_g * m + 1 && c5.a == 0 && c5.q == q_uf) by {
        assert((0nat) / m == 0);
        assert((0nat) % m == 0);
    }
    assert(tm_run(tm, c5, 0) == c5);
    assert(tm_run(tm, c4, 1) == c5);
    lemma_tm_run_split(tm, c0, (g + 1) as nat, 1);
    assert(tm_run(tm, c0, (g + 2) as nat) == c5);
    assert(quint_matches(tm.quints[i_u1], c4));
    lemma_step_tail_safe(tm, c4, i_u1, 1);
    lemma_tail_chain(tm, c0, (g + 1) as nat, 1, h0, 1, 0);

    // ── S7: TURN (q_uf, 0, 0, q_ur, R) onto the master one. offset 0 → 1 (unconditional). ──
    assert(c5.v == pile_sym(p_g, 1, 1, m)) by {
        assert(pile_sym(p_g, 1, 0, m) == p_g);
        assert(pile_sym(p_g, 1, 1, m) == pile_sym(p_g, 1, 0, m) * m + 1);
    }
    lemma_pile_sym_div_mod(p_g, 1, 1, m);
    assert(c5.u * m == 0) by(nonlinear_arith) requires c5.u == 0;
    lemma_tm_step_picks(tm, c5, i_turn);
    let c6 = apply_quint(tm.quints[i_turn], c5, m);
    assert(tm_step(tm, c5) == Some(c6));
    assert(c6.u == 0 && c6.a == 1 && c6.v == p_g && c6.q == q_ur) by {
        assert(pile_sym(p_g, 1, 0, m) == p_g);
    }
    assert(tm_run(tm, c6, 0) == c6);
    assert(tm_run(tm, c5, 1) == c6);
    lemma_tm_run_split(tm, c0, (g + 2) as nat, 1);
    assert(tm_run(tm, c0, (g + 3) as nat) == c6);
    assert(quint_matches(tm.quints[i_turn], c5));
    lemma_step_tail_safe(tm, c5, i_turn, 0);
    lemma_tail_chain(tm, c0, (g + 2) as nat, 1, h0, 0, 1);

    // ── S8: master-walk-right (1 step, cross the new one). offset 1 → 2. ──
    assert(c6.u == 1 * repunit_m(0, m) + pow_nat(m, 0) * 0) by(nonlinear_arith)
        requires c6.u == 0, repunit_m(0, m) == 0, pow_nat(m, 0) == 1;
    assert(c6.v == pile_sym(p_g, 1, 0, m)) by { assert(pile_sym(p_g, 1, 0, m) == p_g); }
    lemma_run_walk_right(tm, c6, q_ur, 1, 0, 0, p_g, 0, i_master);
    assert((0 + 0 + 1) as nat == 1nat);
    assert(1 * repunit_m(1, m) + pow_nat(m, 1) * 0 == 1) by(nonlinear_arith)
        requires repunit_m(1, m) == 1;
    assert(p_g == (pile_temp * pow_nat(m, (g - 2) as nat)) * m) by(nonlinear_arith)
        requires p_g == pile_temp * pow_nat(m, (g - 1) as nat),
            pow_nat(m, (g - 1) as nat) == m * pow_nat(m, (g - 2) as nat);
    lemma_div_mod_step((pile_temp * pow_nat(m, (g - 2) as nat)) as nat, m, 0);
    let c7 = TmConfig { u: 1, v: (pile_temp * pow_nat(m, (g - 2) as nat)) as nat, a: 0, q: q_ur };
    assert(tm_run(tm, c6, 1) == c7);
    lemma_tm_run_split(tm, c0, (g + 3) as nat, 1);
    assert(tm_run(tm, c0, (g + 4) as nat) == c7);
    lemma_run_walk_right_tail_safe(tm, c6, q_ur, 1, 0, 0, p_g, 0, i_master, 1);
    lemma_tail_chain(tm, c0, (g + 3) as nat, 1, h0, 1, 2);

    // ── S9: m2g transition (q_ur, 0, 0, q_urg, R). offset 2 → 3. ──
    lemma_pow_nat_unfold(m, (g - 2) as nat);
    assert(c7.v == (pile_temp * pow_nat(m, (g - 3) as nat)) * m) by(nonlinear_arith)
        requires c7.v == pile_temp * pow_nat(m, (g - 2) as nat),
            pow_nat(m, (g - 2) as nat) == m * pow_nat(m, (g - 3) as nat);
    lemma_div_mod_step((pile_temp * pow_nat(m, (g - 3) as nat)) as nat, m, 0);
    lemma_tm_step_picks(tm, c7, i_m2g);
    let c8 = apply_quint(tm.quints[i_m2g], c7, m);
    assert(tm_step(tm, c7) == Some(c8));
    assert(c8.u == 1 * m + 0 && c8.v == c7.v / m && c8.a == 0 && c8.q == q_urg);
    assert(c8.u == m) by(nonlinear_arith) requires c8.u == 1 * m + 0;
    assert(c8.v == pile_temp * pow_nat(m, (g - 3) as nat));
    assert(tm_run(tm, c8, 0) == c8);
    assert(tm_run(tm, c7, 1) == c8);
    lemma_tm_run_split(tm, c0, (g + 4) as nat, 1);
    assert(tm_run(tm, c0, (g + 5) as nat) == c8);
    assert(quint_matches(tm.quints[i_m2g], c7));
    lemma_step_tail_safe(tm, c7, i_m2g, 2);
    lemma_tail_chain(tm, c0, (g + 4) as nat, 1, h0, 2, 3);

    // ── S10: gap-seek-right (g-2 steps). offset 3 → g+1. ──
    lemma_pile_sym_div_mod(out * m, 1, 1, m);
    assert(c8.v == pow_nat(m, (g - 3) as nat) * pile_temp) by(nonlinear_arith)
        requires c8.v == pile_temp * pow_nat(m, (g - 3) as nat);
    lemma_seek_right_blanks(tm, c8, q_urg, (g - 3) as nat, pile_temp, i_rgap);
    assert(((g - 3) + 1) as nat == (g - 2) as nat);
    let c9 = TmConfig { u: (c8.u * pow_nat(m, (g - 2) as nat)) as nat, v: out * m, a: 1, q: q_urg };
    assert(pile_sym(out * m, 1, 0, m) == out * m);
    assert(tm_run(tm, c8, (g - 2) as nat) == c9);
    lemma_tm_run_split(tm, c0, (g + 5) as nat, (g - 2) as nat);
    assert((g + 5 + (g - 2)) as nat == (2 * g + 3) as nat);
    assert(tm_run(tm, c0, (2 * g + 3) as nat) == c9);
    lemma_seek_right_tail_safe(tm, c8, q_urg, (g - 3) as nat, pile_temp, i_rgap, 3);
    assert((3 + (g - 2)) as nat == (g + 1) as nat);
    lemma_tail_chain(tm, c0, (g + 5) as nat, (g - 2) as nat, h0, 3, (g + 1) as nat);

    // ── S11: g2t transition (q_urg, 1, 1, q_urt, R) lands DIRECTLY on the pivot. offset g+1 → g+2. ──
    lemma_div_mod_step(out, m, 0);
    assert(out * m + 0 == out * m) by(nonlinear_arith);
    lemma_tm_step_picks(tm, c9, i_g2t);
    let c10 = apply_quint(tm.quints[i_g2t], c9, m);
    assert(tm_step(tm, c9) == Some(c10));
    assert(c10.u == c9.u * m + 1 && c10.v == (out * m) / m && c10.a == (out * m) % m && c10.q == q_urt);
    assert(c10.v == out && c10.a == 0);
    assert(tm_run(tm, c10, 0) == c10);
    assert(tm_run(tm, c9, 1) == c10);
    lemma_tm_run_split(tm, c0, (2 * g + 3) as nat, 1);
    assert(tm_run(tm, c0, (2 * g + 4) as nat) == c10);
    assert(quint_matches(tm.quints[i_g2t], c9));
    lemma_step_tail_safe(tm, c9, i_g2t, (g + 1) as nat);
    lemma_tail_chain(tm, c0, (2 * g + 3) as nat, 1, h0, (g + 1) as nat, (g + 2) as nat);
}

/// **`copy_refresh_m1` is tail-safe** for its `6g+12` steps at the home offset `H_0 = g+2`, net
/// displacement 0. Three phases (`copy_iter_j0` ∘ `mark_terminate_m1` ∘ `unmark_m1`), each net-disp-0 at
/// `H_0`, chained by [`lemma_tail_chain`]. Mirror of [`crate::tm_copy_refresh::lemma_copy_refresh_m1`].
pub proof fn lemma_copy_refresh_m1_tail_safe(
    tm: Tm, g: nat, out: nat,
    q_dh0: nat, q_dw0: nat, q_bk0: nat, q_t0: nat, q_a0: nat, q_rf0: nat, q_rg0: nat,
    q_t: nat, q_a: nat, q_b: nat, q_turn: nat, q_turng: nat, q_ret: nat, q_home: nat,
    q_ut: nat, q_ua: nat, q_uf: nat, q_ur: nat, q_urg: nat, q_urt: nat,
    i_dpeel: int, i_dtemp: int, i_dins: int, i_dwb: int,
    i_cpeel: int, i_ctemp: int, i_ct2g: int, i_cgap: int, i_cmark: int, i_crf2g: int, i_crgap: int,
    i_crg2t: int,
    i_tpeel: int, i_ttemp: int, i_tt2g: int, i_tgap: int, i_ta2b: int,
    i_tturn: int, i_tmaster: int, i_tm2g: int, i_trgap: int, i_tg2t: int,
    i_upeel: int, i_utemp: int, i_ut2g: int, i_ugap: int, i_uu1: int,
    i_uturn: int, i_umaster: int, i_um2g: int, i_urgap: int, i_ug2t: int,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        g >= 3,
        0 <= i_dpeel < tm.quints.len(),
        0 <= i_dtemp < tm.quints.len(),
        0 <= i_dins < tm.quints.len(),
        0 <= i_dwb < tm.quints.len(),
        0 <= i_cpeel < tm.quints.len(),
        0 <= i_ctemp < tm.quints.len(),
        0 <= i_ct2g < tm.quints.len(),
        0 <= i_cgap < tm.quints.len(),
        0 <= i_cmark < tm.quints.len(),
        0 <= i_crf2g < tm.quints.len(),
        0 <= i_crgap < tm.quints.len(),
        0 <= i_crg2t < tm.quints.len(),
        0 <= i_tpeel < tm.quints.len(),
        0 <= i_ttemp < tm.quints.len(),
        0 <= i_tt2g < tm.quints.len(),
        0 <= i_tgap < tm.quints.len(),
        0 <= i_ta2b < tm.quints.len(),
        0 <= i_tturn < tm.quints.len(),
        0 <= i_tmaster < tm.quints.len(),
        0 <= i_tm2g < tm.quints.len(),
        0 <= i_trgap < tm.quints.len(),
        0 <= i_tg2t < tm.quints.len(),
        0 <= i_upeel < tm.quints.len(),
        0 <= i_utemp < tm.quints.len(),
        0 <= i_ut2g < tm.quints.len(),
        0 <= i_ugap < tm.quints.len(),
        0 <= i_uu1 < tm.quints.len(),
        0 <= i_uturn < tm.quints.len(),
        0 <= i_umaster < tm.quints.len(),
        0 <= i_um2g < tm.quints.len(),
        0 <= i_urgap < tm.quints.len(),
        0 <= i_ug2t < tm.quints.len(),
        // ── j=0 copy quints (deposit-first; exits q_home) ──
        tm.quints[i_dpeel] == mk_quint(q_dh0, 0, 0, q_dw0, Dir::L),
        tm.quints[i_dtemp] == mk_quint(q_dw0, 1, 1, q_dw0, Dir::L),
        tm.quints[i_dins] == mk_quint(q_dw0, 0, 1, q_bk0, Dir::R),
        tm.quints[i_dwb] == mk_quint(q_bk0, 1, 1, q_bk0, Dir::R),
        tm.quints[i_cpeel] == mk_quint(q_bk0, 0, 0, q_t0, Dir::L),
        tm.quints[i_ctemp] == mk_quint(q_t0, 1, 1, q_t0, Dir::L),
        tm.quints[i_ct2g] == mk_quint(q_t0, 0, 0, q_a0, Dir::L),
        tm.quints[i_cgap] == mk_quint(q_a0, 0, 0, q_a0, Dir::L),
        tm.quints[i_cmark] == mk_quint(q_a0, 1, 5, q_rf0, Dir::R),
        tm.quints[i_crf2g] == mk_quint(q_rf0, 0, 0, q_rg0, Dir::R),
        tm.quints[i_crgap] == mk_quint(q_rg0, 0, 0, q_rg0, Dir::R),
        tm.quints[i_crg2t] == mk_quint(q_rg0, 1, 1, q_home, Dir::R),
        // ── terminate quints (home == q_home) ──
        tm.quints[i_tpeel] == mk_quint(q_home, 0, 0, q_t, Dir::L),
        tm.quints[i_ttemp] == mk_quint(q_t, 1, 1, q_t, Dir::L),
        tm.quints[i_tt2g] == mk_quint(q_t, 0, 0, q_a, Dir::L),
        tm.quints[i_tgap] == mk_quint(q_a, 0, 0, q_a, Dir::L),
        tm.quints[i_ta2b] == mk_quint(q_a, 5, 5, q_b, Dir::L),
        tm.quints[i_tturn] == mk_quint(q_b, 0, 0, q_turn, Dir::R),
        tm.quints[i_tmaster] == mk_quint(q_turn, 5, 5, q_turn, Dir::R),
        tm.quints[i_tm2g] == mk_quint(q_turn, 0, 0, q_turng, Dir::R),
        tm.quints[i_trgap] == mk_quint(q_turng, 0, 0, q_turng, Dir::R),
        tm.quints[i_tg2t] == mk_quint(q_turng, 1, 1, q_ret, Dir::R),
        // ── unmark quints (home == q_ret) ──
        tm.quints[i_upeel] == mk_quint(q_ret, 0, 0, q_ut, Dir::L),
        tm.quints[i_utemp] == mk_quint(q_ut, 1, 1, q_ut, Dir::L),
        tm.quints[i_ut2g] == mk_quint(q_ut, 0, 0, q_ua, Dir::L),
        tm.quints[i_ugap] == mk_quint(q_ua, 0, 0, q_ua, Dir::L),
        tm.quints[i_uu1] == mk_quint(q_ua, 5, 1, q_uf, Dir::L),
        tm.quints[i_uturn] == mk_quint(q_uf, 0, 0, q_ur, Dir::R),
        tm.quints[i_umaster] == mk_quint(q_ur, 1, 1, q_ur, Dir::R),
        tm.quints[i_um2g] == mk_quint(q_ur, 0, 0, q_urg, Dir::R),
        tm.quints[i_urgap] == mk_quint(q_urg, 0, 0, q_urg, Dir::R),
        tm.quints[i_ug2t] == mk_quint(q_urg, 1, 1, q_urt, Dir::R),
    ensures
        tail_safe(tm, TmConfig { u: copy_u(0, 1nat, g, tm.m), v: out, a: 0, q: q_dh0 },
            (6 * g + 12) as nat, (g + 2) as nat),
        tail_end_h(tm, TmConfig { u: copy_u(0, 1nat, g, tm.m), v: out, a: 0, q: q_dh0 },
            (6 * g + 12) as nat, (g + 2) as nat) == (g + 2) as nat,
{
    reveal(tm_wf);
    let m = tm.m;
    let h0 = (g + 2) as nat;
    let phase = (2 * g + 4) as nat;
    let c0 = TmConfig { u: copy_u(0, 1nat, g, m), v: out, a: 0, q: q_dh0 };

    // ── PHASE 1 — COPY (single j=0 iter): copy_u(0,1,g) → copy_u(1,1,g)@q_home. offset h0 → h0. ──
    lemma_copy_iter_j0(tm, 1nat, g, out,
        q_dh0, q_dw0, q_bk0, q_t0, q_a0, q_rf0, q_rg0, q_home,
        i_dpeel, i_dtemp, i_dins, i_dwb,
        i_cpeel, i_ctemp, i_ct2g, i_cgap, i_cmark, i_crf2g, i_crgap, i_crg2t);
    let c_copy = TmConfig { u: copy_u(1, 1nat, g, m), v: out, a: 0, q: q_home };
    assert(tm_run(tm, c0, phase) == c_copy);
    lemma_copy_iter_j0_tail_safe(tm, 1nat, g, out,
        q_dh0, q_dw0, q_bk0, q_t0, q_a0, q_rf0, q_rg0, q_home,
        i_dpeel, i_dtemp, i_dins, i_dwb,
        i_cpeel, i_ctemp, i_ct2g, i_cgap, i_cmark, i_crf2g, i_crgap, i_crg2t);

    // ── PHASE 2 — TERMINATE: copy_u(1,1,g)@q_home → @q_ret. offset h0 → h0. ──
    lemma_mark_terminate_m1(tm, g, out,
        q_home, q_t, q_a, q_b, q_turn, q_turng, q_ret,
        i_tpeel, i_ttemp, i_tt2g, i_tgap, i_ta2b, i_tturn, i_tmaster, i_tm2g, i_trgap, i_tg2t);
    let c_term = TmConfig { u: copy_u(1, 1nat, g, m), v: out, a: 0, q: q_ret };
    assert(tm_run(tm, c_copy, phase) == c_term);
    lemma_mark_terminate_m1_tail_safe(tm, g, out,
        q_home, q_t, q_a, q_b, q_turn, q_turng, q_ret,
        i_tpeel, i_ttemp, i_tt2g, i_tgap, i_ta2b, i_tturn, i_tmaster, i_tm2g, i_trgap, i_tg2t);

    // ── PHASE 3 — UNMARK: copy_u(1,1,g)@q_ret → dec_u(...)@q_urt. offset h0 → h0. ──
    lemma_unmark_m1(tm, g, out,
        q_ret, q_ut, q_ua, q_uf, q_ur, q_urg, q_urt,
        i_upeel, i_utemp, i_ut2g, i_ugap, i_uu1, i_uturn, i_umaster, i_um2g, i_urgap, i_ug2t);
    lemma_unmark_m1_tail_safe(tm, g, out,
        q_ret, q_ut, q_ua, q_uf, q_ur, q_urg, q_urt,
        i_upeel, i_utemp, i_ut2g, i_ugap, i_uu1, i_uturn, i_umaster, i_um2g, i_urgap, i_ug2t);

    // ── chain COPY ∘ TERMINATE ∘ UNMARK at h0. ──
    lemma_tm_run_split(tm, c0, phase, phase);
    assert(tm_run(tm, c0, (2 * phase) as nat) == c_term);
    lemma_tail_chain(tm, c0, phase, phase, h0, h0, h0);          // COPY ∘ TERMINATE
    lemma_tail_chain(tm, c0, (2 * phase) as nat, phase, h0, h0, h0);   // (·) ∘ UNMARK
    assert((2 * phase + phase) as nat == (6 * g + 12) as nat);
}

} // verus!
