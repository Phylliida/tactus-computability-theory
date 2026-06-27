//! # GAP-2 G2-F Route (i) brick R-relnum-gen (STEP 2, model B) — the per-block LOOP.
//!
//! A `fam_digits` power-block `(blk)^i` is emitted by iterating [`crate::tm_block_iter`]'s body `i` times,
//! decrementing the active counter `temp` each pass until it is exhausted. This file wraps that body in a
//! TM-level loop: a 2-step **guard** peeks the counter at the home pivot and branches —
//!   - `temp > 0` ([`lemma_guard_continue`]): the inner cell is a `1`, restore and fall into the iteration;
//!   - `temp == 0` ([`lemma_guard_exit`]): the inner cell is the separator `0`, restore and exit.
//! The guard is non-destructive (peel pivot left → peek → move back right), so the output and masters round
//! trip. The iteration body's `dec_temp` lands back in the guard state (`q_back == q_loop`), closing the loop.
//!
//! [`lemma_block_loop_block1`] is the full loop for a singleton power-block (`(1)^i`, `(3)^i`): from
//! `{u: dec_u(temp, w), v: dpack(od)}` it runs to `{u: dec_u(0, m^temp·w), v: dpack(od ++ seq_pow([s], temp))}`
//! in [`loop_fuel_b1`] steps (induction on `temp`). The counter is consumed (its `temp` ones replaced by
//! blanks, the master `w` shifted up to `m^temp·w`), the output gains the run `(s)^temp`.
//!
//! `docs/gap2-input-loader-plan.md` §5 (R-relnum-gen STEP 2, model B). Fully verified, no escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use verus_group_theory::word_numbering::lemma_div_mod_step;
use crate::tm::{Tm, TmConfig, tm_wf, tm_step, tm_run, quint_matches, apply_quint};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};
use crate::tm_run_lemmas::lemma_tm_run_split;
use crate::tm_two_counter::{repunit_m, lemma_repunit_zero, lemma_repunit_step};
use crate::tm_dstring::{dpack, pow_nat, lemma_pow_nat_unfold};
use crate::tm_dec_master::dec_u;
use crate::tm_block_iter::{lemma_block_iter_block1, lemma_block_iter_block3};
use crate::gap2_relnum_dds::seq_pow;

verus! {

// ============================================================================
// dec_u arithmetic the guard reads
// ============================================================================

/// `dec_u(0, w, m) == w` — an empty counter is just the high content.
pub proof fn lemma_dec_u_zero(w: nat, m: nat)
    ensures
        dec_u(0, w, m) == w,
{
    lemma_repunit_zero(m);          // repunit_m(0) == 0
    assert(pow_nat(m, 0) == 1);
    assert(1nat * w == w) by(nonlinear_arith);
}

/// `dec_u(temp, w, m) == m·dec_u(temp − 1, w, m) + 1` for `temp ≥ 1` — peeling the inner counter one. So
/// `dec_u(temp, w) % m == 1` (the counter is nonempty) and `/ m == dec_u(temp − 1, w)`.
pub proof fn lemma_dec_u_step(temp: nat, w: nat, m: nat)
    requires
        m > 1,
        temp >= 1,
    ensures
        dec_u(temp, w, m) == m * dec_u((temp - 1) as nat, w, m) + 1,
        dec_u(temp, w, m) % m == 1,
        dec_u(temp, w, m) / m == dec_u((temp - 1) as nat, w, m),
{
    let t1 = (temp - 1) as nat;
    lemma_repunit_step(t1, m);          // repunit_m(t1+1) == m·repunit_m(t1) + 1
    assert(repunit_m(temp, m) == m * repunit_m(t1, m) + 1);
    lemma_pow_nat_unfold(m, temp);      // m^temp == m·m^{temp-1}
    // dec_u(temp,w) == repunit(temp) + m^temp·w == m·repunit(t1)+1 + m·(m^{t1}·w)
    //              == m·(repunit(t1) + m^{t1}·w) + 1 == m·dec_u(t1,w) + 1.
    assert(dec_u(temp, w, m) == m * dec_u(t1, w, m) + 1) by(nonlinear_arith)
        requires
            dec_u(temp, w, m) == repunit_m(temp, m) + pow_nat(m, temp) * w,
            dec_u(t1, w, m) == repunit_m(t1, m) + pow_nat(m, t1) * w,
            repunit_m(temp, m) == m * repunit_m(t1, m) + 1,
            pow_nat(m, temp) == m * pow_nat(m, t1);
    lemma_div_mod_step(dec_u(t1, w, m), m, 1);   // (x·m + 1)/m == x, %m == 1
}

// ============================================================================
// the guard (peek the counter, branch)
// ============================================================================

/// **Guard, continue branch (`temp ≥ 1`).** From home `{u: dec_u(temp, w), v: out, a: 0, q: q_loop}`, the
/// 2-step non-destructive peek `(q_loop, 0, 0, q_guard, L)` then `(q_guard, 1, 1, q_iter, R)` sees the inner
/// counter `1`, restores the pivot/output, and lands `{u: dec_u(temp, w), v: out, a: 0, q: q_iter}` — ready
/// to run the iteration body. Requires `w % m == 0` (the peeled pivot pushes a `0`, restored on the way back).
pub proof fn lemma_guard_continue(
    tm: Tm, temp: nat, w: nat, out: nat, q_loop: nat, q_guard: nat, q_iter: nat,
    i_peek: int, i_cont: int,
)
    requires
        tm_wf(tm),
        temp >= 1,
        0 <= i_peek < tm.quints.len(),
        0 <= i_cont < tm.quints.len(),
        tm.quints[i_peek] == mk_quint(q_loop, 0, 0, q_guard, Dir::L),
        tm.quints[i_cont] == mk_quint(q_guard, 1, 1, q_iter, Dir::R),
    ensures
        tm_run(tm, TmConfig { u: dec_u(temp, w, tm.m), v: out, a: 0, q: q_loop }, 2)
            == (TmConfig { u: dec_u(temp, w, tm.m), v: out, a: 0, q: q_iter }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1);
    lemma_dec_u_step(temp, w, m);   // dec_u(temp,w)%m==1, /m==dec_u(temp-1,w)
    let c0 = TmConfig { u: dec_u(temp, w, m), v: out, a: 0, q: q_loop };
    // step 1: peel pivot left.
    assert(quint_matches(tm.quints[i_peek], c0));
    lemma_tm_step_picks(tm, c0, i_peek);
    let c1 = apply_quint(tm.quints[i_peek], c0, m);
    assert(tm_step(tm, c0) == Some(c1));
    // L: u = dec_u(temp,w)/m == dec_u(temp-1,w), v = out·m, a = dec_u(temp,w)%m == 1.
    assert(c1.u == dec_u((temp - 1) as nat, w, m));
    assert(c1.v == out * m);
    assert(c1.a == 1);
    assert(c1.q == q_guard);
    assert(tm_run(tm, c1, 0) == c1);
    assert(tm_run(tm, c0, 1) == c1);
    // step 2: move back right, restoring.
    assert(quint_matches(tm.quints[i_cont], c1));
    lemma_tm_step_picks(tm, c1, i_cont);
    let c2 = apply_quint(tm.quints[i_cont], c1, m);
    assert(tm_step(tm, c1) == Some(c2));
    // R: u = dec_u(temp-1,w)·m + 1 == dec_u(temp,w), v = (out·m)/m == out, a = (out·m)%m == 0.
    assert(c2.u == dec_u((temp - 1) as nat, w, m) * m + 1);
    assert(c2.u == dec_u(temp, w, m)) by(nonlinear_arith)
        requires
            dec_u(temp, w, m) == m * dec_u((temp - 1) as nat, w, m) + 1,
            c2.u == dec_u((temp - 1) as nat, w, m) * m + 1;
    lemma_div_mod_step(out, m, 0);   // (out·m + 0)/m == out, %m == 0
    assert(out * m + 0 == out * m);
    assert(c2.v == out);
    assert(c2.a == 0);
    assert(c2.q == q_iter);
    assert(tm_run(tm, c2, 0) == c2);
    assert(tm_run(tm, c1, 1) == c2);
    lemma_tm_run_split(tm, c0, 1, 1);
    assert((1 + 1) as nat == 2);
}

/// **Guard, exit branch (`temp == 0`).** From `{u: dec_u(0, w) == w, v: out, a: 0, q: q_loop}` (`w % m == 0`),
/// the 2-step peek `(q_loop, 0, 0, q_guard, L)` then `(q_guard, 0, 0, q_exit, R)` sees the separator `0`
/// (counter empty), restores, and lands `{u: w, v: out, a: 0, q: q_exit}`.
pub proof fn lemma_guard_exit(
    tm: Tm, w: nat, out: nat, q_loop: nat, q_guard: nat, q_exit: nat,
    i_peek: int, i_exit: int,
)
    requires
        tm_wf(tm),
        w % tm.m == 0,
        0 <= i_peek < tm.quints.len(),
        0 <= i_exit < tm.quints.len(),
        tm.quints[i_peek] == mk_quint(q_loop, 0, 0, q_guard, Dir::L),
        tm.quints[i_exit] == mk_quint(q_guard, 0, 0, q_exit, Dir::R),
    ensures
        tm_run(tm, TmConfig { u: dec_u(0, w, tm.m), v: out, a: 0, q: q_loop }, 2)
            == (TmConfig { u: w, v: out, a: 0, q: q_exit }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1);
    lemma_dec_u_zero(w, m);   // dec_u(0,w) == w
    let c0 = TmConfig { u: w, v: out, a: 0, q: q_loop };
    // step 1: peel pivot left. a' = w%m == 0 (separator).
    assert(quint_matches(tm.quints[i_peek], c0));
    lemma_tm_step_picks(tm, c0, i_peek);
    let c1 = apply_quint(tm.quints[i_peek], c0, m);
    assert(tm_step(tm, c0) == Some(c1));
    assert(c1.u == w / m);
    assert(c1.v == out * m);
    assert(c1.a == 0);   // w % m == 0
    assert(c1.q == q_guard);
    assert(tm_run(tm, c1, 0) == c1);
    assert(tm_run(tm, c0, 1) == c1);
    // step 2: move back right. u = (w/m)·m + 0 == w  (w%m==0).
    assert(quint_matches(tm.quints[i_exit], c1));
    lemma_tm_step_picks(tm, c1, i_exit);
    let c2 = apply_quint(tm.quints[i_exit], c1, m);
    assert(tm_step(tm, c1) == Some(c2));
    lemma_div_mod_step(w / m, m, 0);   // ((w/m)·m + 0)/m == w/m, %m == 0
    assert((w / m) * m == w) by {
        assert(w == (w / m) * m + w % m) by(nonlinear_arith) requires m > 0;
        assert(w % m == 0);
    }
    assert(c2.u == w);
    lemma_div_mod_step(out, m, 0);
    assert(out * m + 0 == out * m);
    assert(c2.v == out);
    assert(c2.a == 0);
    assert(c2.q == q_exit);
    assert(tm_run(tm, c2, 0) == c2);
    assert(tm_run(tm, c1, 1) == c2);
    lemma_tm_run_split(tm, c0, 1, 1);
    assert((1 + 1) as nat == 2);
}

// ============================================================================
// the per-block loop (singleton power-block)
// ============================================================================

/// The total fuel for [`lemma_block_loop_block1`]: per turn, 2 (continue guard) + the body
/// (`2·odlen + 2·temp + 6`); the base (`temp == 0`) is the 2-step exit guard.
pub open spec fn loop_fuel_b1(odlen: nat, temp: nat) -> nat
    decreases temp
{
    if temp == 0 {
        2
    } else {
        (2 + (2 * odlen + 2 * temp + 6) + loop_fuel_b1((odlen + 1) as nat, (temp - 1) as nat)) as nat
    }
}

/// **The singleton power-block loop.** From `{u: dec_u(temp, w), v: dpack(od), a: 0, q: q_loop}` (counter
/// `temp`, master `w` with `w % m == 0`, output `od` digits `1..4`), iterating the body `temp` times emits
/// the run `(s)^temp`: lands `{u: dec_u(0, m^temp·w), v: dpack(od ++ seq_pow([s], temp)), a: 0, q: q_exit}`.
/// The counter is consumed; the master `w` survives, shifted to `m^temp·w`. `q_back == q_loop` (the body's
/// `dec_temp` returns to the guard). Induction on `temp`: the guard branches, the body emits one `s` and
/// decrements, recurse on `(od ++ [s], temp − 1, m·w)`.
pub proof fn lemma_block_loop_block1(
    tm: Tm, temp: nat, w: nat, od: Seq<nat>, s: nat,
    q_loop: nat, q_guard: nat, q_iter: nat, q_surge: nat, q_eret: nat, q_home: nat,
    q_dwalk: nat, q_disc: nat, q_exit: nat,
    i_peek: int, i_cont: int, i_exit: int,
    i_pivot_r: int, ir1: int, ir2: int, ir3: int, ir4: int,
    i_emit: int, i_off_l: int, il1: int, il2: int, il3: int, il4: int,
    i_pivot: int, i_one_l: int, i_erase: int, i_disc: int, i_one_r: int,
)
    requires
        tm_wf(tm),
        tm.n >= 4,
        w % tm.m == 0,
        1 <= s <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
        0 <= i_peek < tm.quints.len(),
        0 <= i_cont < tm.quints.len(),
        0 <= i_exit < tm.quints.len(),
        0 <= i_pivot_r < tm.quints.len(),
        0 <= ir1 < tm.quints.len(),
        0 <= ir2 < tm.quints.len(),
        0 <= ir3 < tm.quints.len(),
        0 <= ir4 < tm.quints.len(),
        0 <= i_emit < tm.quints.len(),
        0 <= i_off_l < tm.quints.len(),
        0 <= il1 < tm.quints.len(),
        0 <= il2 < tm.quints.len(),
        0 <= il3 < tm.quints.len(),
        0 <= il4 < tm.quints.len(),
        0 <= i_pivot < tm.quints.len(),
        0 <= i_one_l < tm.quints.len(),
        0 <= i_erase < tm.quints.len(),
        0 <= i_disc < tm.quints.len(),
        0 <= i_one_r < tm.quints.len(),
        tm.quints[i_peek] == mk_quint(q_loop, 0, 0, q_guard, Dir::L),
        tm.quints[i_cont] == mk_quint(q_guard, 1, 1, q_iter, Dir::R),
        tm.quints[i_exit] == mk_quint(q_guard, 0, 0, q_exit, Dir::R),
        tm.quints[i_pivot_r] == mk_quint(q_iter, 0, 0, q_surge, Dir::R),
        tm.quints[ir1] == mk_quint(q_surge, 1, 1, q_surge, Dir::R),
        tm.quints[ir2] == mk_quint(q_surge, 2, 2, q_surge, Dir::R),
        tm.quints[ir3] == mk_quint(q_surge, 3, 3, q_surge, Dir::R),
        tm.quints[ir4] == mk_quint(q_surge, 4, 4, q_surge, Dir::R),
        tm.quints[i_emit] == mk_quint(q_surge, 0, s, q_eret, Dir::R),
        tm.quints[i_off_l] == mk_quint(q_eret, 0, 0, q_home, Dir::L),
        tm.quints[il1] == mk_quint(q_home, 1, 1, q_home, Dir::L),
        tm.quints[il2] == mk_quint(q_home, 2, 2, q_home, Dir::L),
        tm.quints[il3] == mk_quint(q_home, 3, 3, q_home, Dir::L),
        tm.quints[il4] == mk_quint(q_home, 4, 4, q_home, Dir::L),
        tm.quints[i_pivot] == mk_quint(q_home, 0, 0, q_dwalk, Dir::L),
        tm.quints[i_one_l] == mk_quint(q_dwalk, 1, 1, q_dwalk, Dir::L),
        tm.quints[i_erase] == mk_quint(q_dwalk, 0, 0, q_disc, Dir::R),
        tm.quints[i_disc] == mk_quint(q_disc, 1, 0, q_loop, Dir::R),
        tm.quints[i_one_r] == mk_quint(q_loop, 1, 1, q_loop, Dir::R),
    ensures
        tm_run(tm, TmConfig { u: dec_u(temp, w, tm.m), v: dpack(od, tm.m), a: 0, q: q_loop },
            loop_fuel_b1(od.len(), temp))
            == (TmConfig { u: dec_u(0, (pow_nat(tm.m, temp) * w) as nat, tm.m),
                v: dpack(od + seq_pow(seq![s], temp), tm.m), a: 0, q: q_exit }),
    decreases temp,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 4);   // tm_wf ⟹ 0 < n < m, n ≥ 4
    let c0 = TmConfig { u: dec_u(temp, w, m), v: dpack(od, m), a: 0, q: q_loop };
    if temp == 0 {
        // exit guard. dec_u(0,w) == w; m^0·w == w; seq_pow([s],0) == empty.
        lemma_guard_exit(tm, w, dpack(od, m), q_loop, q_guard, q_exit, i_peek, i_exit);
        lemma_dec_u_zero(w, m);
        assert(pow_nat(m, 0) == 1);
        assert(1nat * w == w) by(nonlinear_arith);
        assert(seq_pow(seq![s], 0) =~= Seq::<nat>::empty());
        assert(od + seq_pow(seq![s], 0) =~= od);
        assert(dec_u(0, (pow_nat(m, 0) * w) as nat, m) == w) by { lemma_dec_u_zero(w, m); }
        assert(loop_fuel_b1(od.len(), 0) == 2);
    } else {
        // ── continue guard (2 steps) → q_iter ──
        lemma_guard_continue(tm, temp, w, dpack(od, m), q_loop, q_guard, q_iter, i_peek, i_cont);
        let c1 = TmConfig { u: dec_u(temp, w, m), v: dpack(od, m), a: 0, q: q_iter };
        assert(tm_run(tm, c0, 2) == c1);
        // ── body: output od ↦ od ++ [s], temp ↦ temp − 1, w ↦ m·w; lands q_loop ──
        lemma_block_iter_block1(tm, temp, w, od, s,
            q_iter, q_surge, q_eret, q_home, q_dwalk, q_disc, q_loop,
            i_pivot_r, ir1, ir2, ir3, ir4, i_emit, i_off_l, il1, il2, il3, il4,
            i_pivot, i_one_l, i_erase, i_disc, i_one_r);
        let od2 = od + seq![s];
        let c2 = TmConfig { u: dec_u((temp - 1) as nat, (m * w) as nat, m), v: dpack(od2, m), a: 0,
            q: q_loop };
        assert(tm_run(tm, c1, (2 * od.len() + 2 * temp + 6) as nat) == c2);
        // od2 digits 1..4; (m·w) % m == 0.
        assert forall|k: int| 0 <= k < od2.len() implies 1 <= #[trigger] od2[k] <= 4 by {
            if k < od.len() { assert(od2[k] == od[k]); } else { assert(od2[k] == s); }
        }
        assert((m * w) % m == 0) by {
            assert(m * w == w * m) by(nonlinear_arith);
            lemma_div_mod_step(w, m, 0);
        }
        // ── recurse on (od2, temp − 1, m·w) ──
        lemma_block_loop_block1(tm, (temp - 1) as nat, (m * w) as nat, od2, s,
            q_loop, q_guard, q_iter, q_surge, q_eret, q_home, q_dwalk, q_disc, q_exit,
            i_peek, i_cont, i_exit, i_pivot_r, ir1, ir2, ir3, ir4,
            i_emit, i_off_l, il1, il2, il3, il4, i_pivot, i_one_l, i_erase, i_disc, i_one_r);
        let c3 = TmConfig {
            u: dec_u(0, (pow_nat(m, (temp - 1) as nat) * (m * w)) as nat, m),
            v: dpack(od2 + seq_pow(seq![s], (temp - 1) as nat), m), a: 0, q: q_exit };
        assert(tm_run(tm, c2, loop_fuel_b1(od2.len(), (temp - 1) as nat)) == c3);
        // c3 == goal: m^{temp-1}·(m·w) == m^temp·w; (od++[s]) ++ seq_pow([s],temp-1) == od ++ seq_pow([s],temp).
        lemma_pow_nat_unfold(m, temp);   // m^temp == m·m^{temp-1}
        assert(pow_nat(m, (temp - 1) as nat) * (m * w) == pow_nat(m, temp) * w) by(nonlinear_arith)
            requires pow_nat(m, temp) == m * pow_nat(m, (temp - 1) as nat);
        assert(seq_pow(seq![s], temp) =~= seq![s] + seq_pow(seq![s], (temp - 1) as nat));   // seq_pow unfold
        assert(od2 + seq_pow(seq![s], (temp - 1) as nat)
            =~= od + seq_pow(seq![s], temp)) by {
            assert(od2 + seq_pow(seq![s], (temp - 1) as nat)
                =~= od + (seq![s] + seq_pow(seq![s], (temp - 1) as nat)));
        }
        assert(c3.u == dec_u(0, (pow_nat(m, temp) * w) as nat, m));
        assert(c3.v == dpack(od + seq_pow(seq![s], temp), m));
        // ── chain the fuel: 2 (guard) + body + recurse == loop_fuel_b1(od.len(), temp) ──
        lemma_tm_run_split(tm, c0, 2, (2 * od.len() + 2 * temp + 6) as nat);
        assert((2 + (2 * od.len() + 2 * temp + 6)) as nat == (2 * od.len() + 2 * temp + 8) as nat);
        assert(tm_run(tm, c0, (2 * od.len() + 2 * temp + 8) as nat) == c2);
        lemma_tm_run_split(tm, c0, (2 * od.len() + 2 * temp + 8) as nat,
            loop_fuel_b1(od2.len(), (temp - 1) as nat));
        assert(od2.len() == od.len() + 1);
        assert((2 * od.len() + 2 * temp + 8 + loop_fuel_b1(od2.len(), (temp - 1) as nat)) as nat
            == loop_fuel_b1(od.len(), temp));
    }
}

// ============================================================================
// the per-block loop (triple power-block)
// ============================================================================

/// The total fuel for [`lemma_block_loop_block3`]: per turn, 2 (continue guard) + the triple body
/// (`2·odlen + 2·temp + 10`); the output grows by 3 each turn. Base (`temp == 0`) is the exit guard.
pub open spec fn loop_fuel_b3(odlen: nat, temp: nat) -> nat
    decreases temp
{
    if temp == 0 {
        2
    } else {
        (2 + (2 * odlen + 2 * temp + 10) + loop_fuel_b3((odlen + 3) as nat, (temp - 1) as nat)) as nat
    }
}

/// **The triple power-block loop.** Like [`lemma_block_loop_block1`] but emits the triple `[s0,s1,s2]`
/// (the `fam_digits` triple power-blocks `(4,1,2)^i`, `(4,3,2)^i`): from `{u: dec_u(temp, w), v: dpack(od)}`
/// it runs to `{u: dec_u(0, m^temp·w), v: dpack(od ++ seq_pow([s0,s1,s2], temp))}`. Induction on `temp`,
/// body [`lemma_block_iter_block3`], output grows by 3 per turn.
pub proof fn lemma_block_loop_block3(
    tm: Tm, temp: nat, w: nat, od: Seq<nat>, s0: nat, s1: nat, s2: nat,
    q_loop: nat, q_guard: nat, q_iter: nat, q_surge: nat, q_e1: nat, q_e2: nat, q_eret: nat,
    q_home: nat, q_dwalk: nat, q_disc: nat, q_exit: nat,
    i_peek: int, i_cont: int, i_exit: int,
    i_pivot_r: int, ir1: int, ir2: int, ir3: int, ir4: int,
    i_e0: int, i_e1: int, i_e2: int, i_off_l: int, il1: int, il2: int, il3: int, il4: int,
    i_pivot: int, i_one_l: int, i_erase: int, i_disc: int, i_one_r: int,
)
    requires
        tm_wf(tm),
        tm.n >= 4,
        w % tm.m == 0,
        1 <= s0 <= 4,
        1 <= s1 <= 4,
        1 <= s2 <= 4,
        forall|k: int| 0 <= k < od.len() ==> 1 <= #[trigger] od[k] <= 4,
        0 <= i_peek < tm.quints.len(),
        0 <= i_cont < tm.quints.len(),
        0 <= i_exit < tm.quints.len(),
        0 <= i_pivot_r < tm.quints.len(),
        0 <= ir1 < tm.quints.len(),
        0 <= ir2 < tm.quints.len(),
        0 <= ir3 < tm.quints.len(),
        0 <= ir4 < tm.quints.len(),
        0 <= i_e0 < tm.quints.len(),
        0 <= i_e1 < tm.quints.len(),
        0 <= i_e2 < tm.quints.len(),
        0 <= i_off_l < tm.quints.len(),
        0 <= il1 < tm.quints.len(),
        0 <= il2 < tm.quints.len(),
        0 <= il3 < tm.quints.len(),
        0 <= il4 < tm.quints.len(),
        0 <= i_pivot < tm.quints.len(),
        0 <= i_one_l < tm.quints.len(),
        0 <= i_erase < tm.quints.len(),
        0 <= i_disc < tm.quints.len(),
        0 <= i_one_r < tm.quints.len(),
        tm.quints[i_peek] == mk_quint(q_loop, 0, 0, q_guard, Dir::L),
        tm.quints[i_cont] == mk_quint(q_guard, 1, 1, q_iter, Dir::R),
        tm.quints[i_exit] == mk_quint(q_guard, 0, 0, q_exit, Dir::R),
        tm.quints[i_pivot_r] == mk_quint(q_iter, 0, 0, q_surge, Dir::R),
        tm.quints[ir1] == mk_quint(q_surge, 1, 1, q_surge, Dir::R),
        tm.quints[ir2] == mk_quint(q_surge, 2, 2, q_surge, Dir::R),
        tm.quints[ir3] == mk_quint(q_surge, 3, 3, q_surge, Dir::R),
        tm.quints[ir4] == mk_quint(q_surge, 4, 4, q_surge, Dir::R),
        tm.quints[i_e0] == mk_quint(q_surge, 0, s0, q_e1, Dir::R),
        tm.quints[i_e1] == mk_quint(q_e1, 0, s1, q_e2, Dir::R),
        tm.quints[i_e2] == mk_quint(q_e2, 0, s2, q_eret, Dir::R),
        tm.quints[i_off_l] == mk_quint(q_eret, 0, 0, q_home, Dir::L),
        tm.quints[il1] == mk_quint(q_home, 1, 1, q_home, Dir::L),
        tm.quints[il2] == mk_quint(q_home, 2, 2, q_home, Dir::L),
        tm.quints[il3] == mk_quint(q_home, 3, 3, q_home, Dir::L),
        tm.quints[il4] == mk_quint(q_home, 4, 4, q_home, Dir::L),
        tm.quints[i_pivot] == mk_quint(q_home, 0, 0, q_dwalk, Dir::L),
        tm.quints[i_one_l] == mk_quint(q_dwalk, 1, 1, q_dwalk, Dir::L),
        tm.quints[i_erase] == mk_quint(q_dwalk, 0, 0, q_disc, Dir::R),
        tm.quints[i_disc] == mk_quint(q_disc, 1, 0, q_loop, Dir::R),
        tm.quints[i_one_r] == mk_quint(q_loop, 1, 1, q_loop, Dir::R),
    ensures
        tm_run(tm, TmConfig { u: dec_u(temp, w, tm.m), v: dpack(od, tm.m), a: 0, q: q_loop },
            loop_fuel_b3(od.len(), temp))
            == (TmConfig { u: dec_u(0, (pow_nat(tm.m, temp) * w) as nat, tm.m),
                v: dpack(od + seq_pow(seq![s0, s1, s2], temp), tm.m), a: 0, q: q_exit }),
    decreases temp,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 4);
    let blk = seq![s0, s1, s2];
    let c0 = TmConfig { u: dec_u(temp, w, m), v: dpack(od, m), a: 0, q: q_loop };
    if temp == 0 {
        lemma_guard_exit(tm, w, dpack(od, m), q_loop, q_guard, q_exit, i_peek, i_exit);
        lemma_dec_u_zero(w, m);
        assert(pow_nat(m, 0) == 1);
        assert(1nat * w == w) by(nonlinear_arith);
        assert(seq_pow(blk, 0) =~= Seq::<nat>::empty());
        assert(od + seq_pow(blk, 0) =~= od);
        assert(dec_u(0, (pow_nat(m, 0) * w) as nat, m) == w) by { lemma_dec_u_zero(w, m); }
        assert(loop_fuel_b3(od.len(), 0) == 2);
    } else {
        // ── continue guard (2 steps) → q_iter ──
        lemma_guard_continue(tm, temp, w, dpack(od, m), q_loop, q_guard, q_iter, i_peek, i_cont);
        let c1 = TmConfig { u: dec_u(temp, w, m), v: dpack(od, m), a: 0, q: q_iter };
        assert(tm_run(tm, c0, 2) == c1);
        // ── body: output od ↦ od ++ [s0,s1,s2], temp ↦ temp − 1, w ↦ m·w; lands q_loop ──
        lemma_block_iter_block3(tm, temp, w, od, s0, s1, s2,
            q_iter, q_surge, q_e1, q_e2, q_eret, q_home, q_dwalk, q_disc, q_loop,
            i_pivot_r, ir1, ir2, ir3, ir4, i_e0, i_e1, i_e2, i_off_l, il1, il2, il3, il4,
            i_pivot, i_one_l, i_erase, i_disc, i_one_r);
        let od2 = od + blk;
        let c2 = TmConfig { u: dec_u((temp - 1) as nat, (m * w) as nat, m), v: dpack(od2, m), a: 0,
            q: q_loop };
        assert(tm_run(tm, c1, (2 * od.len() + 2 * temp + 10) as nat) == c2);
        assert(blk.len() == 3);
        assert forall|k: int| 0 <= k < od2.len() implies 1 <= #[trigger] od2[k] <= 4 by {
            if k < od.len() { assert(od2[k] == od[k]); } else { assert(od2[k] == blk[k - od.len()]); }
        }
        assert((m * w) % m == 0) by {
            assert(m * w == w * m) by(nonlinear_arith);
            lemma_div_mod_step(w, m, 0);
        }
        // ── recurse on (od2, temp − 1, m·w) ──
        lemma_block_loop_block3(tm, (temp - 1) as nat, (m * w) as nat, od2, s0, s1, s2,
            q_loop, q_guard, q_iter, q_surge, q_e1, q_e2, q_eret, q_home, q_dwalk, q_disc, q_exit,
            i_peek, i_cont, i_exit, i_pivot_r, ir1, ir2, ir3, ir4,
            i_e0, i_e1, i_e2, i_off_l, il1, il2, il3, il4, i_pivot, i_one_l, i_erase, i_disc, i_one_r);
        let c3 = TmConfig {
            u: dec_u(0, (pow_nat(m, (temp - 1) as nat) * (m * w)) as nat, m),
            v: dpack(od2 + seq_pow(blk, (temp - 1) as nat), m), a: 0, q: q_exit };
        assert(tm_run(tm, c2, loop_fuel_b3(od2.len(), (temp - 1) as nat)) == c3);
        lemma_pow_nat_unfold(m, temp);
        assert(pow_nat(m, (temp - 1) as nat) * (m * w) == pow_nat(m, temp) * w) by(nonlinear_arith)
            requires pow_nat(m, temp) == m * pow_nat(m, (temp - 1) as nat);
        assert(seq_pow(blk, temp) =~= blk + seq_pow(blk, (temp - 1) as nat));
        assert(od2 + seq_pow(blk, (temp - 1) as nat) =~= od + seq_pow(blk, temp)) by {
            assert(od2 + seq_pow(blk, (temp - 1) as nat) =~= od + (blk + seq_pow(blk, (temp - 1) as nat)));
        }
        assert(c3.u == dec_u(0, (pow_nat(m, temp) * w) as nat, m));
        assert(c3.v == dpack(od + seq_pow(blk, temp), m));
        // ── chain the fuel ──
        lemma_tm_run_split(tm, c0, 2, (2 * od.len() + 2 * temp + 10) as nat);
        assert((2 + (2 * od.len() + 2 * temp + 10)) as nat == (2 * od.len() + 2 * temp + 12) as nat);
        assert(tm_run(tm, c0, (2 * od.len() + 2 * temp + 12) as nat) == c2);
        lemma_tm_run_split(tm, c0, (2 * od.len() + 2 * temp + 12) as nat,
            loop_fuel_b3(od2.len(), (temp - 1) as nat));
        assert(od2.len() == od.len() + 3);
        assert((2 * od.len() + 2 * temp + 12 + loop_fuel_b3(od2.len(), (temp - 1) as nat)) as nat
            == loop_fuel_b3(od.len(), temp));
    }
}

} // verus!
