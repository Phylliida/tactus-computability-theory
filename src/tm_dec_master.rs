//! # GAP-2 G2-F Route (i) brick R-relnum-gen (STEP 2, model B) — the master-decrement foundation.
//!
//! Model B's per-block loop decrements a master counter (`iₐ` or `i_b`) at "home" each iteration. The
//! home layout is `[iₐ ones] 0 [i_b ones] 0 [output] 0 [blanks]`, head on the pivot `0` before the output.
//! Decrementing `i_b` mirrors [`crate::tm_dec::lemma_dec`] (walk out over `i_b`'s ones, erase the OUTER
//! one at the `i_b/iₐ` separator, walk back — keeping `i_b` adjacent to the pivot, no gap growth), with one
//! twist: the left tape is NOT a bare counter, it carries `iₐ`'s content beyond the `i_b/iₐ` separator. So
//! the walk-left must STOP at that separator and LEAVE the high content intact, unlike
//! [`crate::tm_walk::lemma_walk_left_inner`] (which assumes the rest of `u` is blank and lands `u == 0`).
//!
//! This file is the foundation: [`lemma_walk_left_prefix`], the generalized walk-left over a `repunit`
//! PREFIX with an arbitrary high tail `w` left in `u`. The walk-BACK reuses
//! [`crate::tm_walk::lemma_walk_back_inner`] verbatim (it is already generic in the under-pile content).
//! The full `dec_master` gadget + `home_config` build on this next.
//!
//! `docs/gap2-input-loader-plan.md` §5 (R-relnum-gen STEP 2, model B). Fully verified, no escape hatches.

use vstd::prelude::*;
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
use verus_group_theory::machine_group::Dir;
use verus_group_theory::word_numbering::lemma_div_mod_step;
use crate::tm::{Tm, TmConfig, tm_wf, tm_step, tm_run, apply_quint};
use crate::tm_two_counter::{repunit_m, lemma_repunit_zero, lemma_repunit_step};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};
use crate::tm_walk::{pile_ones, lemma_pile_ones_shift, lemma_pile_ones_div_mod};
use crate::tm_dstring::{pow_nat, lemma_pow_nat_unfold};
use crate::tm_run_lemmas::lemma_tm_run_split;

verus! {

/// The left-tape value of the home layout when the active temp counter holds `temp` ones with the
/// preserved high content `w` packed above (the `temp/master` separator + master): `dec_u(temp, w) =
/// repunit_m(temp) + m^temp·w`. Decrementing temp drops it to `dec_u(temp-1, m·w)` — `temp` shrinks while
/// `w`'s ABSOLUTE position `m^temp` stays put, so the implicit blank gap between temp and the master grows
/// by one (absorbed cleanly into `w ← m·w`, low digit still `0`).
pub open spec fn dec_u(temp: nat, w: nat, m: nat) -> nat {
    repunit_m(temp, m) + pow_nat(m, temp) * w
}

/// **Generalized walk-left over a `repunit` prefix with a high tail `w`.** From a config in state
/// `q_walk` scanning a `1`, with `j0` further ones and then the tail `w` packed above them in `u`
/// (`u == repunit_m(j0) + pow_nat(m, j0)·w`), the loop quintuple `(q_walk, 1, 1, q_walk, L)` fires
/// `j0 + 1` times — peeling the scanned `1` and the `j0` ones, piling all `j0 + 1` onto `v` — and lands
/// the head on `w`'s low cell (`a == w % m`, `u == w / m`), still in `q_walk`. The `dec_master` analog of
/// [`crate::tm_walk::lemma_walk_left_inner`]: instead of assuming the rest of `u` is blank (landing
/// `u == 0`), it LEAVES the high tail `w` intact. The caller sets `w % m == 0` (the `i_b/iₐ` separator
/// blank) so the head stops on a blank, where the erase-turnaround then fires. Induction on `j0`.
pub proof fn lemma_walk_left_prefix(tm: Tm, c: TmConfig, q_walk: nat, j0: nat, w: nat, i1: int)
    requires
        tm_wf(tm),
        0 <= i1 < tm.quints.len(),
        tm.quints[i1] == mk_quint(q_walk, 1, 1, q_walk, Dir::L),
        c.u == repunit_m(j0, tm.m) + pow_nat(tm.m, j0) * w,
        c.a == 1,
        c.q == q_walk,
    ensures
        tm_run(tm, c, (j0 + 1) as nat)
            == (TmConfig { u: w / tm.m, v: pile_ones(c.v, (j0 + 1) as nat, tm.m),
                a: w % tm.m, q: q_walk }),
    decreases j0,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1);   // tm_wf ⟹ 0 < n < m
    // the loop quintuple matches (q == q_walk, a == 1) and fires (L-move, a2 == 1).
    lemma_tm_step_picks(tm, c, i1);
    let c_next = TmConfig { u: c.u / m, v: c.v * m + 1, a: c.u % m, q: q_walk };
    assert(tm_step(tm, c) == Some(c_next));
    if j0 == 0 {
        // u == repunit(0) + pow_nat(m,0)·w == 0 + 1·w == w.
        assert(pow_nat(m, 0) == 1);
        lemma_repunit_zero(m);
        assert(1nat * w == w) by(nonlinear_arith);
        assert(c.u == w);
        // c_next == (w/m, pile_ones(c.v,1), w%m, q_walk).
        assert(pile_ones(c.v, 0, m) == c.v);
        assert(pile_ones(c.v, 1, m) == pile_ones(c.v, 0, m) * m + 1);
        assert(c_next == (TmConfig { u: w / m, v: pile_ones(c.v, 1, m), a: w % m, q: q_walk }));
        assert(tm_run(tm, c_next, 0) == c_next);
        assert(tm_run(tm, c, 1) == c_next);
    } else {
        // u == repunit(j0) + m^j0·w == (repunit(j0-1) + m^(j0-1)·w)·m + 1.
        let x = repunit_m((j0 - 1) as nat, m) + pow_nat(m, (j0 - 1) as nat) * w;
        assert(repunit_m(j0, m) == m * repunit_m((j0 - 1) as nat, m) + 1);   // repunit recurrence
        lemma_pow_nat_unfold(m, j0);                                         // m^j0 == m·m^(j0-1)
        assert(c.u == x * m + 1) by(nonlinear_arith)
            requires
                c.u == repunit_m(j0, m) + pow_nat(m, j0) * w,
                repunit_m(j0, m) == m * repunit_m((j0 - 1) as nat, m) + 1,
                pow_nat(m, j0) == m * pow_nat(m, (j0 - 1) as nat),
                x == repunit_m((j0 - 1) as nat, m) + pow_nat(m, (j0 - 1) as nat) * w;
        lemma_div_mod_step(x, m, 1);   // (x·m + 1)/m == x, %m == 1
        assert(c_next.u == x);
        assert(c_next.a == 1);
        lemma_walk_left_prefix(tm, c_next, q_walk, (j0 - 1) as nat, w, i1);
        // IH: tm_run(c_next, j0) == (w/m, pile_ones(c.v·m+1, j0), w%m, q_walk).
        lemma_pile_ones_shift(c.v, j0, m);   // pile_ones(c.v·m+1, j0) == pile_ones(c.v, j0+1)
        assert(tm_run(tm, c, (j0 + 1) as nat) == tm_run(tm, c_next, j0));
    }
}

/// **Generalized walk-back-right over a pile, preserving a high tail `w_hi` in `u`.** The back-direction
/// twin of [`lemma_walk_left_prefix`] (and the generalization of [`crate::tm_walk::lemma_walk_back_inner`]
/// that carries the preserved high content `w_hi`). From a config in state `q_back` scanning a `1`, with
/// `k0` ones already reconstructed atop `w_hi` in `u` (`u == repunit_m(k0) + pow_nat(m,k0)·w_hi`) and a
/// pile of `rem0` ones above `w_pile` in `v` (`v == pile_ones(w_pile, rem0)`), the `(q_back, 1, 1, q_back,
/// R)` step fires `rem0 + 1` times — writing each `1` back onto `u`'s low end (pushing `w_hi` up) and
/// popping the pile — landing `u == repunit_m(k0 + rem0 + 1) + pow_nat(m, k0+rem0+1)·w_hi` with the head on
/// `w_pile`'s low cell (`a == w_pile % m`, `v == w_pile / m`). The walk-BACK of `dec_temp` (reconstructs
/// the decremented temp counter while leaving the master `w_hi` intact — though shifted up by the gap the
/// erase/discard introduced). Induction on `rem0`, mirroring `lemma_walk_back_inner`.
pub proof fn lemma_walk_back_prefix(
    tm: Tm, c: TmConfig, q_back: nat, k0: nat, rem0: nat, w_pile: nat, w_hi: nat, i1b: int,
)
    requires
        tm_wf(tm),
        0 <= i1b < tm.quints.len(),
        tm.quints[i1b] == mk_quint(q_back, 1, 1, q_back, Dir::R),
        c.u == repunit_m(k0, tm.m) + pow_nat(tm.m, k0) * w_hi,
        c.v == pile_ones(w_pile, rem0, tm.m),
        c.a == 1,
        c.q == q_back,
    ensures
        tm_run(tm, c, (rem0 + 1) as nat)
            == (TmConfig {
                u: repunit_m((k0 + rem0 + 1) as nat, tm.m)
                    + pow_nat(tm.m, (k0 + rem0 + 1) as nat) * w_hi,
                v: w_pile / tm.m, a: w_pile % tm.m, q: q_back }),
    decreases rem0,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 1);
    lemma_tm_step_picks(tm, c, i1b);
    let c_next = TmConfig { u: c.u * m + 1, v: c.v / m, a: c.v % m, q: q_back };
    assert(tm_step(tm, c) == Some(c_next));
    // c_next.u == repunit(k0+1) + m^(k0+1)·w_hi.
    let nk = (k0 + 1) as nat;
    assert(repunit_m(nk, m) == m * repunit_m(k0, m) + 1);   // repunit recurrence
    lemma_pow_nat_unfold(m, nk);                            // m^(k0+1) == m·m^k0
    assert(c_next.u == repunit_m(nk, m) + pow_nat(m, nk) * w_hi) by(nonlinear_arith)
        requires
            c.u == repunit_m(k0, m) + pow_nat(m, k0) * w_hi,
            c_next.u == c.u * m + 1,
            repunit_m(nk, m) == m * repunit_m(k0, m) + 1,
            pow_nat(m, nk) == m * pow_nat(m, k0);
    if rem0 == 0 {
        // c.v == pile_ones(w_pile, 0) == w_pile.
        assert(pile_ones(w_pile, 0, m) == w_pile);
        assert((k0 + 0 + 1) as nat == nk);
        assert(c_next == (TmConfig {
            u: repunit_m(nk, m) + pow_nat(m, nk) * w_hi, v: w_pile / m, a: w_pile % m, q: q_back }));
        assert(tm_run(tm, c_next, 0) == c_next);
        assert(tm_run(tm, c, 1) == c_next);
    } else {
        // pop a pile-one: c.v % m == 1, c.v / m == pile_ones(w_pile, rem0-1).
        lemma_pile_ones_div_mod(w_pile, rem0, m);
        assert(c_next.a == 1);
        assert(c_next.v == pile_ones(w_pile, (rem0 - 1) as nat, m));
        lemma_walk_back_prefix(tm, c_next, q_back, nk, (rem0 - 1) as nat, w_pile, w_hi, i1b);
        // IH: lands u == repunit((k0+1)+(rem0-1)+1) + m^(...)·w_hi == repunit(k0+rem0+1) + m^(k0+rem0+1)·w_hi.
        assert(((k0 + 1) + (rem0 - 1) + 1) as nat == (k0 + rem0 + 1) as nat);
        assert(tm_run(tm, c, (rem0 + 1) as nat) == tm_run(tm, c_next, rem0));
    }
}

/// **The `dec_temp` gadget — decrement the active temp counter at home, return to the home pivot.** The
/// model-B master-decrement: the home layout is `[master]0[temp]0[output]0[blanks]` with the head on the
/// pivot `0` before the output. Five quintuples (the analog of [`crate::tm_dec::lemma_dec`], with a DISTINCT
/// `q_home` for the pivot-peel — both pivot-peel and erase scan `0`, so they need different states, unlike
/// `lemma_dec` whose sep-peel scans `2`):
///   `(q_home, 0, 0, q_walk, L)`  peel the pivot (push it onto v, expose temp's inner one),
///   `(q_walk, 1, 1, q_walk, L)`  walk left over temp's ones to the temp/master separator,
///   `(q_walk, 0, 0, q_disc, R)`  erase-turnaround at the separator,
///   `(q_disc, 1, 0, q_back, R)`  discard the outermost temp one,
///   `(q_back, 1, 1, q_back, R)`  walk back, reconstructing temp−1 (master `w` preserved, shifted up).
/// From `{u: dec_u(temp, w), v: output_val, a: 0, q_home}`, `2·temp + 2` steps reach
/// `{u: dec_u(temp−1, m·w), v: output_val, a: 0, q_back}` — `temp` decremented, the master `w` and the
/// output untouched, head back on the pivot. Composes [`lemma_walk_left_prefix`] + [`lemma_walk_back_prefix`]
/// (the walk-out/back over temp leaving `w` intact); the output `v` round-trips (pushed onto the pile,
/// restored) exactly as in `lemma_dec`.
pub proof fn lemma_dec_temp(
    tm: Tm, temp: nat, w: nat, output_val: nat,
    q_home: nat, q_walk: nat, q_disc: nat, q_back: nat,
    i_pivot: int, i_one_l: int, i_erase: int, i_disc: int, i_one_r: int,
)
    requires
        tm_wf(tm),
        tm.n >= 2,
        temp >= 1,
        w % tm.m == 0,
        0 <= i_pivot < tm.quints.len(),
        0 <= i_one_l < tm.quints.len(),
        0 <= i_erase < tm.quints.len(),
        0 <= i_disc < tm.quints.len(),
        0 <= i_one_r < tm.quints.len(),
        tm.quints[i_pivot] == mk_quint(q_home, 0, 0, q_walk, Dir::L),
        tm.quints[i_one_l] == mk_quint(q_walk, 1, 1, q_walk, Dir::L),
        tm.quints[i_erase] == mk_quint(q_walk, 0, 0, q_disc, Dir::R),
        tm.quints[i_disc] == mk_quint(q_disc, 1, 0, q_back, Dir::R),
        tm.quints[i_one_r] == mk_quint(q_back, 1, 1, q_back, Dir::R),
    ensures
        tm_run(tm,
            TmConfig { u: dec_u(temp, w, tm.m), v: output_val, a: 0, q: q_home },
            (2 * temp + 2) as nat)
            == (TmConfig { u: dec_u((temp - 1) as nat, (tm.m * w) as nat, tm.m), v: output_val, a: 0,
                q: q_back }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 2);   // tm_wf ⟹ 0 < n < m, n ≥ 2
    let c0 = TmConfig { u: dec_u(temp, w, m), v: output_val, a: 0, q: q_home };
    let v1 = output_val * m;   // the output with the pivot 0 pushed on top
    lemma_div_mod_step(output_val, m, 0);   // v1/m == output_val, v1%m == 0
    assert(output_val * m + 0 == v1);

    // w == (w/m)·m  (w%m == 0).
    lemma_fundamental_div_mod(w as int, m as int);
    assert(w == m * (w / m)) by { assert(w % m == 0); }
    assert(m * (w / m) == (w / m) * m) by(nonlinear_arith);

    // ── Step 1: peel the pivot (q_home, 0, 0, q_walk, L). ──
    // u0 == repunit(temp) + m^temp·w == (repunit(temp-1) + m^(temp-1)·w)·m + 1.
    let ux = repunit_m((temp - 1) as nat, m) + pow_nat(m, (temp - 1) as nat) * w;
    assert(repunit_m(temp, m) == m * repunit_m((temp - 1) as nat, m) + 1);
    lemma_pow_nat_unfold(m, temp);   // m^temp == m·m^(temp-1)
    assert(dec_u(temp, w, m) == ux * m + 1) by(nonlinear_arith)
        requires
            dec_u(temp, w, m) == repunit_m(temp, m) + pow_nat(m, temp) * w,
            repunit_m(temp, m) == m * repunit_m((temp - 1) as nat, m) + 1,
            pow_nat(m, temp) == m * pow_nat(m, (temp - 1) as nat),
            ux == repunit_m((temp - 1) as nat, m) + pow_nat(m, (temp - 1) as nat) * w;
    lemma_div_mod_step(ux, m, 1);   // u0/m == ux, u0%m == 1
    lemma_tm_step_picks(tm, c0, i_pivot);
    let c_peel = apply_quint(tm.quints[i_pivot], c0, m);
    assert(tm_step(tm, c0) == Some(c_peel));
    // L-move, a2 == 0: u' = u0/m == ux, v' = v0·m + 0 == v1, a' = u0%m == 1.
    assert(c_peel.u == ux);
    assert(c_peel.v == v1);
    assert(c_peel.a == 1);
    assert(c_peel.q == q_walk);
    assert(tm_run(tm, c_peel, 0) == c_peel);
    assert(tm_run(tm, c0, 1) == c_peel);

    // ── Step 2: walk-left over temp's ones (temp steps) to the temp/master separator. ──
    lemma_walk_left_prefix(tm, c_peel, q_walk, (temp - 1) as nat, w, i_one_l);
    let c_sep = TmConfig { u: w / m, v: pile_ones(v1, temp, m), a: w % m, q: q_walk };
    assert(((temp - 1) + 1) as nat == temp);
    assert(tm_run(tm, c_peel, temp) == c_sep);
    lemma_tm_run_split(tm, c0, 1, temp);
    assert(tm_run(tm, c0, (1 + temp) as nat) == c_sep);

    // ── Step 3: erase-turnaround at the separator (a == w%m == 0). ──
    assert(c_sep.a == 0);   // w % m == 0
    lemma_tm_step_picks(tm, c_sep, i_erase);
    let c_erase = apply_quint(tm.quints[i_erase], c_sep, m);
    assert(tm_step(tm, c_sep) == Some(c_erase));
    lemma_pile_ones_div_mod(v1, temp, m);   // pile_ones(v1,temp)%m==1, /m==pile_ones(v1,temp-1)
    // R-move, a2 == 0: u'' = (w/m)·m + 0 == w, v'' = pile_ones(v1,temp)/m, a'' = pile_ones(v1,temp)%m == 1.
    assert(c_erase.u == w);
    assert(c_erase.v == pile_ones(v1, (temp - 1) as nat, m));
    assert(c_erase.a == 1);
    assert(c_erase.q == q_disc);
    assert(tm_run(tm, c_erase, 0) == c_erase);
    assert(tm_run(tm, c_sep, 1) == c_erase);
    lemma_tm_run_split(tm, c0, (1 + temp) as nat, 1);
    assert(tm_run(tm, c0, (1 + temp + 1) as nat) == c_erase);

    // ── Step 4: discard the popped (outermost temp) one. ──
    lemma_tm_step_picks(tm, c_erase, i_disc);
    let c_disc = apply_quint(tm.quints[i_disc], c_erase, m);
    assert(tm_step(tm, c_erase) == Some(c_disc));
    // R-move, a2 == 0: u''' = w·m, v''' = pile_ones(v1,temp-1)/m, a''' = pile_ones(v1,temp-1)%m.
    assert(c_disc.u == w * m);
    assert(c_disc.q == q_back);
    assert(tm_run(tm, c_disc, 0) == c_disc);
    assert(tm_run(tm, c_erase, 1) == c_disc);
    lemma_tm_run_split(tm, c0, (1 + temp + 1) as nat, 1);
    assert(tm_run(tm, c0, (1 + temp + 1 + 1) as nat) == c_disc);

    if temp == 1 {
        // c_erase.v == pile_ones(v1, 0) == v1; discard pops v1 ⟹ c_disc == {w·m, output_val, 0, q_back}.
        assert(pile_ones(v1, 0, m) == v1);
        assert(c_disc.v == output_val);   // v1 / m
        assert(c_disc.a == 0);            // v1 % m
        // dec_u(0, m·w) == repunit(0) + m^0·(m·w) == m·w == w·m.
        assert(pow_nat(m, 0) == 1);
        lemma_repunit_zero(m);
        assert(1nat * (m * w) == m * w) by(nonlinear_arith);
        assert(m * w == w * m) by(nonlinear_arith);
        assert(c_disc == (TmConfig { u: dec_u(0, (m * w) as nat, m), v: output_val, a: 0, q: q_back }));
        assert((2 * temp + 2) as nat == (1 + temp + 1 + 1) as nat);
        assert(tm_run(tm, c0, (2 * temp + 2) as nat) == c_disc);
    } else {
        // temp ≥ 2: c_erase.v == pile_ones(v1, temp-1) with temp-1 ≥ 1; discard pops a one.
        lemma_pile_ones_div_mod(v1, (temp - 1) as nat, m);
        assert(c_disc.v == pile_ones(v1, (temp - 2) as nat, m));
        assert(c_disc.a == 1);
        // walk-back (temp-1 steps): k0 = 0, rem0 = temp-2, w_hi = w·m. u == w·m == repunit(0)+m^0·(w·m).
        assert(pow_nat(m, 0) == 1);
        lemma_repunit_zero(m);
        assert(c_disc.u == repunit_m(0, m) + pow_nat(m, 0) * (w * m)) by(nonlinear_arith)
            requires c_disc.u == w * m, repunit_m(0, m) == 0, pow_nat(m, 0) == 1;
        lemma_walk_back_prefix(tm, c_disc, q_back, 0, (temp - 2) as nat, v1, (w * m) as nat, i_one_r);
        let c_final = TmConfig {
            u: repunit_m((temp - 1) as nat, m) + pow_nat(m, (temp - 1) as nat) * (w * m),
            v: v1 / m, a: v1 % m, q: q_back };
        assert((0 + (temp - 2) + 1) as nat == (temp - 1) as nat);
        assert(tm_run(tm, c_disc, (temp - 1) as nat) == c_final);
        // c_final == dec_u(temp-1, m·w): repunit(temp-1) + m^(temp-1)·(w·m) == repunit(temp-1) + m^temp·w·...
        //   == dec_u(temp-1, m·w) since m^(temp-1)·(w·m) == pow_nat(m,temp-1)·(m·w).
        assert(w * m == m * w) by(nonlinear_arith);
        assert(c_final.v == output_val);   // v1 / m
        assert(c_final.a == 0);            // v1 % m
        assert(c_final == (TmConfig { u: dec_u((temp - 1) as nat, (m * w) as nat, m), v: output_val,
            a: 0, q: q_back }));
        lemma_tm_run_split(tm, c0, (1 + temp + 1 + 1) as nat, (temp - 1) as nat);
        assert((1 + temp + 1 + 1 + (temp - 1)) as nat == (2 * temp + 2) as nat);
        assert(tm_run(tm, c0, (2 * temp + 2) as nat) == c_final);
    }
}

} // verus!
