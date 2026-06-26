//! # GAP-2-E brick B4 — the dec gadget
//!
//! The mirror of the inc gadget (`docs/gap2-register-to-tm-plan.md` B4), for `c1 ≥ 1`: walk the head
//! left **to the blank** (reusing `lemma_walk_left_inner`), then erase the outermost `1` — which the
//! walk-out conveniently left as the pile's low digit. Erasing pops that `1` into the scanned cell, so a
//! **discard** step drops it (writes `0`, doesn't push it back), then `lemma_walk_back_inner`
//! reconstructs `u = repunit(c1−1)`. For `c1 = 1` the discard pops the separator straight back (no
//! walk-back). From `two_counter_config(c1,c2,q_walk)`, `2·(c1+1)` steps reach
//! `two_counter_config(c1−1,c2,q_back)`. (DecJump folds the B2 zero-test for the `c1 = 0` jump.)
//!
//! Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use verus_group_theory::word_numbering::lemma_div_mod_step;
use crate::tm::{Tm, TmConfig, tm_wf, tm_step, tm_run, apply_quint};
use crate::tm_two_counter::{two_counter_config, repunit_m, sep, lemma_repunit_div_mod, lemma_repunit_zero};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};
use crate::tm_walk::{pile_ones, lemma_walk_left_inner, lemma_walk_back_inner, lemma_pile_ones_div_mod};
use crate::tm_run_lemmas::lemma_tm_run_split;

verus! {

/// **The dec gadget (B4).** Five quintuples:
///   `(q_walk, 2, 2, q_walk, L)`  peel separator,
///   `(q_walk, 1, 1, q_walk, L)`  walk left to the blank,
///   `(q_walk, 0, 0, q_disc, R)`  erase-turnaround: write 0 (the outer 1 pops into scanned),
///   `(q_disc, 1, 0, q_back, R)`  discard that popped 1,
///   `(q_back, 1, 1, q_back, R)`  walk back.
/// For `c1 ≥ 1`, `2·(c1+1)` steps reach `two_counter_config(c1−1, c2, q_back)`.
pub proof fn lemma_dec(
    tm: Tm, c1: nat, c2: nat, q_walk: nat, q_disc: nat, q_back: nat,
    i_sep: int, i_one_l: int, i_turn: int, i_disc: int, i_one_r: int,
)
    requires
        tm_wf(tm),
        tm.n >= 2,
        q_walk < tm.m,
        c1 >= 1,
        0 <= i_sep < tm.quints.len(),
        0 <= i_one_l < tm.quints.len(),
        0 <= i_turn < tm.quints.len(),
        0 <= i_disc < tm.quints.len(),
        0 <= i_one_r < tm.quints.len(),
        tm.quints[i_sep] == mk_quint(q_walk, sep(), sep(), q_walk, Dir::L),
        tm.quints[i_one_l] == mk_quint(q_walk, 1, 1, q_walk, Dir::L),
        tm.quints[i_turn] == mk_quint(q_walk, 0, 0, q_disc, Dir::R),
        tm.quints[i_disc] == mk_quint(q_disc, 1, 0, q_back, Dir::R),
        tm.quints[i_one_r] == mk_quint(q_back, 1, 1, q_back, Dir::R),
    ensures
        tm_run(tm, two_counter_config(c1, c2, q_walk, tm.m), (2 * c1 + 2) as nat)
            == two_counter_config((c1 - 1) as nat, c2, q_back, tm.m),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 2);
    let c0 = two_counter_config(c1, c2, q_walk, m);
    let v1 = repunit_m(c2, m) * m + sep();
    lemma_div_mod_step(repunit_m(c2, m), m, sep());   // v1 / m == repunit(c2), v1 % m == sep()
    lemma_repunit_zero(m);

    // Step 1: sep-peel ⟹ c_sep == (repunit(c1-1), v1, 1, q_walk).
    lemma_tm_step_picks(tm, c0, i_sep);
    let c_sep = apply_quint(tm.quints[i_sep], c0, m);
    assert(tm_step(tm, c0) == Some(c_sep));
    lemma_repunit_div_mod((c1 - 1) as nat, m);
    assert(((c1 - 1) as nat + 1) as nat == c1);
    assert(c_sep.u == repunit_m((c1 - 1) as nat, m));
    assert(c_sep.v == v1);
    assert(c_sep.a == 1);
    assert(c_sep.q == q_walk);
    assert(tm_run(tm, c_sep, 0) == c_sep);
    assert(tm_run(tm, c0, 1) == c_sep);

    // Step 2: walk-left to blank (c1 steps) ⟹ c_blank == (0, pile_ones(v1, c1), 0, q_walk).
    lemma_walk_left_inner(tm, c_sep, q_walk, (c1 - 1) as nat, i_one_l);
    let c_blank = (TmConfig { u: 0, v: pile_ones(v1, c1, m), a: 0, q: q_walk });
    assert(tm_run(tm, c_sep, c1) == c_blank);
    lemma_tm_run_split(tm, c0, 1, c1);
    assert(tm_run(tm, c0, (1 + c1) as nat) == c_blank);

    // Step 3: erase-turnaround ⟹ c_erase == (0, pile_ones(v1, c1-1), 1, q_disc).
    lemma_tm_step_picks(tm, c_blank, i_turn);
    let c_erase = apply_quint(tm.quints[i_turn], c_blank, m);
    assert(tm_step(tm, c_blank) == Some(c_erase));
    lemma_pile_ones_div_mod(v1, c1, m);
    assert(0nat * m == 0) by(nonlinear_arith);
    assert(c_erase.u == 0);
    assert(c_erase.v == pile_ones(v1, (c1 - 1) as nat, m));
    assert(c_erase.a == 1);
    assert(c_erase.q == q_disc);
    assert(tm_run(tm, c_erase, 0) == c_erase);
    assert(tm_run(tm, c_blank, 1) == c_erase);
    lemma_tm_run_split(tm, c0, (1 + c1) as nat, 1);
    assert(tm_run(tm, c0, (1 + c1 + 1) as nat) == c_erase);

    // Step 4: discard ⟹ c_disc (v/a case-split on c1).
    lemma_tm_step_picks(tm, c_erase, i_disc);
    let c_disc = apply_quint(tm.quints[i_disc], c_erase, m);
    assert(tm_step(tm, c_erase) == Some(c_disc));
    assert(0nat * m == 0) by(nonlinear_arith);
    assert(c_disc.u == 0);
    assert(c_disc.q == q_back);
    assert(tm_run(tm, c_disc, 0) == c_disc);
    assert(tm_run(tm, c_erase, 1) == c_disc);
    lemma_tm_run_split(tm, c0, (1 + c1 + 1) as nat, 1);
    assert(tm_run(tm, c0, (1 + c1 + 1 + 1) as nat) == c_disc);

    if c1 == 1 {
        // c_erase.v == pile_ones(v1, 0) == v1; discard pops v1 ⟹ c_disc == (0, repunit(c2), sep, q_back).
        assert(pile_ones(v1, 0, m) == v1);
        assert(c_disc.v == repunit_m(c2, m));   // v1 / m
        assert(c_disc.a == sep());              // v1 % m
        let c_final = two_counter_config(0, c2, q_back, m);
        assert(c_final.u == repunit_m(0, m));
        assert(c_disc == c_final);
        assert((2 * c1 + 2) as nat == (1 + c1 + 1 + 1) as nat);
        assert(tm_run(tm, c0, (2 * c1 + 2) as nat) == c_final);
    } else {
        // c1 ≥ 2: c_erase.v == pile_ones(v1, c1-1) with c1-1 ≥ 1; discard pops a one.
        lemma_pile_ones_div_mod(v1, (c1 - 1) as nat, m);
        assert(c_disc.v == pile_ones(v1, (c1 - 2) as nat, m));
        assert(c_disc.a == 1);
        assert(c_disc.u == repunit_m(0, m));
        // walk-back (c1-1 steps): k0 = 0, rem0 = c1-2.
        lemma_walk_back_inner(tm, c_disc, q_back, 0, (c1 - 2) as nat, v1, i_one_r);
        assert((0 + (c1 - 2) + 1) as nat == (c1 - 1) as nat);
        let c_final = two_counter_config((c1 - 1) as nat, c2, q_back, m);
        assert(c_final.u == repunit_m((c1 - 1) as nat, m));
        assert(c_final.v == repunit_m(c2, m));   // v1 / m
        assert(c_final.a == sep());              // v1 % m
        assert(tm_run(tm, c_disc, (c1 - 1) as nat) == c_final);
        lemma_tm_run_split(tm, c0, (1 + c1 + 1 + 1) as nat, (c1 - 1) as nat);
        assert((1 + c1 + 1 + 1 + (c1 - 1)) as nat == (2 * c1 + 2) as nat);
        assert(tm_run(tm, c0, (2 * c1 + 2) as nat) == c_final);
    }
}

} // verus!
