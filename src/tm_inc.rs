//! # GAP-2-E brick B3 (assembly) — the inc gadget
//!
//! Assembles the inc gadget from its four quintuples (`docs/gap2-register-to-tm-plan.md` B3): peel the
//! separator, walk the head left through the block (`lemma_walk_left_inner`), write the new `1` at the
//! turnaround, walk back (`lemma_walk_back_inner`). The result: from `two_counter_config(c1,c2,q_walk)`,
//! `2·(c1+1)` steps reach `two_counter_config(c1+1,c2,q_back)`. Chained with `lemma_tm_run_split`.
//!
//! Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use verus_group_theory::word_numbering::lemma_div_mod_step;
use crate::tm::{Tm, TmConfig, tm_wf, tm_step, tm_run, apply_quint};
use crate::tm_two_counter::{two_counter_config, repunit_m, sep,
    lemma_repunit_div_mod, lemma_repunit_step, lemma_repunit_zero};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};
use crate::tm_walk::{pile_ones, lemma_walk_left_inner, lemma_walk_back_inner, lemma_pile_ones_div_mod};
use crate::tm_run_lemmas::lemma_tm_run_split;

verus! {

/// **The inc gadget (B3).** From the head-on-separator layout in state `q_walk`, the four quintuples
///   `(q_walk, 2, 2, q_walk, L)`  peel separator,
///   `(q_walk, 1, 1, q_walk, L)`  walk left over block-1s,
///   `(q_walk, 0, 1, q_back, R)`  turnaround: write the new 1,
///   `(q_back, 1, 1, q_back, R)`  walk back,
/// run for `2·(c1+1)` steps and reach `two_counter_config(c1+1, c2, q_back)` — the left counter
/// incremented, the head back on the separator in the exit state `q_back`. Works for `c1 = 0`
/// (2 steps: peel onto the blank, turnaround pops the separator straight back).
pub proof fn lemma_inc(
    tm: Tm, c1: nat, c2: nat, q_walk: nat, q_back: nat,
    i_sep: int, i_one_l: int, i_turn: int, i_one_r: int,
)
    requires
        tm_wf(tm),
        tm.n >= 2,
        q_walk < tm.m,
        0 <= i_sep < tm.quints.len(),
        0 <= i_one_l < tm.quints.len(),
        0 <= i_turn < tm.quints.len(),
        0 <= i_one_r < tm.quints.len(),
        tm.quints[i_sep] == mk_quint(q_walk, sep(), sep(), q_walk, Dir::L),
        tm.quints[i_one_l] == mk_quint(q_walk, 1, 1, q_walk, Dir::L),
        tm.quints[i_turn] == mk_quint(q_walk, 0, 1, q_back, Dir::R),
        tm.quints[i_one_r] == mk_quint(q_back, 1, 1, q_back, Dir::R),
    ensures
        tm_run(tm, two_counter_config(c1, c2, q_walk, tm.m), (2 * c1 + 2) as nat)
            == two_counter_config((c1 + 1) as nat, c2, q_back, tm.m),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 2);   // tm_wf ⟹ 0 < n < m, n ≥ 2
    let c0 = two_counter_config(c1, c2, q_walk, m);
    let v1 = repunit_m(c2, m) * m + sep();   // the separator + c2 block, under the pile
    lemma_div_mod_step(repunit_m(c2, m), m, sep());   // v1 / m == repunit(c2), v1 % m == sep()
    lemma_repunit_zero(m);
    lemma_repunit_step(0, m);
    assert(repunit_m(1, m) == 1);

    if c1 == 0 {
        assert(c0.u == 0);   // repunit(0)
        // Step 1: sep-peel ⟹ c_sep == (0, v1, 0, q_walk).
        lemma_tm_step_picks(tm, c0, i_sep);
        let c_sep = apply_quint(tm.quints[i_sep], c0, m);
        assert(tm_step(tm, c0) == Some(c_sep));
        assert(0nat / m == 0) by(nonlinear_arith) requires m > 0;
        assert(0nat % m == 0) by(nonlinear_arith) requires m > 0;
        assert(c_sep.u == 0);
        assert(c_sep.v == v1);
        assert(c_sep.a == 0);
        assert(c_sep.q == q_walk);
        assert(tm_run(tm, c_sep, 0) == c_sep);
        assert(tm_run(tm, c0, 1) == c_sep);
        // Step 2: turnaround ⟹ c_turn == (1, repunit(c2), sep, q_back) == two_counter_config(1,c2,q_back).
        lemma_tm_step_picks(tm, c_sep, i_turn);
        let c_turn = apply_quint(tm.quints[i_turn], c_sep, m);
        assert(tm_step(tm, c_sep) == Some(c_turn));
        assert(0nat * m == 0) by(nonlinear_arith);
        let c_final = two_counter_config(1, c2, q_back, m);
        assert(c_turn.u == 1);
        assert(c_turn.v == repunit_m(c2, m));   // c_sep.v / m == v1 / m == repunit(c2)
        assert(c_turn.a == sep());              // c_sep.v % m == v1 % m == sep()
        assert(c_turn.q == q_back);
        assert(c_final.u == repunit_m(1, m));
        assert(c_turn == c_final);
        assert(tm_run(tm, c_turn, 0) == c_turn);
        assert(tm_run(tm, c_sep, 1) == c_turn);
        lemma_tm_run_split(tm, c0, 1, 1);
        assert((2 * c1 + 2) as nat == 2);
        assert(tm_run(tm, c0, 2) == c_final);
    } else {
        // Step 1: sep-peel ⟹ c_sep == (repunit(c1-1), v1, 1, q_walk).
        lemma_tm_step_picks(tm, c0, i_sep);
        let c_sep = apply_quint(tm.quints[i_sep], c0, m);
        assert(tm_step(tm, c0) == Some(c_sep));
        lemma_repunit_div_mod((c1 - 1) as nat, m);   // repunit(c1)/m == repunit(c1-1), %m == 1
        assert(((c1 - 1) as nat + 1) as nat == c1);
        assert(c_sep.u == repunit_m((c1 - 1) as nat, m));
        assert(c_sep.v == v1);
        assert(c_sep.a == 1);
        assert(c_sep.q == q_walk);
        assert(tm_run(tm, c_sep, 0) == c_sep);
        assert(tm_run(tm, c0, 1) == c_sep);

        // Step 2: walk-left ones-loop (c1 steps) ⟹ c_blank == (0, pile_ones(v1, c1), 0, q_walk).
        lemma_walk_left_inner(tm, c_sep, q_walk, (c1 - 1) as nat, i_one_l);
        let c_blank = (TmConfig { u: 0, v: pile_ones(v1, c1, m), a: 0, q: q_walk });
        assert(tm_run(tm, c_sep, c1) == c_blank);   // fuel (c1-1)+1 == c1; c_sep.v == v1
        lemma_tm_run_split(tm, c0, 1, c1);
        assert(tm_run(tm, c0, (1 + c1) as nat) == c_blank);

        // Step 3: turnaround (1 step) ⟹ c_turn == (1, pile_ones(v1, c1-1), 1, q_back).
        lemma_tm_step_picks(tm, c_blank, i_turn);
        let c_turn = apply_quint(tm.quints[i_turn], c_blank, m);
        assert(tm_step(tm, c_blank) == Some(c_turn));
        lemma_pile_ones_div_mod(v1, c1, m);   // pile_ones(v1,c1)%m == 1, /m == pile_ones(v1,c1-1)
        assert(0nat * m == 0) by(nonlinear_arith);
        assert(c_turn.u == 1);
        assert(c_turn.v == pile_ones(v1, (c1 - 1) as nat, m));
        assert(c_turn.a == 1);
        assert(c_turn.q == q_back);
        assert(tm_run(tm, c_turn, 0) == c_turn);
        assert(tm_run(tm, c_blank, 1) == c_turn);
        lemma_tm_run_split(tm, c0, (1 + c1) as nat, 1);
        assert(tm_run(tm, c0, (1 + c1 + 1) as nat) == c_turn);

        // Step 4: walk-back ones-loop (c1 steps) ⟹ c_final == two_counter_config(c1+1, c2, q_back).
        assert(c_turn.u == repunit_m(1, m));   // c_turn.u == 1 == repunit(1)
        lemma_walk_back_inner(tm, c_turn, q_back, 1, (c1 - 1) as nat, v1, i_one_r);
        assert((1 + (c1 - 1) + 1) as nat == (c1 + 1) as nat);
        let c_final = two_counter_config((c1 + 1) as nat, c2, q_back, m);
        assert(c_final.u == repunit_m((c1 + 1) as nat, m));
        assert(c_final.v == repunit_m(c2, m));   // v1 / m
        assert(c_final.a == sep());              // v1 % m
        assert(tm_run(tm, c_turn, c1) == c_final);
        lemma_tm_run_split(tm, c0, (1 + c1 + 1) as nat, c1);
        assert((1 + c1 + 1 + c1) as nat == (2 * c1 + 2) as nat);
        assert(tm_run(tm, c0, (2 * c1 + 2) as nat) == c_final);
    }
}

} // verus!
