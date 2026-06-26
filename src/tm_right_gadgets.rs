//! # GAP-2-E brick B5.2 — the right-counter gadgets (peek / inc / dec)
//!
//! The `u ↔ v`, `L ↔ R` mirrors of `tm_gadget::lemma_peek_gadget`, `tm_inc::lemma_inc`,
//! `tm_dec::lemma_dec`, operating on the **right** counter `c2` (stored in `v`). They walk the head
//! right into the `c2` block via `Dir::R` (piling peeled `1`s onto `u`) and back left via `Dir::L`,
//! using the right walk loops from `tm_walk_right.rs`. The separator + `c1` block sits under the pile
//! as `u1 = repunit_m(c1)·m + 2` (the mirror of inc/dec's `v1`).
//!
//! Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use verus_group_theory::word_numbering::lemma_div_mod_step;
use crate::tm::{Tm, TmConfig, tm_wf, tm_step, tm_run, apply_quint};
use crate::tm_two_counter::{two_counter_config, repunit_m, sep,
    lemma_repunit_div_mod, lemma_repunit_step, lemma_repunit_zero};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};
use crate::tm_walk::{pile_ones, lemma_pile_ones_div_mod};
use crate::tm_walk_right::{lemma_walk_right_inner, lemma_walk_back_left_inner};
use crate::tm_run_lemmas::lemma_tm_run_split;

verus! {

/// **The right-counter peek gadget** (mirror of `lemma_peek_gadget`). From the head-on-separator
/// layout in state `q_entry`, two steps — `R` to expose the right block's inner cell, `L` to write it
/// back — restore the config and land in `q_pos` if `c2 > 0` or `q_zero` if `c2 = 0`. Quintuples:
///   `(q_entry, 2, 2, q_branch, R)`, `(q_branch, 1, 1, q_pos, L)`, `(q_branch, 0, 0, q_zero, L)`.
pub proof fn lemma_peek_right(
    tm: Tm, c1: nat, c2: nat,
    q_entry: nat, q_branch: nat, q_pos: nat, q_zero: nat,
    i_entry: int, i_pos: int, i_zero: int,
)
    requires
        tm_wf(tm),
        tm.n >= 2,
        q_entry < tm.m,
        0 <= i_entry < tm.quints.len(),
        0 <= i_pos < tm.quints.len(),
        0 <= i_zero < tm.quints.len(),
        tm.quints[i_entry] == mk_quint(q_entry, sep(), sep(), q_branch, Dir::R),
        tm.quints[i_pos] == mk_quint(q_branch, 1, 1, q_pos, Dir::L),
        tm.quints[i_zero] == mk_quint(q_branch, 0, 0, q_zero, Dir::L),
    ensures
        c2 > 0 ==> tm_run(tm, two_counter_config(c1, c2, q_entry, tm.m), 2)
                    == two_counter_config(c1, c2, q_pos, tm.m),
        c2 == 0 ==> tm_run(tm, two_counter_config(c1, c2, q_entry, tm.m), 2)
                    == two_counter_config(c1, c2, q_zero, tm.m),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 2);
    let c_entry = two_counter_config(c1, c2, q_entry, m);
    lemma_tm_step_picks(tm, c_entry, i_entry);
    let c_branch = apply_quint(tm.quints[i_entry], c_entry, m);
    assert(tm_step(tm, c_entry) == Some(c_branch));
    // c_branch (R-move): (repunit(c1)*m + 2, repunit(c2)/m, repunit(c2)%m, q_branch).
    assert(c_branch.u == repunit_m(c1, m) * m + sep());
    assert(c_branch.v == repunit_m(c2, m) / m);
    assert(c_branch.a == repunit_m(c2, m) % m);
    assert(c_branch.q == q_branch);
    // u restores: (repunit(c1)*m + 2)/m == repunit(c1), %m == 2.
    lemma_div_mod_step(repunit_m(c1, m), m, sep());

    if c2 > 0 {
        lemma_repunit_div_mod((c2 - 1) as nat, m);
        assert(((c2 - 1) as nat + 1) as nat == c2);
        assert(c_branch.v == repunit_m((c2 - 1) as nat, m));
        assert(c_branch.a == 1);
        lemma_tm_step_picks(tm, c_branch, i_pos);
        let c_final = apply_quint(tm.quints[i_pos], c_branch, m);
        assert(tm_step(tm, c_branch) == Some(c_final));
        // c_final (L-move): (u/m, v*m + 1, u%m, q_pos).
        lemma_repunit_step((c2 - 1) as nat, m);
        assert(repunit_m(c2, m) == m * repunit_m((c2 - 1) as nat, m) + 1);
        assert(repunit_m((c2 - 1) as nat, m) * m == m * repunit_m((c2 - 1) as nat, m)) by(nonlinear_arith);
        assert(c_final.v == repunit_m(c2, m));
        assert(c_final.u == repunit_m(c1, m));
        assert(c_final.a == sep());
        assert(c_final.q == q_pos);
        assert(c_final == two_counter_config(c1, c2, q_pos, m));
        assert(tm_run(tm, c_final, 0) == c_final);
        assert(tm_run(tm, c_branch, 1) == c_final);
        assert(tm_run(tm, c_entry, 2) == c_final);
    } else {
        lemma_repunit_zero(m);
        assert(repunit_m(c2, m) == 0);
        assert(0nat / m == 0) by(nonlinear_arith) requires m > 0;
        assert(0nat % m == 0) by(nonlinear_arith) requires m > 0;
        assert(c_branch.v == 0);
        assert(c_branch.a == 0);
        lemma_tm_step_picks(tm, c_branch, i_zero);
        let c_final = apply_quint(tm.quints[i_zero], c_branch, m);
        assert(tm_step(tm, c_branch) == Some(c_final));
        assert(0nat * m == 0) by(nonlinear_arith);
        assert(c_final.v == 0);
        assert(c_final.u == repunit_m(c1, m));
        assert(c_final.a == sep());
        assert(c_final.q == q_zero);
        assert(c_final == two_counter_config(c1, 0, q_zero, m));
        assert(tm_run(tm, c_final, 0) == c_final);
        assert(tm_run(tm, c_branch, 1) == c_final);
        assert(tm_run(tm, c_entry, 2) == c_final);
    }
}

/// **The inc-right gadget** (mirror of `lemma_inc`). Four quintuples
///   `(q_walk, 2, 2, q_walk, R)`  peel separator,
///   `(q_walk, 1, 1, q_walk, R)`  walk right over block-1s,
///   `(q_walk, 0, 1, q_back, L)`  turnaround: write the new 1,
///   `(q_back, 1, 1, q_back, L)`  walk back left,
/// run for `2·(c2+1)` steps and reach `two_counter_config(c1, c2+1, q_back)`.
pub proof fn lemma_inc_right(
    tm: Tm, c1: nat, c2: nat, q_walk: nat, q_back: nat,
    i_sep: int, i_one_r: int, i_turn: int, i_one_l: int,
)
    requires
        tm_wf(tm),
        tm.n >= 2,
        q_walk < tm.m,
        0 <= i_sep < tm.quints.len(),
        0 <= i_one_r < tm.quints.len(),
        0 <= i_turn < tm.quints.len(),
        0 <= i_one_l < tm.quints.len(),
        tm.quints[i_sep] == mk_quint(q_walk, sep(), sep(), q_walk, Dir::R),
        tm.quints[i_one_r] == mk_quint(q_walk, 1, 1, q_walk, Dir::R),
        tm.quints[i_turn] == mk_quint(q_walk, 0, 1, q_back, Dir::L),
        tm.quints[i_one_l] == mk_quint(q_back, 1, 1, q_back, Dir::L),
    ensures
        tm_run(tm, two_counter_config(c1, c2, q_walk, tm.m), (2 * c2 + 2) as nat)
            == two_counter_config(c1, (c2 + 1) as nat, q_back, tm.m),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 2);
    let c0 = two_counter_config(c1, c2, q_walk, m);
    let u1 = repunit_m(c1, m) * m + sep();   // the separator + c1 block, under the pile
    lemma_div_mod_step(repunit_m(c1, m), m, sep());   // u1 / m == repunit(c1), u1 % m == sep()
    lemma_repunit_zero(m);
    lemma_repunit_step(0, m);
    assert(repunit_m(1, m) == 1);

    if c2 == 0 {
        assert(c0.v == 0);   // repunit(0)
        // Step 1: sep-peel ⟹ c_sep == (u1, 0, 0, q_walk).
        lemma_tm_step_picks(tm, c0, i_sep);
        let c_sep = apply_quint(tm.quints[i_sep], c0, m);
        assert(tm_step(tm, c0) == Some(c_sep));
        assert(0nat / m == 0) by(nonlinear_arith) requires m > 0;
        assert(0nat % m == 0) by(nonlinear_arith) requires m > 0;
        assert(c_sep.u == u1);
        assert(c_sep.v == 0);
        assert(c_sep.a == 0);
        assert(c_sep.q == q_walk);
        assert(tm_run(tm, c_sep, 0) == c_sep);
        assert(tm_run(tm, c0, 1) == c_sep);
        // Step 2: turnaround ⟹ c_turn == (repunit(c1), 1, sep, q_back) == two_counter_config(c1,1,q_back).
        lemma_tm_step_picks(tm, c_sep, i_turn);
        let c_turn = apply_quint(tm.quints[i_turn], c_sep, m);
        assert(tm_step(tm, c_sep) == Some(c_turn));
        assert(0nat * m == 0) by(nonlinear_arith);
        let c_final = two_counter_config(c1, 1, q_back, m);
        assert(c_turn.v == 1);
        assert(c_turn.u == repunit_m(c1, m));   // u1 / m
        assert(c_turn.a == sep());              // u1 % m
        assert(c_turn.q == q_back);
        assert(c_final.v == repunit_m(1, m));
        assert(c_turn == c_final);
        assert(tm_run(tm, c_turn, 0) == c_turn);
        assert(tm_run(tm, c_sep, 1) == c_turn);
        lemma_tm_run_split(tm, c0, 1, 1);
        assert((2 * c2 + 2) as nat == 2);
        assert(tm_run(tm, c0, 2) == c_final);
    } else {
        // Step 1: sep-peel ⟹ c_sep == (u1, repunit(c2-1), 1, q_walk).
        lemma_tm_step_picks(tm, c0, i_sep);
        let c_sep = apply_quint(tm.quints[i_sep], c0, m);
        assert(tm_step(tm, c0) == Some(c_sep));
        lemma_repunit_div_mod((c2 - 1) as nat, m);   // repunit(c2)/m == repunit(c2-1), %m == 1
        assert(((c2 - 1) as nat + 1) as nat == c2);
        assert(c_sep.u == u1);
        assert(c_sep.v == repunit_m((c2 - 1) as nat, m));
        assert(c_sep.a == 1);
        assert(c_sep.q == q_walk);
        assert(tm_run(tm, c_sep, 0) == c_sep);
        assert(tm_run(tm, c0, 1) == c_sep);

        // Step 2: walk-right ones-loop (c2 steps) ⟹ c_blank == (pile_ones(u1, c2), 0, 0, q_walk).
        lemma_walk_right_inner(tm, c_sep, q_walk, (c2 - 1) as nat, i_one_r);
        let c_blank = (TmConfig { u: pile_ones(u1, c2, m), v: 0, a: 0, q: q_walk });
        assert(tm_run(tm, c_sep, c2) == c_blank);   // fuel (c2-1)+1 == c2; c_sep.v == repunit(c2-1)
        lemma_tm_run_split(tm, c0, 1, c2);
        assert(tm_run(tm, c0, (1 + c2) as nat) == c_blank);

        // Step 3: turnaround (1 step) ⟹ c_turn == (pile_ones(u1, c2-1), 1, 1, q_back).
        lemma_tm_step_picks(tm, c_blank, i_turn);
        let c_turn = apply_quint(tm.quints[i_turn], c_blank, m);
        assert(tm_step(tm, c_blank) == Some(c_turn));
        lemma_pile_ones_div_mod(u1, c2, m);   // pile_ones(u1,c2)%m == 1, /m == pile_ones(u1,c2-1)
        assert(0nat * m == 0) by(nonlinear_arith);
        assert(c_turn.v == 1);
        assert(c_turn.u == pile_ones(u1, (c2 - 1) as nat, m));
        assert(c_turn.a == 1);
        assert(c_turn.q == q_back);
        assert(tm_run(tm, c_turn, 0) == c_turn);
        assert(tm_run(tm, c_blank, 1) == c_turn);
        lemma_tm_run_split(tm, c0, (1 + c2) as nat, 1);
        assert(tm_run(tm, c0, (1 + c2 + 1) as nat) == c_turn);

        // Step 4: walk-back-left ones-loop (c2 steps) ⟹ c_final == two_counter_config(c1, c2+1, q_back).
        assert(c_turn.v == repunit_m(1, m));   // c_turn.v == 1 == repunit(1)
        lemma_walk_back_left_inner(tm, c_turn, q_back, 1, (c2 - 1) as nat, u1, i_one_l);
        assert((1 + (c2 - 1) + 1) as nat == (c2 + 1) as nat);
        let c_final = two_counter_config(c1, (c2 + 1) as nat, q_back, m);
        assert(c_final.v == repunit_m((c2 + 1) as nat, m));
        assert(c_final.u == repunit_m(c1, m));   // u1 / m
        assert(c_final.a == sep());              // u1 % m
        assert(tm_run(tm, c_turn, c2) == c_final);
        lemma_tm_run_split(tm, c0, (1 + c2 + 1) as nat, c2);
        assert((1 + c2 + 1 + c2) as nat == (2 * c2 + 2) as nat);
        assert(tm_run(tm, c0, (2 * c2 + 2) as nat) == c_final);
    }
}

/// **The dec-right gadget** (mirror of `lemma_dec`), for `c2 ≥ 1`. Five quintuples:
///   `(q_walk, 2, 2, q_walk, R)`  peel separator,
///   `(q_walk, 1, 1, q_walk, R)`  walk right to the blank,
///   `(q_walk, 0, 0, q_disc, L)`  erase-turnaround: write 0,
///   `(q_disc, 1, 0, q_back, L)`  discard that popped 1,
///   `(q_back, 1, 1, q_back, L)`  walk back left.
/// For `c2 ≥ 1`, `2·(c2+1)` steps reach `two_counter_config(c1, c2−1, q_back)`.
pub proof fn lemma_dec_right(
    tm: Tm, c1: nat, c2: nat, q_walk: nat, q_disc: nat, q_back: nat,
    i_sep: int, i_one_r: int, i_turn: int, i_disc: int, i_one_l: int,
)
    requires
        tm_wf(tm),
        tm.n >= 2,
        q_walk < tm.m,
        c2 >= 1,
        0 <= i_sep < tm.quints.len(),
        0 <= i_one_r < tm.quints.len(),
        0 <= i_turn < tm.quints.len(),
        0 <= i_disc < tm.quints.len(),
        0 <= i_one_l < tm.quints.len(),
        tm.quints[i_sep] == mk_quint(q_walk, sep(), sep(), q_walk, Dir::R),
        tm.quints[i_one_r] == mk_quint(q_walk, 1, 1, q_walk, Dir::R),
        tm.quints[i_turn] == mk_quint(q_walk, 0, 0, q_disc, Dir::L),
        tm.quints[i_disc] == mk_quint(q_disc, 1, 0, q_back, Dir::L),
        tm.quints[i_one_l] == mk_quint(q_back, 1, 1, q_back, Dir::L),
    ensures
        tm_run(tm, two_counter_config(c1, c2, q_walk, tm.m), (2 * c2 + 2) as nat)
            == two_counter_config(c1, (c2 - 1) as nat, q_back, tm.m),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 2);
    let c0 = two_counter_config(c1, c2, q_walk, m);
    let u1 = repunit_m(c1, m) * m + sep();
    lemma_div_mod_step(repunit_m(c1, m), m, sep());   // u1 / m == repunit(c1), u1 % m == sep()
    lemma_repunit_zero(m);

    // Step 1: sep-peel ⟹ c_sep == (u1, repunit(c2-1), 1, q_walk).
    lemma_tm_step_picks(tm, c0, i_sep);
    let c_sep = apply_quint(tm.quints[i_sep], c0, m);
    assert(tm_step(tm, c0) == Some(c_sep));
    lemma_repunit_div_mod((c2 - 1) as nat, m);
    assert(((c2 - 1) as nat + 1) as nat == c2);
    assert(c_sep.u == u1);
    assert(c_sep.v == repunit_m((c2 - 1) as nat, m));
    assert(c_sep.a == 1);
    assert(c_sep.q == q_walk);
    assert(tm_run(tm, c_sep, 0) == c_sep);
    assert(tm_run(tm, c0, 1) == c_sep);

    // Step 2: walk-right to blank (c2 steps) ⟹ c_blank == (pile_ones(u1, c2), 0, 0, q_walk).
    lemma_walk_right_inner(tm, c_sep, q_walk, (c2 - 1) as nat, i_one_r);
    let c_blank = (TmConfig { u: pile_ones(u1, c2, m), v: 0, a: 0, q: q_walk });
    assert(tm_run(tm, c_sep, c2) == c_blank);
    lemma_tm_run_split(tm, c0, 1, c2);
    assert(tm_run(tm, c0, (1 + c2) as nat) == c_blank);

    // Step 3: erase-turnaround ⟹ c_erase == (pile_ones(u1, c2-1), 0, 1, q_disc).
    lemma_tm_step_picks(tm, c_blank, i_turn);
    let c_erase = apply_quint(tm.quints[i_turn], c_blank, m);
    assert(tm_step(tm, c_blank) == Some(c_erase));
    lemma_pile_ones_div_mod(u1, c2, m);
    assert(0nat * m == 0) by(nonlinear_arith);
    assert(c_erase.v == 0);
    assert(c_erase.u == pile_ones(u1, (c2 - 1) as nat, m));
    assert(c_erase.a == 1);
    assert(c_erase.q == q_disc);
    assert(tm_run(tm, c_erase, 0) == c_erase);
    assert(tm_run(tm, c_blank, 1) == c_erase);
    lemma_tm_run_split(tm, c0, (1 + c2) as nat, 1);
    assert(tm_run(tm, c0, (1 + c2 + 1) as nat) == c_erase);

    // Step 4: discard ⟹ c_disc (u/a case-split on c2).
    lemma_tm_step_picks(tm, c_erase, i_disc);
    let c_disc = apply_quint(tm.quints[i_disc], c_erase, m);
    assert(tm_step(tm, c_erase) == Some(c_disc));
    assert(0nat * m == 0) by(nonlinear_arith);
    assert(c_disc.v == 0);
    assert(c_disc.q == q_back);
    assert(tm_run(tm, c_disc, 0) == c_disc);
    assert(tm_run(tm, c_erase, 1) == c_disc);
    lemma_tm_run_split(tm, c0, (1 + c2 + 1) as nat, 1);
    assert(tm_run(tm, c0, (1 + c2 + 1 + 1) as nat) == c_disc);

    if c2 == 1 {
        // c_erase.u == pile_ones(u1, 0) == u1; discard pops u1 ⟹ c_disc == (repunit(c1), 0, sep, q_back).
        assert(pile_ones(u1, 0, m) == u1);
        assert(c_disc.u == repunit_m(c1, m));   // u1 / m
        assert(c_disc.a == sep());              // u1 % m
        let c_final = two_counter_config(c1, 0, q_back, m);
        assert(c_final.v == repunit_m(0, m));
        assert(c_disc == c_final);
        assert((2 * c2 + 2) as nat == (1 + c2 + 1 + 1) as nat);
        assert(tm_run(tm, c0, (2 * c2 + 2) as nat) == c_final);
    } else {
        // c2 ≥ 2: c_erase.u == pile_ones(u1, c2-1) with c2-1 ≥ 1; discard pops a one.
        lemma_pile_ones_div_mod(u1, (c2 - 1) as nat, m);
        assert(c_disc.u == pile_ones(u1, (c2 - 2) as nat, m));
        assert(c_disc.a == 1);
        assert(c_disc.v == repunit_m(0, m));
        // walk-back-left (c2-1 steps): k0 = 0, rem0 = c2-2.
        lemma_walk_back_left_inner(tm, c_disc, q_back, 0, (c2 - 2) as nat, u1, i_one_l);
        assert((0 + (c2 - 2) + 1) as nat == (c2 - 1) as nat);
        let c_final = two_counter_config(c1, (c2 - 1) as nat, q_back, m);
        assert(c_final.v == repunit_m((c2 - 1) as nat, m));
        assert(c_final.u == repunit_m(c1, m));   // u1 / m
        assert(c_final.a == sep());              // u1 % m
        assert(tm_run(tm, c_disc, (c2 - 1) as nat) == c_final);
        lemma_tm_run_split(tm, c0, (1 + c2 + 1 + 1) as nat, (c2 - 1) as nat);
        assert((1 + c2 + 1 + 1 + (c2 - 1)) as nat == (2 * c2 + 2) as nat);
        assert(tm_run(tm, c0, (2 * c2 + 2) as nat) == c_final);
    }
}

} // verus!
