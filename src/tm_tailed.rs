//! # GAP-2 G2-F — tailed sim gadgets (the enum-sim shares the tape with the CZ/output/α tail)
//!
//! When the 2-counter enum-sim runs as a sub-region of `psc_tm`, the right counter's tape (`v`)
//! carries the CZ/output/α working region as an inert high tail above reg2. The clean gadget
//! lemmas (`tm_inc::lemma_inc`, …) pin `v == repunit_m(c2, m)` (blank above reg2), so they don't
//! apply once a tail is present.
//!
//! **The key observation** (verified against the clean proofs): the LEFT-counter gadgets read only
//! `u` and the scanned symbol for control flow — they *push/pop* `v` (during the left walk and the
//! walk back) but never inspect its high digits, and the turnaround fires on the `u`-side blank
//! (`u` exhausted), not on anything in `v`. So they preserve an **arbitrary** `v == r2` verbatim.
//! Hence the "tailed" gadget is just the clean gadget with `v` left abstract — no `+ m^H·tail`
//! bookkeeping is needed at all, because `r2` is never decomposed.
//!
//! For the `[enum-sim bank] · [CZ] · [output] · [α]` layout (sim bank leftmost), the caller
//! instantiates `r2 = repunit_m(c2, m) + pow_nat(m, (c2+1) as nat)·tail`: reg2's block, a blank
//! separator at place `c2`, then the working-region `tail`. But the proof needs no structure on
//! `r2`, so the same lemma serves any layout that keeps the left counter growing into blank.
//!
//! Route-independent: any in-tape 2-counter simulation needs these (the sim's right tape is never
//! infinite blank inside `psc_tm`), and the gadget body is the proven clean one.
//!
//! Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use verus_group_theory::word_numbering::lemma_div_mod_step;
use crate::tm::{Tm, TmConfig, tm_wf, tm_step, tm_run, apply_quint, quint_matches};
use crate::tm_two_counter::{repunit_m, sep, lemma_repunit_div_mod, lemma_repunit_step, lemma_repunit_zero};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};
use crate::tm_walk::{pile_ones, lemma_walk_left_inner, lemma_walk_back_inner, lemma_pile_ones_div_mod};
use crate::tm_run_lemmas::lemma_tm_run_split;

verus! {

/// **The tail-generic inc gadget (left counter).** The `v`-abstract mirror of [`crate::tm_inc::lemma_inc`]:
/// from a head-on-separator config `{u: repunit(c1), v: r2, a: sep(), q: q_walk}` with `r2` an ARBITRARY
/// `v`-value (reg2's block plus any high tail), the four inc quintuples
///   `(q_walk, 2, 2, q_walk, L)`  peel separator,
///   `(q_walk, 1, 1, q_walk, L)`  walk left over reg1's ones,
///   `(q_walk, 0, 1, q_back, R)`  turnaround: write the new 1,
///   `(q_back, 1, 1, q_back, R)`  walk back,
/// run for `2·(c1+1)` steps and reach `{u: repunit(c1+1), v: r2, a: sep(), q: q_back}` — reg1
/// incremented, `r2` (and hence any CZ/output/α tail above reg2) preserved verbatim. `r2 == repunit(c2)`
/// recovers `lemma_inc`. Proof = the clean `lemma_inc` with `repunit(c2)` left abstract as `r2`.
pub proof fn lemma_inc_tailed(
    tm: Tm, c1: nat, r2: nat, q_walk: nat, q_back: nat,
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
        tm_run(tm, (TmConfig { u: repunit_m(c1, tm.m), v: r2, a: sep(), q: q_walk }), (2 * c1 + 2) as nat)
            == (TmConfig { u: repunit_m((c1 + 1) as nat, tm.m), v: r2, a: sep(), q: q_back }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 2);   // tm_wf ⟹ 0 < n < m, n ≥ 2
    let c0 = (TmConfig { u: repunit_m(c1, m), v: r2, a: sep(), q: q_walk });
    let v1 = r2 * m + sep();   // the separator pushed under the (abstract) v
    lemma_div_mod_step(r2, m, sep());   // v1 / m == r2, v1 % m == sep()
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
        // Step 2: turnaround ⟹ c_turn == (1, v1/m, v1%m, q_back) == (1, r2, sep, q_back).
        lemma_tm_step_picks(tm, c_sep, i_turn);
        let c_turn = apply_quint(tm.quints[i_turn], c_sep, m);
        assert(tm_step(tm, c_sep) == Some(c_turn));
        assert(0nat * m == 0) by(nonlinear_arith);
        let c_final = (TmConfig { u: repunit_m(1, m), v: r2, a: sep(), q: q_back });
        assert(c_turn.u == 1);
        assert(c_turn.v == r2);      // c_sep.v / m == v1 / m == r2
        assert(c_turn.a == sep());   // c_sep.v % m == v1 % m == sep()
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

        // Step 4: walk-back ones-loop (c1 steps) ⟹ c_final == (repunit(c1+1), v1/m, v1%m, q_back).
        assert(c_turn.u == repunit_m(1, m));   // c_turn.u == 1 == repunit(1)
        lemma_walk_back_inner(tm, c_turn, q_back, 1, (c1 - 1) as nat, v1, i_one_r);
        assert((1 + (c1 - 1) + 1) as nat == (c1 + 1) as nat);
        let c_final = (TmConfig { u: repunit_m((c1 + 1) as nat, m), v: r2, a: sep(), q: q_back });
        assert(c_final.u == repunit_m((c1 + 1) as nat, m));
        assert(c_final.v == r2);       // v1 / m == r2
        assert(c_final.a == sep());    // v1 % m == sep()
        assert(tm_run(tm, c_turn, c1) == c_final);
        lemma_tm_run_split(tm, c0, (1 + c1 + 1) as nat, c1);
        assert((1 + c1 + 1 + c1) as nat == (2 * c1 + 2) as nat);
        assert(tm_run(tm, c0, (2 * c1 + 2) as nat) == c_final);
    }
}

/// **The tail-generic dec gadget (left counter).** The `v`-abstract mirror of [`crate::tm_dec::lemma_dec`]:
/// from `{u: repunit(c1), v: r2, a: sep(), q: q_walk}` (`c1 ≥ 1`, `r2` arbitrary), the five dec quintuples
///   `(q_walk, 2, 2, q_walk, L)`  peel separator,
///   `(q_walk, 1, 1, q_walk, L)`  walk left to the blank,
///   `(q_walk, 0, 0, q_disc, R)`  erase-turnaround (the outer 1 pops into scanned),
///   `(q_disc, 1, 0, q_back, R)`  discard that popped 1,
///   `(q_back, 1, 1, q_back, R)`  walk back,
/// run for `2·(c1+1)` steps and reach `{u: repunit(c1-1), v: r2, a: sep(), q: q_back}`. The discard drops
/// reg1's outer one; `r2` (any CZ/output/α tail above reg2) is pushed/popped but never inspected, so it is
/// preserved verbatim. `r2 == repunit(c2)` recovers `lemma_dec`.
pub proof fn lemma_dec_tailed(
    tm: Tm, c1: nat, r2: nat, q_walk: nat, q_disc: nat, q_back: nat,
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
        tm_run(tm, (TmConfig { u: repunit_m(c1, tm.m), v: r2, a: sep(), q: q_walk }), (2 * c1 + 2) as nat)
            == (TmConfig { u: repunit_m((c1 - 1) as nat, tm.m), v: r2, a: sep(), q: q_back }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 2);
    let c0 = (TmConfig { u: repunit_m(c1, m), v: r2, a: sep(), q: q_walk });
    let v1 = r2 * m + sep();
    lemma_div_mod_step(r2, m, sep());   // v1 / m == r2, v1 % m == sep()
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
        // c_erase.v == pile_ones(v1, 0) == v1; discard pops v1 ⟹ c_disc == (0, r2, sep, q_back).
        assert(pile_ones(v1, 0, m) == v1);
        assert(c_disc.v == r2);       // v1 / m
        assert(c_disc.a == sep());    // v1 % m
        let c_final = (TmConfig { u: repunit_m(0, m), v: r2, a: sep(), q: q_back });
        assert(c_final.u == repunit_m(0, m));
        assert(c_disc == c_final);
        assert((2 * c1 + 2) as nat == (1 + c1 + 1 + 1) as nat);
        assert(tm_run(tm, c0, (2 * c1 + 2) as nat) == c_final);
    } else {
        // c1 ≥ 2: c_erase.v == pile_ones(v1, c1-1), c1-1 ≥ 1; discard pops a one.
        lemma_pile_ones_div_mod(v1, (c1 - 1) as nat, m);
        assert(c_disc.v == pile_ones(v1, (c1 - 2) as nat, m));
        assert(c_disc.a == 1);
        assert(c_disc.u == repunit_m(0, m));
        // walk-back (c1-1 steps): k0 = 0, rem0 = c1-2.
        lemma_walk_back_inner(tm, c_disc, q_back, 0, (c1 - 2) as nat, v1, i_one_r);
        assert((0 + (c1 - 2) + 1) as nat == (c1 - 1) as nat);
        let c_final = (TmConfig { u: repunit_m((c1 - 1) as nat, m), v: r2, a: sep(), q: q_back });
        assert(c_final.u == repunit_m((c1 - 1) as nat, m));
        assert(c_final.v == r2);       // v1 / m
        assert(c_final.a == sep());    // v1 % m
        assert(tm_run(tm, c_disc, (c1 - 1) as nat) == c_final);
        lemma_tm_run_split(tm, c0, (1 + c1 + 1 + 1) as nat, (c1 - 1) as nat);
        assert((1 + c1 + 1 + 1 + (c1 - 1)) as nat == (2 * c1 + 2) as nat);
        assert(tm_run(tm, c0, (2 * c1 + 2) as nat) == c_final);
    }
}

/// **The tail-generic zero-test (peek) on the left counter.** The `v`-abstract mirror of
/// [`crate::tm_gadget::lemma_peek_gadget`]: from `{u: repunit(c1), v: r2, a: sep(), q: q_entry}`,
///   `(q_entry, 2, 2, q_branch, L)`  step off the separator into reg1,
///   `(q_branch, 1, 1, q_pos, R)`    reg1 nonempty (inner cell 1, `c1>0`) → q_pos,
///   `(q_branch, 0, 0, q_zero, R)`   reg1 empty (inner cell blank, `c1==0`) → q_zero,
/// run 2 steps and land in `q_pos`/`q_zero` (head back on the separator), counters and `r2` unchanged.
/// `r2 == repunit(c2)` recovers `lemma_peek_gadget`.
pub proof fn lemma_peek_tailed(
    tm: Tm, c1: nat, r2: nat,
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
        tm.quints[i_entry] == mk_quint(q_entry, sep(), sep(), q_branch, Dir::L),
        tm.quints[i_pos] == mk_quint(q_branch, 1, 1, q_pos, Dir::R),
        tm.quints[i_zero] == mk_quint(q_branch, 0, 0, q_zero, Dir::R),
    ensures
        c1 > 0 ==> tm_run(tm, (TmConfig { u: repunit_m(c1, tm.m), v: r2, a: sep(), q: q_entry }), 2)
                    == (TmConfig { u: repunit_m(c1, tm.m), v: r2, a: sep(), q: q_pos }),
        c1 == 0 ==> tm_run(tm, (TmConfig { u: repunit_m(c1, tm.m), v: r2, a: sep(), q: q_entry }), 2)
                    == (TmConfig { u: repunit_m(c1, tm.m), v: r2, a: sep(), q: q_zero }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 2);
    let c_entry = (TmConfig { u: repunit_m(c1, m), v: r2, a: sep(), q: q_entry });
    assert(quint_matches(tm.quints[i_entry], c_entry));   // q == q_entry, a == sep()
    lemma_tm_step_picks(tm, c_entry, i_entry);
    let c_branch = apply_quint(tm.quints[i_entry], c_entry, m);
    assert(tm_step(tm, c_entry) == Some(c_branch));
    // c_branch (L-move): (repunit(c1)/m, r2*m + sep, repunit(c1)%m, q_branch).
    assert(c_branch.u == repunit_m(c1, m) / m);
    assert(c_branch.v == r2 * m + sep());
    assert(c_branch.a == repunit_m(c1, m) % m);
    assert(c_branch.q == q_branch);
    lemma_div_mod_step(r2, m, sep());   // (r2*m + sep)/m == r2, %m == sep

    if c1 > 0 {
        lemma_repunit_div_mod((c1 - 1) as nat, m);   // repunit(c1)/m == repunit(c1-1), %m == 1
        assert(((c1 - 1) as nat + 1) as nat == c1);
        assert(c_branch.u == repunit_m((c1 - 1) as nat, m));
        assert(c_branch.a == 1);
        assert(quint_matches(tm.quints[i_pos], c_branch));   // q==q_branch, a==1
        lemma_tm_step_picks(tm, c_branch, i_pos);
        let c_final = apply_quint(tm.quints[i_pos], c_branch, m);
        assert(tm_step(tm, c_branch) == Some(c_final));
        // c_final (R-move): (repunit(c1-1)*m + 1, r2, sep, q_pos).
        lemma_repunit_step((c1 - 1) as nat, m);
        assert(repunit_m(c1, m) == m * repunit_m((c1 - 1) as nat, m) + 1);
        assert(repunit_m((c1 - 1) as nat, m) * m == m * repunit_m((c1 - 1) as nat, m)) by(nonlinear_arith);
        assert(c_final.u == repunit_m((c1 - 1) as nat, m) * m + 1);
        assert(c_final.u == repunit_m(c1, m));
        assert(c_final.v == r2);
        assert(c_final.a == sep());
        assert(c_final.q == q_pos);
        let c_pos = (TmConfig { u: repunit_m(c1, m), v: r2, a: sep(), q: q_pos });
        assert(c_final == c_pos);
        assert(tm_run(tm, c_final, 0) == c_final);
        assert(tm_run(tm, c_branch, 1) == c_final);
        assert(tm_run(tm, c_entry, 2) == c_final);
    } else {
        lemma_repunit_zero(m);
        assert(repunit_m(c1, m) == 0);
        assert(0nat / m == 0) by(nonlinear_arith) requires m > 0;
        assert(0nat % m == 0) by(nonlinear_arith) requires m > 0;
        assert(c_branch.u == 0);
        assert(c_branch.a == 0);
        assert(quint_matches(tm.quints[i_zero], c_branch));   // q==q_branch, a==0
        lemma_tm_step_picks(tm, c_branch, i_zero);
        let c_final = apply_quint(tm.quints[i_zero], c_branch, m);
        assert(tm_step(tm, c_branch) == Some(c_final));
        assert(0nat * m == 0) by(nonlinear_arith);
        assert(c_final.u == 0);
        assert(c_final.v == r2);
        assert(c_final.a == sep());
        assert(c_final.q == q_zero);
        let c_zero = (TmConfig { u: repunit_m(c1, m), v: r2, a: sep(), q: q_zero });
        assert(c_final == c_zero);
        assert(tm_run(tm, c_final, 0) == c_final);
        assert(tm_run(tm, c_branch, 1) == c_final);
        assert(tm_run(tm, c_entry, 2) == c_final);
    }
}

/// **The tail-generic left-exit bounce.** The `v`-abstract mirror of [`crate::tm_bounce::lemma_bounce_left`]:
/// from `{u: repunit(c1), v: r2, a: sep(), q}`,
///   `(q, 2, 2, q_mid, L)`  step off the separator into reg1,
///   `(q_mid, 1, 1, q_out, R)` / `(q_mid, 0, 0, q_out, R)`  bounce back (restoring reg1's inner cell),
/// run 2 steps to `{u: repunit(c1), v: r2, a: sep(), q: q_out}` — a pure state change, counters and `r2`
/// preserved. `r2 == repunit(c2)` recovers `lemma_bounce_left`.
pub proof fn lemma_bounce_left_tailed(
    tm: Tm, c1: nat, r2: nat, q: nat, q_mid: nat, q_out: nat,
    i_b: int, i_one: int, i_zero: int,
)
    requires
        tm_wf(tm),
        tm.n >= 2,
        q < tm.m,
        0 <= i_b < tm.quints.len(),
        0 <= i_one < tm.quints.len(),
        0 <= i_zero < tm.quints.len(),
        tm.quints[i_b] == mk_quint(q, sep(), sep(), q_mid, Dir::L),
        tm.quints[i_one] == mk_quint(q_mid, 1, 1, q_out, Dir::R),
        tm.quints[i_zero] == mk_quint(q_mid, 0, 0, q_out, Dir::R),
    ensures
        tm_run(tm, (TmConfig { u: repunit_m(c1, tm.m), v: r2, a: sep(), q }), 2)
            == (TmConfig { u: repunit_m(c1, tm.m), v: r2, a: sep(), q: q_out }),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 2);
    let c0 = (TmConfig { u: repunit_m(c1, m), v: r2, a: sep(), q });
    lemma_tm_step_picks(tm, c0, i_b);
    let c_mid = apply_quint(tm.quints[i_b], c0, m);
    assert(tm_step(tm, c0) == Some(c_mid));
    lemma_div_mod_step(r2, m, sep());   // (r2*m+sep)/m == r2, %m == sep
    assert(c_mid.v == r2 * m + sep());
    assert(c_mid.q == q_mid);

    if c1 >= 1 {
        lemma_repunit_div_mod((c1 - 1) as nat, m);
        assert(((c1 - 1) as nat + 1) as nat == c1);
        assert(c_mid.u == repunit_m((c1 - 1) as nat, m));
        assert(c_mid.a == 1);
        lemma_tm_step_picks(tm, c_mid, i_one);
        let c_fin = apply_quint(tm.quints[i_one], c_mid, m);
        assert(tm_step(tm, c_mid) == Some(c_fin));
        lemma_repunit_step((c1 - 1) as nat, m);
        assert(repunit_m(c1, m) == m * repunit_m((c1 - 1) as nat, m) + 1);
        assert(repunit_m((c1 - 1) as nat, m) * m == m * repunit_m((c1 - 1) as nat, m)) by(nonlinear_arith);
        assert(c_fin.u == repunit_m(c1, m));
        assert(c_fin.v == r2);       // (r2*m+sep)/m
        assert(c_fin.a == sep());    // (r2*m+sep)%m
        assert(c_fin.q == q_out);
        let c_target = (TmConfig { u: repunit_m(c1, m), v: r2, a: sep(), q: q_out });
        assert(c_fin == c_target);
        assert(tm_run(tm, c_fin, 0) == c_fin);
        assert(tm_run(tm, c_mid, 1) == c_fin);
        assert(tm_run(tm, c0, 2) == c_fin);
    } else {
        lemma_repunit_zero(m);
        assert(repunit_m(c1, m) == 0);
        assert(0nat / m == 0) by(nonlinear_arith) requires m > 0;
        assert(0nat % m == 0) by(nonlinear_arith) requires m > 0;
        assert(c_mid.u == 0);
        assert(c_mid.a == 0);
        lemma_tm_step_picks(tm, c_mid, i_zero);
        let c_fin = apply_quint(tm.quints[i_zero], c_mid, m);
        assert(tm_step(tm, c_mid) == Some(c_fin));
        assert(0nat * m == 0) by(nonlinear_arith);
        assert(c_fin.u == 0);
        assert(c_fin.v == r2);
        assert(c_fin.a == sep());
        assert(c_fin.q == q_out);
        let c_target = (TmConfig { u: repunit_m(c1, m), v: r2, a: sep(), q: q_out });
        assert(c_fin == c_target);
        assert(tm_run(tm, c_fin, 0) == c_fin);
        assert(tm_run(tm, c_mid, 1) == c_fin);
        assert(tm_run(tm, c0, 2) == c_fin);
    }
}

} // verus!
