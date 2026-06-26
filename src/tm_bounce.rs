//! # GAP-2-E brick B5.0 — the exit-routing "bounce" gadget
//!
//! Every walk gadget (inc/dec) ends with the head back **on the separator** but in the gadget's own
//! internal exit state (`q_back`). To chain into the next instruction the head must rest on the
//! separator in the *next instruction's entry state* — and, crucially, the quintuple that performs
//! that state change must be keyed on a state owned by the *current* instruction's block (so each
//! instruction's quintuples all live in one disjoint state-window, making the `rm_to_tm` determinism
//! proof trivial). A direct `q_back := entry(next)` identification would instead key the gadget's
//! walk-back quintuple on the *next* block's state — breaking that locality.
//!
//! The bounce is a two-step trampoline that fixes this: from `two_counter_config(c1, c2, q)` (head on
//! separator), step **L** off the separator (peeling the inner cell), then step **R** back, restoring
//! the config and landing in the target state `q_out`. Both inner-cell cases (`c1 = 0` → blank,
//! `c1 ≥ 1` → a `1`) are handled, so it works regardless of the counter value. The mirror
//! `lemma_bounce_right` does the same for right-counter exits (R then L, peeling `c2`'s inner cell).
//!
//! Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use verus_group_theory::word_numbering::lemma_div_mod_step;
use crate::tm::{Tm, TmConfig, tm_wf, tm_step, tm_run, apply_quint};
use crate::tm_two_counter::{two_counter_config, repunit_m, sep,
    lemma_repunit_div_mod, lemma_repunit_step, lemma_repunit_zero};
use crate::tm_gadget::{mk_quint, lemma_tm_step_picks};

verus! {

/// **The left-exit bounce.** From the head-on-separator layout in state `q`, the three quintuples
///   `(q, 2, 2, q_mid, L)`   step off the separator into the left block,
///   `(q_mid, 1, 1, q_out, R)`  walk back (inner cell was a `1`, i.e. `c1 ≥ 1`),
///   `(q_mid, 0, 0, q_out, R)`  walk back (inner cell was blank, i.e. `c1 = 0`),
/// run for exactly 2 steps and reach `two_counter_config(c1, c2, q_out)` — counters unchanged, the
/// head back on the separator in the target state `q_out`. The `q_mid` branch selects on `c1`'s
/// inner cell; both arms restore the popped digit, so the net effect is a pure state change.
pub proof fn lemma_bounce_left(
    tm: Tm, c1: nat, c2: nat, q: nat, q_mid: nat, q_out: nat,
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
        tm_run(tm, two_counter_config(c1, c2, q, tm.m), 2)
            == two_counter_config(c1, c2, q_out, tm.m),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 2);   // tm_wf ⟹ 0 < n < m, n ≥ 2
    let c0 = two_counter_config(c1, c2, q, m);
    // Step 1: peel the separator (L-move): u → repunit(c1)/m, v → repunit(c2)*m + 2.
    lemma_tm_step_picks(tm, c0, i_b);
    let c_mid = apply_quint(tm.quints[i_b], c0, m);
    assert(tm_step(tm, c0) == Some(c_mid));
    lemma_div_mod_step(repunit_m(c2, m), m, sep());   // (repunit(c2)*m+2)/m == repunit(c2), %m == 2
    assert(c_mid.v == repunit_m(c2, m) * m + sep());
    assert(c_mid.q == q_mid);

    if c1 >= 1 {
        lemma_repunit_div_mod((c1 - 1) as nat, m);   // repunit(c1)/m == repunit(c1-1), %m == 1
        assert(((c1 - 1) as nat + 1) as nat == c1);
        assert(c_mid.u == repunit_m((c1 - 1) as nat, m));
        assert(c_mid.a == 1);
        // Step 2: walk back (R-move) restoring u: u → repunit(c1-1)*m + 1 == repunit(c1).
        lemma_tm_step_picks(tm, c_mid, i_one);
        let c_fin = apply_quint(tm.quints[i_one], c_mid, m);
        assert(tm_step(tm, c_mid) == Some(c_fin));
        lemma_repunit_step((c1 - 1) as nat, m);   // repunit((c1-1)+1) == m*repunit(c1-1) + 1
        assert(repunit_m(c1, m) == m * repunit_m((c1 - 1) as nat, m) + 1);   // (c1-1)+1 == c1
        assert(repunit_m((c1 - 1) as nat, m) * m == m * repunit_m((c1 - 1) as nat, m)) by(nonlinear_arith);
        assert(c_fin.u == repunit_m(c1, m));
        assert(c_fin.v == repunit_m(c2, m));   // (repunit(c2)*m+2)/m
        assert(c_fin.a == sep());              // (repunit(c2)*m+2)%m
        assert(c_fin.q == q_out);
        assert(c_fin == two_counter_config(c1, c2, q_out, m));
        assert(tm_run(tm, c_fin, 0) == c_fin);
        assert(tm_run(tm, c_mid, 1) == c_fin);
        assert(tm_run(tm, c0, 2) == c_fin);
    } else {
        // c1 == 0: repunit(0) == 0, so u == 0/m == 0, a == 0 % m == 0.
        lemma_repunit_zero(m);
        assert(repunit_m(c1, m) == 0);
        assert(0nat / m == 0) by(nonlinear_arith) requires m > 0;
        assert(0nat % m == 0) by(nonlinear_arith) requires m > 0;
        assert(c_mid.u == 0);
        assert(c_mid.a == 0);
        // Step 2: walk back (R-move) with a2 == 0: u → 0*m + 0 == 0 == repunit(0).
        lemma_tm_step_picks(tm, c_mid, i_zero);
        let c_fin = apply_quint(tm.quints[i_zero], c_mid, m);
        assert(tm_step(tm, c_mid) == Some(c_fin));
        assert(0nat * m == 0) by(nonlinear_arith);
        assert(c_fin.u == 0);
        assert(c_fin.v == repunit_m(c2, m));
        assert(c_fin.a == sep());
        assert(c_fin.q == q_out);
        assert(c_fin == two_counter_config(0, c2, q_out, m));
        assert(tm_run(tm, c_fin, 0) == c_fin);
        assert(tm_run(tm, c_mid, 1) == c_fin);
        assert(tm_run(tm, c0, 2) == c_fin);
    }
}

/// **The right-exit bounce** (mirror of `lemma_bounce_left`). From the head-on-separator layout in
/// state `q`, step **R** off the separator into the right block, then step **L** back, restoring the
/// config and landing in `q_out`. Quintuples:
///   `(q, 2, 2, q_mid, R)`, `(q_mid, 1, 1, q_out, L)`, `(q_mid, 0, 0, q_out, L)`.
pub proof fn lemma_bounce_right(
    tm: Tm, c1: nat, c2: nat, q: nat, q_mid: nat, q_out: nat,
    i_b: int, i_one: int, i_zero: int,
)
    requires
        tm_wf(tm),
        tm.n >= 2,
        q < tm.m,
        0 <= i_b < tm.quints.len(),
        0 <= i_one < tm.quints.len(),
        0 <= i_zero < tm.quints.len(),
        tm.quints[i_b] == mk_quint(q, sep(), sep(), q_mid, Dir::R),
        tm.quints[i_one] == mk_quint(q_mid, 1, 1, q_out, Dir::L),
        tm.quints[i_zero] == mk_quint(q_mid, 0, 0, q_out, Dir::L),
    ensures
        tm_run(tm, two_counter_config(c1, c2, q, tm.m), 2)
            == two_counter_config(c1, c2, q_out, tm.m),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 2);
    let c0 = two_counter_config(c1, c2, q, m);
    // Step 1: peel the separator (R-move): v → repunit(c2)/m, u → repunit(c1)*m + 2.
    lemma_tm_step_picks(tm, c0, i_b);
    let c_mid = apply_quint(tm.quints[i_b], c0, m);
    assert(tm_step(tm, c0) == Some(c_mid));
    lemma_div_mod_step(repunit_m(c1, m), m, sep());   // (repunit(c1)*m+2)/m == repunit(c1), %m == 2
    assert(c_mid.u == repunit_m(c1, m) * m + sep());
    assert(c_mid.q == q_mid);

    if c2 >= 1 {
        lemma_repunit_div_mod((c2 - 1) as nat, m);   // repunit(c2)/m == repunit(c2-1), %m == 1
        assert(((c2 - 1) as nat + 1) as nat == c2);
        assert(c_mid.v == repunit_m((c2 - 1) as nat, m));
        assert(c_mid.a == 1);
        // Step 2: walk back (L-move) restoring v: v → repunit(c2-1)*m + 1 == repunit(c2).
        lemma_tm_step_picks(tm, c_mid, i_one);
        let c_fin = apply_quint(tm.quints[i_one], c_mid, m);
        assert(tm_step(tm, c_mid) == Some(c_fin));
        lemma_repunit_step((c2 - 1) as nat, m);
        assert(repunit_m(c2, m) == m * repunit_m((c2 - 1) as nat, m) + 1);
        assert(repunit_m((c2 - 1) as nat, m) * m == m * repunit_m((c2 - 1) as nat, m)) by(nonlinear_arith);
        assert(c_fin.v == repunit_m(c2, m));
        assert(c_fin.u == repunit_m(c1, m));   // (repunit(c1)*m+2)/m
        assert(c_fin.a == sep());              // (repunit(c1)*m+2)%m
        assert(c_fin.q == q_out);
        assert(c_fin == two_counter_config(c1, c2, q_out, m));
        assert(tm_run(tm, c_fin, 0) == c_fin);
        assert(tm_run(tm, c_mid, 1) == c_fin);
        assert(tm_run(tm, c0, 2) == c_fin);
    } else {
        lemma_repunit_zero(m);
        assert(repunit_m(c2, m) == 0);
        assert(0nat / m == 0) by(nonlinear_arith) requires m > 0;
        assert(0nat % m == 0) by(nonlinear_arith) requires m > 0;
        assert(c_mid.v == 0);
        assert(c_mid.a == 0);
        lemma_tm_step_picks(tm, c_mid, i_zero);
        let c_fin = apply_quint(tm.quints[i_zero], c_mid, m);
        assert(tm_step(tm, c_mid) == Some(c_fin));
        assert(0nat * m == 0) by(nonlinear_arith);
        assert(c_fin.v == 0);
        assert(c_fin.u == repunit_m(c1, m));
        assert(c_fin.a == sep());
        assert(c_fin.q == q_out);
        assert(c_fin == two_counter_config(c1, 0, q_out, m));
        assert(tm_run(tm, c_fin, 0) == c_fin);
        assert(tm_run(tm, c_mid, 1) == c_fin);
        assert(tm_run(tm, c0, 2) == c_fin);
    }
}

} // verus!
