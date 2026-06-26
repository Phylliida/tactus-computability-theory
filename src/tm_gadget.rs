//! # GAP-2-E gadget infrastructure — deterministic step selection + bounded peek
//!
//! The register→TM simulation builds one big deterministic `Tm` whose states are partitioned into
//! per-instruction gadget blocks (like `multi_output_primitives::embed_instructions` for register
//! machines). Each gadget lemma reasons over an *abstract* `tm: Tm` that is `requires`d to carry the
//! gadget's specific quintuples at specific `(state, scanned)` keys; `lemma_tm_step_picks` turns
//! "this quintuple matches" into "`tm_step` fires exactly it", using `tm_wf` determinism.
//!
//! The first gadget is the **bounded zero-test/peek** (B2): from the head-on-separator layout, an
//! `L`-move exposes the inner cell of the left block (`1` ⟺ counter > 0, blank ⟺ counter = 0), and an
//! `R`-move writing the peeked symbol back restores the config — netting only a state change that
//! branches on the counter's zero-ness. Two TM steps, no walk. It validates the gadget machinery
//! before the unbounded inc/dec walks (B3/B4).
//!
//! See `docs/gap2-register-to-tm-plan.md`. Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use verus_group_theory::word_numbering::lemma_div_mod_step;
use crate::tm::{Tm, TmConfig, Quintuple, tm_wf, tm_step, tm_run, tm_terminal, quint_matches,
    apply_quint, matching_index};
use crate::tm_two_counter::{two_counter_config, repunit_m, sep,
    lemma_repunit_div_mod, lemma_repunit_step, lemma_repunit_zero};

verus! {

/// Quintuple constructor (avoids struct-literal parsing issues in `requires`/`assert`).
pub open spec fn mk_quint(q: nat, a: nat, a2: nat, q2: nat, dir: Dir) -> Quintuple {
    Quintuple { q, a, a2, q2, dir }
}

/// **Deterministic step selection.** In a well-formed (hence deterministic) TM, if quintuple `i`
/// matches config `c`, then `tm_step` fires exactly that quintuple. The workhorse behind every gadget:
/// it lets a gadget lemma compute the next config from the one quintuple it placed at `(c.q, c.a)`.
pub proof fn lemma_tm_step_picks(tm: Tm, c: TmConfig, i: int)
    requires
        tm_wf(tm),
        0 <= i < tm.quints.len(),
        quint_matches(tm.quints[i], c),
    ensures
        !tm_terminal(tm, c),
        tm_step(tm, c) == Some(apply_quint(tm.quints[i], c, tm.m)),
{
    reveal(tm_wf);
    // i matches c ⟹ not terminal.
    assert(!tm_terminal(tm, c));
    // matching_index picks SOME matching j; determinism forces j == i.
    let j = matching_index(tm, c);
    assert(0 <= j < tm.quints.len() && quint_matches(tm.quints[j], c)) by {
        let k = choose|k: int| 0 <= k < tm.quints.len() && quint_matches(tm.quints[k], c);
        assert(0 <= k < tm.quints.len() && quint_matches(tm.quints[k], c));
    }
    // quint_matches(quints[i],c) ∧ quint_matches(quints[j],c) ⟹ same (q,a) ⟹ i == j.
    assert(tm.quints[i].q == tm.quints[j].q && tm.quints[i].a == tm.quints[j].a);
    assert(i == j);
}

/// **The bounded zero-test / peek gadget (B2).** From the head-on-separator layout in state `q_entry`,
/// two steps — `L` to expose the left block's inner cell, `R` to write it back — restore the config and
/// land in `q_pos` if `c1 > 0` (inner cell is a `1`) or `q_zero` if `c1 = 0` (inner cell is blank). The
/// counters are unchanged; only the state branches on `c1`'s zero-ness. No walk: exactly two TM steps.
///
/// The three gadget quintuples (placed at `i_entry/i_pos/i_zero`):
///   `(q_entry, 2, 2, q_branch, L)`, `(q_branch, 1, 1, q_pos, R)`, `(q_branch, 0, 0, q_zero, R)`.
pub proof fn lemma_peek_gadget(
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
        tm.quints[i_entry] == mk_quint(q_entry, sep(), sep(), q_branch, Dir::L),
        tm.quints[i_pos] == mk_quint(q_branch, 1, 1, q_pos, Dir::R),
        tm.quints[i_zero] == mk_quint(q_branch, 0, 0, q_zero, Dir::R),
    ensures
        c1 > 0 ==> tm_run(tm, two_counter_config(c1, c2, q_entry, tm.m), 2)
                    == two_counter_config(c1, c2, q_pos, tm.m),
        c1 == 0 ==> tm_run(tm, two_counter_config(c1, c2, q_entry, tm.m), 2)
                    == two_counter_config(c1, c2, q_zero, tm.m),
{
    reveal(tm_wf);
    let m = tm.m;
    // tm_wf ⟹ 0 < n < m and n ≥ 2 ⟹ m > 2 (so sep()=2 < m).
    assert(m > 2);
    let c_entry = two_counter_config(c1, c2, q_entry, m);
    assert(quint_matches(tm.quints[i_entry], c_entry));   // q == q_entry, a == sep()
    lemma_tm_step_picks(tm, c_entry, i_entry);
    let c_branch = apply_quint(tm.quints[i_entry], c_entry, m);
    assert(tm_step(tm, c_entry) == Some(c_branch));
    // c_branch (L-move): (repunit(c1)/m, repunit(c2)*m + 2, repunit(c1)%m, q_branch).
    assert(c_branch.u == repunit_m(c1, m) / m);
    assert(c_branch.v == repunit_m(c2, m) * m + sep());
    assert(c_branch.a == repunit_m(c1, m) % m);
    assert(c_branch.q == q_branch);
    // v restores: (repunit(c2)*m + 2)/m == repunit(c2), %m == 2.
    lemma_div_mod_step(repunit_m(c2, m), m, sep());

    if c1 > 0 {
        // repunit(c1)/m == repunit(c1-1), %m == 1.
        lemma_repunit_div_mod((c1 - 1) as nat, m);
        assert(((c1 - 1) as nat + 1) as nat == c1);
        assert(c_branch.u == repunit_m((c1 - 1) as nat, m));
        assert(c_branch.a == 1);
        assert(quint_matches(tm.quints[i_pos], c_branch));   // q==q_branch, a==1
        lemma_tm_step_picks(tm, c_branch, i_pos);
        let c_final = apply_quint(tm.quints[i_pos], c_branch, m);
        assert(tm_step(tm, c_branch) == Some(c_final));
        // c_final (R-move): (repunit(c1-1)*m + 1, (repunit(c2)*m+2)/m, %m, q_pos).
        lemma_repunit_step((c1 - 1) as nat, m);   // repunit((c1-1)+1) == m*repunit(c1-1) + 1
        assert(repunit_m(c1, m) == m * repunit_m((c1 - 1) as nat, m) + 1);   // (c1-1)+1 == c1
        assert(repunit_m((c1 - 1) as nat, m) * m == m * repunit_m((c1 - 1) as nat, m)) by(nonlinear_arith);
        assert(c_final.u == repunit_m((c1 - 1) as nat, m) * m + 1);
        assert(c_final.u == repunit_m(c1, m));
        assert(c_final.v == repunit_m(c2, m));
        assert(c_final.a == sep());
        assert(c_final.q == q_pos);
        assert(c_final == two_counter_config(c1, c2, q_pos, m));
        // tm_run(c_entry, 2) == tm_run(c_branch, 1) == tm_run(c_final, 0) == c_final.
        assert(tm_run(tm, c_final, 0) == c_final);
        assert(tm_run(tm, c_branch, 1) == c_final);
        assert(tm_run(tm, c_entry, 2) == c_final);
    } else {
        // c1 == 0: repunit(0) == 0, so u == 0/m == 0, a == 0 % m == 0.
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
        // c_final (R-move): (0*m + 0, (repunit(c2)*m+2)/m, %m, q_zero) == (0, repunit(c2), 2, q_zero).
        assert(0nat * m == 0) by(nonlinear_arith);
        assert(c_final.u == 0);
        assert(c_final.v == repunit_m(c2, m));
        assert(c_final.a == sep());
        assert(c_final.q == q_zero);
        assert(c_final == two_counter_config(0, c2, q_zero, m));
        assert(tm_run(tm, c_final, 0) == c_final);
        assert(tm_run(tm, c_branch, 1) == c_final);
        assert(tm_run(tm, c_entry, 2) == c_final);
    }
}

} // verus!
