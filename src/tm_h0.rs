//! # GAP-2 brick G2-D — the H₀ correspondence (forward direction + terminal origin)
//!
//! The payoff of the TM→modular simulation: a TM run that reaches the origin config `(0,0,0,0)`
//! lands the modular machine in `H₀`. We chain the existing
//! `verus_group_theory::machine_group::lemma_step_preserves_h0` (a single modular step preserves
//! `H₀`-membership both ways) along the TM run, using the per-step simulation `lemma_sim_step`.
//! The reps alternate (R lands on rep2, L on rep1), so we carry a generic pair `P ∈ {rep1(c),rep2(c)}`.
//!
//! This forward half needs **no tape digit-invariant** — only that non-terminal configs have
//! in-range residues (`lemma_nonterminal_residues`). The backward half (`mm_in_H0 ⟹ TM reaches
//! origin`) additionally needs the digit-invariant + terminal correspondence; it is brick G2-D-bwd.
//! See `docs/gap2-register-modular-plan.md`.

use vstd::prelude::*;
use verus_group_theory::machine_group::{ModMachine, Dir, mm_in_H0, mm_terminal, mm_yields,
    quad_matches, lemma_step_preserves_h0, lemma_origin_in_H0};
use crate::tm::{Tm, tm_wf, quint_wf, tm_terminal, tm_step, tm_halts_at, tm_origin, TmConfig,
    matching_index, apply_quint};
use crate::tm_modular::{tm_to_modmachine, rep1, rep2, rep_next, sim_target, quint_first,
    quint_second, lemma_quads_of, lemma_tm_modmachine_wf, lemma_sim_step, lemma_index_half};

verus! {

/// `(0,0)` is terminal for the modular machine of any well-formed TM: every quadruple carries a
/// residue `≥ n+1` (first quad `b = state`, second quad `a = state`), so none begins with `(0,0)`.
pub proof fn lemma_mm_terminal_origin(tm: Tm)
    requires
        tm_wf(tm),
    ensures
        mm_terminal(tm_to_modmachine(tm), 0, 0),
{
    reveal(tm_wf);
    let mm = tm_to_modmachine(tm);
    let m = tm.m;
    let qs = tm.quints;
    lemma_quads_of(qs, m);
    assert(mm.quads.len() == 2 * qs.len());
    assert forall|i: int| 0 <= i < mm.quads.len() implies !quad_matches(#[trigger] mm.quads[i], m, 0, 0) by {
        let p = i / 2;
        lemma_index_half(i, qs.len());
        assert(quint_wf(qs[p], tm.n, m));
        assert(qs[p].q >= tm.n + 1);
        if i % 2 == 0 {
            assert(i == 2 * p);
            assert(mm.quads[i] == quint_first(qs[p], m));
            // first quad: b = qs[p].q ≥ n+1 > 0, so residue b ≠ 0.
        } else {
            assert(i == 2 * p + 1);
            assert(mm.quads[i] == quint_second(qs[p], m));
            // second quad: a = qs[p].q ≥ n+1 > 0, so residue a ≠ 0.
        }
    }
}

/// A pair `P` is one of the two encodings of config `c`.
pub open spec fn is_rep(p: (nat, nat), c: TmConfig, m: nat) -> bool {
    p == rep1(c, m) || p == rep2(c, m)
}

/// **Forward H₀ correspondence.** If the TM, started from `c`, halts at the origin within `fuel`
/// steps, then *any* encoding `P` of `c` is in `H₀` of the modular machine. Proved by induction on
/// `fuel`, chaining `lemma_step_preserves_h0` along the run; the rep alternates but stays a valid
/// encoding of the current config.
pub proof fn lemma_rep_reaches_origin_h0(tm: Tm, c: TmConfig, p: (nat, nat), fuel: nat)
    requires
        tm_wf(tm),
        is_rep(p, c, tm.m),
        tm_halts_at(tm, c, tm_origin(), fuel),
    ensures
        mm_in_H0(tm_to_modmachine(tm), p.0, p.1),
    decreases fuel,
{
    let mm = tm_to_modmachine(tm);
    let m = tm.m;
    lemma_tm_modmachine_wf(tm);
    if c == tm_origin() && tm_terminal(tm, tm_origin()) {
        // P is rep1/rep2 of the origin, both = (0,0).
        assert(rep1(tm_origin(), m) == (0nat, 0nat));
        assert(rep2(tm_origin(), m) == (0nat, 0nat));
        assert(p == (0nat, 0nat));
        lemma_mm_terminal_origin(tm);
        lemma_origin_in_H0(mm);
    } else {
        // not the (terminal) origin: fuel > 0 and the TM steps (else tm_halts_at would be false).
        assert(fuel > 0);
        assert(!tm_terminal(tm, c)) by {
            // if c were terminal, tm_step(c) is None ⟹ tm_halts_at recursion is false, and the
            // first branch (c==origin) was excluded ⟹ contradiction with the hypothesis.
            if tm_terminal(tm, c) {
                assert(!(c == tm_origin() && tm_terminal(tm, tm_origin())));
            }
        }
        // the matching quintuple and next config.
        let qt = tm.quints[matching_index(tm, c)];
        let c2 = apply_quint(qt, c, m);
        assert(tm_step(tm, c) == Some(c2));
        let tgt = sim_target(qt, c, m);
        lemma_sim_step(tm, c);
        // both rep1(c) and rep2(c) yield tgt; p is one of them.
        assert(mm_yields(mm, p.0, p.1, tgt.0, tgt.1)) by {
            if p == rep1(c, m) { } else { assert(p == rep2(c, m)); }
        }
        assert(tm_halts_at(tm, c2, tm_origin(), (fuel - 1) as nat));
        // tgt == rep_next(qt,c,m), which is rep1(c2) or rep2(c2) ⟹ is_rep(tgt, c2, m).
        assert(tgt == rep_next(qt, c, m));
        assert(is_rep(tgt, c2, m)) by {
            match qt.dir {
                Dir::R => { assert(rep_next(qt, c, m) == rep2(c2, m)); },
                Dir::L => { assert(rep_next(qt, c, m) == rep1(c2, m)); },
            }
        }
        lemma_rep_reaches_origin_h0(tm, c2, tgt, (fuel - 1) as nat);   // mm_in_H0(tgt)
        // P yields tgt ⟹ mm_in_H0(P) ⟺ mm_in_H0(tgt).
        lemma_step_preserves_h0(mm, p.0, p.1, tgt.0, tgt.1);
        assert(mm_in_H0(mm, p.0, p.1));
    }
}

/// **Forward H₀, packaged.** If the TM reaches the origin from `c` (within some fuel), then `rep1(c)`
/// is in `H₀`.
pub proof fn lemma_tm_halt_implies_h0(tm: Tm, c: TmConfig, fuel: nat)
    requires
        tm_wf(tm),
        tm_halts_at(tm, c, tm_origin(), fuel),
    ensures
        mm_in_H0(tm_to_modmachine(tm), rep1(c, tm.m).0, rep1(c, tm.m).1),
{
    lemma_rep_reaches_origin_h0(tm, c, rep1(c, tm.m), fuel);
}

} // verus!
