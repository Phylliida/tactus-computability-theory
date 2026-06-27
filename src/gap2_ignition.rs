//! # GAP-2 G2-F brick B-FR — the ignition / frame lemmas.
//!
//! `docs/gap2-input-loader-plan.md` §2.1, §4.3, §5 (B-FR). Co-designed with Danielle (port 8051),
//! 2026-06-26.
//!
//! ## Why this brick exists
//! Cohen's Higman consumer is hardcoded to the `(α,0)` input convention: `is_S_canonical` /
//! `s_realizes` / the `cohen_cs5_recog` faithfulness engine all derive `(α,0) ∈ H₀(M)` (from
//! `lemma_theorem1`). But `quint_wf` forces every TM quintuple's current state `≥ n+1` — which is
//! exactly what keeps the origin `(0,0)` terminal — so **no `tm_wf` TM can step from a state-0
//! config**, and a config `(α,0)` (β-residue = state = 0) is terminal in *every* `tm_to_modmachine`.
//! Hence the `(α,0) → running` input transition must be performed by **raw modular-machine quads with
//! `b = 0`** (the "ignition" quads), which cannot come from a TM.
//!
//! This module proves that prepending such ignition quads to a base modular machine is *inert on the
//! running region*: for any config whose β-residue is nonzero (a running TM-sim state), the extended
//! machine and the base machine step identically, and (under the natural "stays-running-until-origin"
//! invariant) reach the origin via the same trajectory. That lets the eventual machine-content lemma
//! splice one ignition step onto the existing, generic `lemma_tm_h0_iff` reduction.
//!
//! ## What's here
//!  - [`mm_extend`] — the extended machine `extra ++ base.quads`.
//!  - [`lemma_yields_mono`] / [`lemma_mm_extend_reaches_mono`] — adding quads only adds reachability
//!    (the easy ⟸ direction).
//!  - [`lemma_combined_yields_eq`] — on the running region (`β%m ≠ 0`) the two machines yield identically.
//!  - [`lemma_mm_extend_terminal`] — the origin stays terminal (ignition `a ≠ 0` dodges it).
//!  - [`lemma_terminal_reaches_zero`] — a terminal config only reaches itself in 0 steps.
//!  - [`lemma_frame_reaches`] — the headline: combined-machine reachability to the origin from a
//!    running config descends to base-machine reachability.
//!
//! Fully constructive — no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::{ModMachine, Quad, Dir, mm_yields, mm_reaches,
    mm_terminal, quad_matches, quad_step, quad_wf, mod_machine_wf};

verus! {

// ============================================================================
// The extended machine
// ============================================================================

/// Prepend `extra` quads to `base`'s quads (same modulus/alphabet). The ignition quads sit at the
/// front; the TM-sim quads follow.
pub open spec fn mm_extend(base: ModMachine, extra: Seq<Quad>) -> ModMachine {
    ModMachine { m: base.m, n: base.n, quads: extra + base.quads }
}

/// Concat indexing: the front block is `extra`, the back block is `base.quads`.
proof fn lemma_extend_index(base: ModMachine, extra: Seq<Quad>, i: int)
    requires
        0 <= i < extra.len() + base.quads.len(),
    ensures
        mm_extend(base, extra).quads.len() == extra.len() + base.quads.len(),
        i < extra.len() ==> mm_extend(base, extra).quads[i] == extra[i],
        i >= extra.len() ==> mm_extend(base, extra).quads[i] == base.quads[i - extra.len()],
{
    let qs = extra + base.quads;
    assert(qs.len() == extra.len() + base.quads.len());
    if i < extra.len() {
        assert(qs[i] == extra[i]);
    } else {
        assert(qs[i] == base.quads[i - extra.len()]);
    }
}

// ============================================================================
// Monotonicity (the easy direction): more quads ⟹ more reachability
// ============================================================================

/// A base yield is an extended-machine yield (the base quad sits at a shifted index).
pub proof fn lemma_yields_mono(base: ModMachine, extra: Seq<Quad>, a: nat, b: nat, a2: nat, b2: nat)
    requires
        mm_yields(base, a, b, a2, b2),
    ensures
        mm_yields(mm_extend(base, extra), a, b, a2, b2),
{
    let m = base.m;
    let mm = mm_extend(base, extra);
    let j = choose|j: int| 0 <= j < base.quads.len()
        && quad_matches(base.quads[j], m, a, b) && quad_step(base.quads[j], m, a, b) == (a2, b2);
    assert(0 <= j < base.quads.len()
        && quad_matches(base.quads[j], m, a, b) && quad_step(base.quads[j], m, a, b) == (a2, b2));
    let i = extra.len() + j;
    lemma_extend_index(base, extra, i);
    assert(mm.quads[i] == base.quads[j]);
    assert(0 <= i < mm.quads.len());
    assert(quad_matches(mm.quads[i], m, a, b) && quad_step(mm.quads[i], m, a, b) == (a2, b2));
}

/// Base reachability lifts to the extended machine.
pub proof fn lemma_mm_extend_reaches_mono(base: ModMachine, extra: Seq<Quad>, a0: nat, b0: nat,
    a1: nat, b1: nat, k: nat)
    requires
        mm_reaches(base, a0, b0, a1, b1, k),
    ensures
        mm_reaches(mm_extend(base, extra), a0, b0, a1, b1, k),
    decreases k,
{
    reveal_with_fuel(mm_reaches, 1);
    if k == 0 {
    } else {
        let (am, bm) = choose|am: nat, bm: nat|
            mm_yields(base, a0, b0, am, bm) && mm_reaches(base, am, bm, a1, b1, (k - 1) as nat);
        assert(mm_yields(base, a0, b0, am, bm) && mm_reaches(base, am, bm, a1, b1, (k - 1) as nat));
        lemma_yields_mono(base, extra, a0, b0, am, bm);
        lemma_mm_extend_reaches_mono(base, extra, am, bm, a1, b1, (k - 1) as nat);
        assert(mm_yields(mm_extend(base, extra), a0, b0, am, bm)
            && mm_reaches(mm_extend(base, extra), am, bm, a1, b1, (k - 1) as nat));
    }
}

// ============================================================================
// Frame on the running region (β%m ≠ 0): the two machines coincide
// ============================================================================

/// On a running config (`β%m ≠ 0`) the ignition quads (`b = 0`) never match, so the extended machine
/// and the base machine yield exactly the same successors.
pub proof fn lemma_combined_yields_eq(base: ModMachine, extra: Seq<Quad>, a: nat, b: nat, a2: nat, b2: nat)
    requires
        b % base.m != 0,
        forall|i: int| 0 <= i < extra.len() ==> (#[trigger] extra[i]).b == 0,
    ensures
        mm_yields(mm_extend(base, extra), a, b, a2, b2) <==> mm_yields(base, a, b, a2, b2),
{
    let m = base.m;
    let mm = mm_extend(base, extra);
    // ⟸ monotone.
    if mm_yields(base, a, b, a2, b2) {
        lemma_yields_mono(base, extra, a, b, a2, b2);
    }
    // ⟹ any matching extended quad is a base quad (extra has b=0, can't match β%m≠0).
    if mm_yields(mm, a, b, a2, b2) {
        let i = choose|i: int| 0 <= i < mm.quads.len()
            && quad_matches(mm.quads[i], m, a, b) && quad_step(mm.quads[i], m, a, b) == (a2, b2);
        assert(0 <= i < mm.quads.len()
            && quad_matches(mm.quads[i], m, a, b) && quad_step(mm.quads[i], m, a, b) == (a2, b2));
        lemma_extend_index(base, extra, i);
        if i < extra.len() {
            // extra[i].b == 0, but quad_matches needs b % m == extra[i].b == 0 — contradiction.
            assert(mm.quads[i] == extra[i]);
            assert(extra[i].b == 0);
            assert(quad_matches(extra[i], m, a, b));   // ⟹ b % m == 0
            assert(false);
        }
        let j = i - extra.len();
        assert(mm.quads[i] == base.quads[j]);
        assert(0 <= j < base.quads.len()
            && quad_matches(base.quads[j], m, a, b) && quad_step(base.quads[j], m, a, b) == (a2, b2));
    }
}

// ============================================================================
// Origin stays terminal; terminal configs only self-reach in 0 steps
// ============================================================================

/// The origin `(0,0)` is terminal in the extended machine: base quads stay terminal there, and the
/// ignition quads (with `a ≠ 0`) cannot match `(0,0)` (whose α-residue is 0).
pub proof fn lemma_mm_extend_terminal(base: ModMachine, extra: Seq<Quad>)
    requires
        base.m > 0,
        mm_terminal(base, 0, 0),
        forall|i: int| 0 <= i < extra.len() ==> (#[trigger] extra[i]).a != 0,
    ensures
        mm_terminal(mm_extend(base, extra), 0, 0),
{
    let m = base.m;
    let mm = mm_extend(base, extra);
    vstd::arithmetic::div_mod::lemma_small_mod(0, m);   // 0 % m == 0
    assert(0nat % m == 0);
    assert forall|i: int| 0 <= i < mm.quads.len() implies !quad_matches(#[trigger] mm.quads[i], m, 0, 0) by {
        lemma_extend_index(base, extra, i);
        if i < extra.len() {
            // quad_matches(extra[i], m, 0, 0) needs 0 % m == extra[i].a, i.e. extra[i].a == 0.
            assert(extra[i].a != 0);
            assert(mm.quads[i] == extra[i]);
            assert(!quad_matches(mm.quads[i], m, 0, 0));
        } else {
            let j = i - extra.len();
            assert(mm.quads[i] == base.quads[j]);
            assert(!quad_matches(base.quads[j], m, 0, 0));   // base terminal at origin
        }
    }
}

/// A terminal config only reaches itself in 0 steps (or it would have to yield, contradiction caller-side).
pub proof fn lemma_terminal_reaches_zero(mm: ModMachine, a: nat, b: nat, j: nat)
    requires
        mm_terminal(mm, a, b),
        mm_reaches(mm, a, b, a, b, j),
    ensures
        j == 0 || (exists|am: nat, bm: nat| mm_yields(mm, a, b, am, bm)),
{
    reveal_with_fuel(mm_reaches, 1);
    if j != 0 {
        let (am, bm) = choose|am: nat, bm: nat|
            mm_yields(mm, a, b, am, bm) && mm_reaches(mm, am, bm, a, b, (j - 1) as nat);
        assert(mm_yields(mm, a, b, am, bm));
    }
}

/// Specialization at the origin: a `mm_terminal(mm,0,0)` config reaches `(0,0)` only in 0 steps.
pub proof fn lemma_origin_reaches_zero(mm: ModMachine, j: nat)
    requires
        mm_terminal(mm, 0, 0),
        mm_reaches(mm, 0, 0, 0, 0, j),
    ensures
        j == 0,
{
    reveal_with_fuel(mm_reaches, 1);
    if j != 0 {
        let (am, bm) = choose|am: nat, bm: nat|
            mm_yields(mm, 0, 0, am, bm) && mm_reaches(mm, am, bm, 0, 0, (j - 1) as nat);
        assert(mm_yields(mm, 0, 0, am, bm));
        let i = choose|i: int| 0 <= i < mm.quads.len()
            && quad_matches(mm.quads[i], mm.m, 0, 0) && quad_step(mm.quads[i], mm.m, 0, 0) == (am, bm);
        assert(0 <= i < mm.quads.len() && quad_matches(mm.quads[i], mm.m, 0, 0));
        assert(!quad_matches(mm.quads[i], mm.m, 0, 0));   // mm_terminal
        assert(false);
    }
}

// ============================================================================
// The headline frame lemma
// ============================================================================

/// **B-FR.**  Under the running-region invariant — a base yield from a `β%m ≠ 0` config lands on the
/// origin or stays `β%m ≠ 0` — extended-machine reachability to the origin from a running config
/// descends to base-machine reachability. (The ignition quads are never used past the start.)
///
/// For the relator-decider this is applied at the post-ignition config `rep1(c1)` (state `≥ n+1`, so
/// `β%m ≠ 0`); the invariant is the TM-sim "states stay `≥ n+1` until the origin" guarantee.
pub proof fn lemma_frame_reaches(base: ModMachine, extra: Seq<Quad>, a: nat, b: nat, k: nat)
    requires
        mod_machine_wf(base),
        mm_terminal(base, 0, 0),
        forall|i: int| 0 <= i < extra.len() ==> (#[trigger] extra[i]).b == 0,
        forall|i: int| 0 <= i < extra.len() ==> (#[trigger] extra[i]).a != 0,
        b % base.m != 0,
        forall|aa: nat, bb: nat, a2: nat, b2: nat|
            (bb % base.m != 0 && #[trigger] mm_yields(base, aa, bb, a2, b2) && !(a2 == 0 && b2 == 0))
                ==> b2 % base.m != 0,
        mm_reaches(mm_extend(base, extra), a, b, 0, 0, k),
    ensures
        mm_reaches(base, a, b, 0, 0, k),
    decreases k,
{
    let m = base.m;
    let mm = mm_extend(base, extra);
    lemma_mm_extend_terminal(base, extra);   // mm_terminal(mm, 0, 0)
    reveal_with_fuel(mm_reaches, 1);
    if k == 0 {
        // (a,b) == (0,0) ⟹ b % m == 0, contradicting b % m != 0.
        assert(a == 0 && b == 0);
        assert(b % m == 0);
        assert(false);
    } else {
        let (am, bm) = choose|am: nat, bm: nat|
            mm_yields(mm, a, b, am, bm) && mm_reaches(mm, am, bm, 0, 0, (k - 1) as nat);
        assert(mm_yields(mm, a, b, am, bm) && mm_reaches(mm, am, bm, 0, 0, (k - 1) as nat));
        lemma_combined_yields_eq(base, extra, a, b, am, bm);
        assert(mm_yields(base, a, b, am, bm));
        if am == 0 && bm == 0 {
            lemma_origin_reaches_zero(mm, (k - 1) as nat);
            assert(k - 1 == 0);
            assert(mm_reaches(base, 0, 0, 0, 0, 0));
            assert(mm_reaches(base, a, b, 0, 0, k)) by {
                assert(mm_yields(base, a, b, 0, 0) && mm_reaches(base, 0, 0, 0, 0, (k - 1) as nat));
            }
        } else {
            assert(bm % m != 0);   // running-region invariant at (a,b)→(am,bm)
            lemma_frame_reaches(base, extra, am, bm, (k - 1) as nat);
            assert(mm_reaches(base, am, bm, 0, 0, (k - 1) as nat));
            assert(mm_reaches(base, a, b, 0, 0, k)) by {
                assert(mm_yields(base, a, b, am, bm) && mm_reaches(base, am, bm, 0, 0, (k - 1) as nat));
            }
        }
    }
}

// ============================================================================
// B-IG — the concrete ignition quads (the (α,0) → running handoff)
// ============================================================================
//
// One ignition quad per relator-word digit `i ∈ 1..=ndig` (ndig = 2·n_word = 4 for the {a,t}
// alphabet). On input config `(α,0)` with low digit `α%m = i`, the L-direction quad
// `{a:i, b:0, c:start(i), dir:L}` steps to `(α/m, start(i))` — exactly `rep1(c1)` of the running
// config `c1 = { u:α/m², v:0, a:(α/m)%m, q:start(i) }` (the parser's per-digit entry state). This is
// the only raw `b=0` step; everything after runs as a `tm_wf` TM (see the plan, §2.1).

/// The ignition quad for digit `i` handing off to running state `qs`.
pub open spec fn ignition_quad(i: nat, qs: nat) -> Quad {
    Quad { a: i, b: 0, c: qs, dir: Dir::L }
}

/// The ignition block: `ndig` quads, the `k`-th for digit `k+1` handing off to `start(k+1)`.
pub open spec fn ignition_quads(ndig: nat, start: spec_fn(nat) -> nat) -> Seq<Quad> {
    Seq::new(ndig, |k: int| ignition_quad((k + 1) as nat, start((k + 1) as nat)))
}

/// Every ignition quad has `b == 0` and `a != 0` — the B-FR frame hypotheses.
pub proof fn lemma_ignition_quads_shape(ndig: nat, start: spec_fn(nat) -> nat)
    ensures
        ignition_quads(ndig, start).len() == ndig,
        forall|k: int| 0 <= k < ndig ==> (#[trigger] ignition_quads(ndig, start)[k]).b == 0,
        forall|k: int| 0 <= k < ndig ==> (#[trigger] ignition_quads(ndig, start)[k]).a != 0,
{
    let igs = ignition_quads(ndig, start);
    assert forall|k: int| 0 <= k < ndig implies
        (#[trigger] igs[k]).b == 0 && igs[k].a != 0 by {
        assert(igs[k] == ignition_quad((k + 1) as nat, start((k + 1) as nat)));
    }
}

/// **The ignition one-step yield.**  From `(α,0)` with low digit `i = α%m` in range, the extended
/// machine steps (via the matching ignition quad) to `(α/m, start(i))`.
pub proof fn lemma_ignition_yields(base: ModMachine, ndig: nat, start: spec_fn(nat) -> nat,
    alpha: nat)
    requires
        base.m > 0,
        1 <= alpha % base.m <= ndig,
    ensures
        mm_yields(mm_extend(base, ignition_quads(ndig, start)), alpha, 0,
            alpha / base.m, start(alpha % base.m)),
{
    let m = base.m;
    let i = alpha % m;
    let igs = ignition_quads(ndig, start);
    let mm = mm_extend(base, igs);
    let idx = (i - 1) as int;
    // The ignition quad at index i-1 is ignition_quad(i, start(i)).
    assert(0 <= idx < ndig);
    assert(igs[idx] == ignition_quad(i, start(i)));
    lemma_extend_index(base, igs, idx);
    assert(mm.quads[idx] == igs[idx]);
    assert(0 <= idx < mm.quads.len());
    // quad_matches: alpha % m == i (== igs[idx].a), 0 % m == 0 (== igs[idx].b).
    vstd::arithmetic::div_mod::lemma_small_mod(0, m);   // 0 % m == 0
    assert(quad_matches(mm.quads[idx], m, alpha, 0));
    // quad_step (L): (alpha/m, (0/m)*(m*m) + start(i)) == (alpha/m, start(i)).
    assert(0nat / m == 0) by { vstd::arithmetic::div_mod::lemma_small_mod(0, m); }
    assert(quad_step(mm.quads[idx], m, alpha, 0) == (alpha / m, start(i)));
}

/// **The combined machine is well-formed.**  Given a `mod_machine_wf` base whose quads all carry a
/// nonzero `b` (true for any `tm_to_modmachine`, whose `b` is the quintuple state `≥ n+1`), and
/// ignition handoff states/digits within range, the extended machine is `mod_machine_wf`:
/// determinism holds because ignition residues `(i,0)` are pairwise distinct and never collide with
/// base residues `(·, b≠0)`.
pub proof fn lemma_mm_extend_wf(base: ModMachine, ndig: nat, start: spec_fn(nat) -> nat)
    requires
        mod_machine_wf(base),
        ndig < base.m,
        forall|i: nat| 1 <= i <= ndig ==> #[trigger] start(i) < base.m,
        forall|j: int| 0 <= j < base.quads.len() ==> (#[trigger] base.quads[j]).b != 0,
    ensures
        mod_machine_wf(mm_extend(base, ignition_quads(ndig, start))),
{
    let m = base.m;
    let n = base.n;
    let igs = ignition_quads(ndig, start);
    let mm = mm_extend(base, igs);
    lemma_ignition_quads_shape(ndig, start);
    assert(mm.m > 1 && 0 < mm.n < mm.m);
    // quad_wf for every combined quad.
    assert forall|i: int| 0 <= i < mm.quads.len() implies quad_wf(#[trigger] mm.quads[i], m) by {
        lemma_extend_index(base, igs, i);
        if i < igs.len() {
            let d = (i + 1) as nat;
            assert(igs[i] == ignition_quad(d, start(d)));
            assert(mm.quads[i] == igs[i]);
            // a = d ≤ ndig < m ; b = 0 < m ; c = start(d) < m ≤ m*m.
            assert(1 <= d <= ndig);
            assert(start(d) < m);
            assert(m <= m * m) by(nonlinear_arith) requires m > 1;
        } else {
            let j = i - igs.len();
            assert(mm.quads[i] == base.quads[j]);
            assert(quad_wf(base.quads[j], m));
        }
    }
    // determinism.
    assert forall|i: int, j: int|
        0 <= i < mm.quads.len() && 0 <= j < mm.quads.len() && i != j
        && (#[trigger] mm.quads[i]).a == (#[trigger] mm.quads[j]).a
        && mm.quads[i].b == mm.quads[j].b implies i == j by {
        lemma_extend_index(base, igs, i);
        lemma_extend_index(base, igs, j);
        let ng = igs.len();
        if i < ng && j < ng {
            // both ignition: a = i+1 = j+1 ⟹ i == j.
            assert(igs[i] == ignition_quad((i + 1) as nat, start((i + 1) as nat)));
            assert(igs[j] == ignition_quad((j + 1) as nat, start((j + 1) as nat)));
            assert(mm.quads[i].a == (i + 1) as nat && mm.quads[j].a == (j + 1) as nat);
        } else if i >= ng && j >= ng {
            // both base: base determinism on shifted indices.
            assert(mm.quads[i] == base.quads[i - ng] && mm.quads[j] == base.quads[j - ng]);
            assert(base.quads[i - ng].a == base.quads[j - ng].a
                && base.quads[i - ng].b == base.quads[j - ng].b);
            assert(i - ng == j - ng);
        } else if i < ng {
            // ignition i (b=0) vs base j (b≠0): same b impossible.
            assert(mm.quads[i] == igs[i] && igs[i].b == 0);
            assert(mm.quads[j] == base.quads[j - ng] && base.quads[j - ng].b != 0);
            assert(false);
        } else {
            assert(mm.quads[j] == igs[j] && igs[j].b == 0);
            assert(mm.quads[i] == base.quads[i - ng] && base.quads[i - ng].b != 0);
            assert(false);
        }
    }
}

} // verus!
