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
use verus_group_theory::machine_group::{ModMachine, Quad, mm_yields, mm_reaches,
    mm_terminal, quad_matches, quad_step, mod_machine_wf};

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

} // verus!
