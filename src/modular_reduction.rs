//! # GAP-2 — the register→modular machine reduction (INTERFACE SKELETON)
//!
//! Aanderaa–Cohen, *Modular machines I*, Theorem 2: a modular machine simulates a
//! register/Turing machine step-for-step, so any c.e. set is realized as some `H₀(M)`.
//! That supplies the `mm: ModMachine` the Higman chain consumes
//! (`tactus-group-theory/docs/final-gate-axiom-removal-plan.md` §4) so that `H₀(mm)`
//! realizes the CEER's declared pairs — the second conjunct of the §3.4 relator-set match.
//!
//! ## Status: INTERFACE DEFINITION only
//! Authorized 2026-06-26 by Danielle (port 8051) as a type-level-plumbing session:
//! **do not close the reduction here**, pin the data shapes and the H₀ *target* first.
//! Design decision (hers): **parametric-over-`enc`** — GAP-1's word-numbering
//! (`numbers_word`/`w_c`) stays orthogonal to GAP-2's machine, threaded through the
//! abstract [`Enc`] map so neither gap can break the other.
//!
//! The data shapes ([`config_encode`], [`ceer_to_modmachine`], [`rm_modulus`]) and the
//! reduction target ([`mm_realizes_declared`]) are pinned and verify; their **deferred
//! bodies** are honest typed placeholders, NOT correct constructions (each is flagged
//! `DEFERRED (GAP-2 impl)`). The simulation-correctness proofs are stated as documented
//! obligations at the foot of this file — deliberately not yet `proof fn`. No verifier
//! escape hatches are used here (no unsound bypasses of any kind).

use vstd::prelude::*;
use verus_group_theory::machine_group::{ModMachine, mm_in_H0, mm_terminal};
use crate::machine::{RegisterMachine, Configuration};
use crate::ceer::{CEER, declared_equiv};

verus! {

// ─────────────────────────────────────────────────────────────────────────────
// Point 1 — the parametric encoding seam  `enc : (a,b) ↦ α`
// ─────────────────────────────────────────────────────────────────────────────

/// The declared-pair → word-number encoding `enc : (a,b) ↦ α`.
///
/// Held ABSTRACT (a `spec_fn`) on purpose: the modular machine simulates the register
/// machine, while `enc` is the *separate* map onto the GAP-1 word-numbering
/// (`verus_group_theory::word_numbering::{numbers_word, w_c}`). Keeping `enc` a parameter
/// keeps the two gaps orthogonal — refining the word-numbering never forces a change to
/// the machine build, and vice versa (Danielle's Option-B decision, 2026-06-26).
pub type Enc = spec_fn(nat, nat) -> nat;

// ─────────────────────────────────────────────────────────────────────────────
// Point 2 — register-machine state ↦ modular-machine state  (TYPED, not proven)
// ─────────────────────────────────────────────────────────────────────────────

/// The modulus `m` of the modular machine that simulates register machine `rm`.
///
/// Aanderaa–Cohen require `m` to exceed the combined alphabet/state count so the `m`-ary
/// residues `(α mod m, β mod m)` recover the simulated symbol+state. The exact value is a
/// GAP-2 *implementation* detail; this signature pins its type and the `m > 1` contract
/// that `ModMachine`/`mod_machine_wf` need.
///
/// DEFERRED (GAP-2 impl): a provisional lower bound `> 1`, NOT the AC-correct modulus.
pub open spec fn rm_modulus(rm: RegisterMachine) -> nat {
    rm.num_regs + rm.instructions.len() + 2
}

/// Encode a register-machine [`Configuration`] as a modular-machine config pair `(α,β)`.
///
/// This is the simulation's **state map**: the AC construction packs the two
/// tape-halves+state of the simulated machine into the `m`-ary digits of `α` and `β`. For
/// a register machine the natural shape is "program counter + register contents packed in
/// base `m = rm_modulus(rm)`". The SIGNATURE and base-`m` shape are pinned here; the exact
/// digit layout (which register lands in `α` vs `β`, the special-state `q₀` slot) is the
/// deferred AC detail.
///
/// DEFERRED (GAP-2 impl): a placeholder that pins the `(nat, nat)` type only.
pub open spec fn config_encode(rm: RegisterMachine, c: Configuration) -> (nat, nat) {
    let _m = rm_modulus(rm);
    (0, 0)
}

/// The modular machine simulating the CEER enumerator `e`.
///
/// AC Theorem 2 builds `M` so that it drives `config_encode(e.enumerator, ·)`
/// step-for-step and a config reaches the origin `(0,0)` iff the enumerator halts with the
/// corresponding declared pair. The SIGNATURE is the GAP-2 interface; the real quad list is
/// built from the register-machine instructions (one AC quadruple-pair per instruction,
/// plus the special state `q₀`).
///
/// DEFERRED (GAP-2 impl): the trivial terminal machine (empty quad list ⇒ every config
/// terminal ⇒ `H₀ = {(0,0)}`). This pins the `ModMachine` type and keeps the crate green;
/// it realizes the *empty* declared set, NOT the real reduction.
pub open spec fn ceer_to_modmachine(e: CEER) -> ModMachine {
    ModMachine { m: 2, n: 1, quads: Seq::empty() }
}

// ─────────────────────────────────────────────────────────────────────────────
// Point 3 — the H₀ reduction TARGET (delineated; the proof is the deferred impl)
// ─────────────────────────────────────────────────────────────────────────────

/// **The GAP-2 correctness target.** A modular machine `mm` *realizes* CEER `e` under
/// encoding `enc` iff its origin is terminal and, for every pair `(a,b)`, the encoded
/// config `enc(a,b)` reaches the origin exactly when `(a,b)` is declared by `e`:
///
/// ```text
///   mm_terminal(mm,0,0) ∧ ∀ a b. ( mm_in_H0(mm, enc(a,b), 0) ⟺ declared_equiv(e,a,b) )
/// ```
///
/// This is exactly the **second conjunct** of the §3.4 relator-set match. Combined with the
/// GAP-1 word-numbering bridge `w_{enc(a,b)}(c) = encode(cₐc_b⁻¹)` it identifies the CEER
/// declared-relator set with Cohen's `is_S_canonical(mm,·,·)`, closing the
/// `equiv_in_g_limit(ceer_decls_fam(e),·) ⟺ equiv_in_pred_presentation(c_pred(mm,·),·)` link
/// (GAP-1 item-3b).
pub open spec fn mm_realizes_declared(mm: ModMachine, enc: Enc, e: CEER) -> bool {
    &&& mm_terminal(mm, 0, 0)
    &&& forall|a: nat, b: nat|
            #[trigger] mm_in_H0(mm, enc(a, b), 0) <==> declared_equiv(e, a, b)
}

/// **Interface contract (verified).** Unfolds [`mm_realizes_declared`] at one pair: a
/// realizing machine puts the encoded declared pairs — and only those — into `H₀`. This is
/// the shape every downstream GAP-1/§3.4 consumer reads; proving it here pins the contract
/// independently of whatever construction eventually discharges `lemma_modmachine_realizes`.
pub proof fn lemma_realizes_iff(mm: ModMachine, enc: Enc, e: CEER, a: nat, b: nat)
    requires mm_realizes_declared(mm, enc, e),
    ensures mm_in_H0(mm, enc(a, b), 0) <==> declared_equiv(e, a, b),
{
}

// ─────────────────────────────────────────────────────────────────────────────
// Deferred GAP-2 obligations (§4.2) — the IMPLEMENTATION, not this interface session
// ─────────────────────────────────────────────────────────────────────────────
//
// A future (co-designed) GAP-2 session discharges these against Aanderaa–Cohen
// *Modular machines I*, Theorem 2. Stated as documented obligations, deliberately NOT as
// `proof fn` — their honest proofs require the real `ceer_to_modmachine`/`config_encode`
// bodies (the deferred impl), so writing them now would either fail or need a verifier
// escape hatch (forbidden).
//
//   proof fn lemma_ceer_modmachine_wf(e: CEER)
//       requires ceer_wf(e)
//       ensures  mod_machine_wf(ceer_to_modmachine(e))
//
//   proof fn lemma_modmachine_realizes(e: CEER, enc: Enc)
//       requires ceer_wf(e),
//                enc_numbers_relator(enc, ...)   // enc = the GAP-1 word-numbering bridge map
//       ensures  mm_realizes_declared(ceer_to_modmachine(e), enc, e)
//
// Wiring (§3.4 / GAP-1 item-3b): with these two, `is_S_canonical(ceer_to_modmachine(e),n,m)`
// equals the word-numbering image of `ceer_decls_fam(e)`, supplying the concrete `mm` that
// `lemma_limit_commutation`'s `dbar_family_monotone`/`decls_family_valid` hypotheses are
// discharged against, and closing the chain that deletes the residual CEER-embedding axiom.

} // verus!
