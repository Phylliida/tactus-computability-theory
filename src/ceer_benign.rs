use vstd::prelude::*;
use crate::ceer::*;
//  Note: ceer_benign_construction contains the old decomposition
//  (axiom_ceer_relators_benign + rope trick + bridge lemmas).
//  The backward bridge lemmas are known false — see docs/two-gen-backward-bug.md.
//  We now use axiom_ceer_fp_embedding directly instead.
use verus_group_theory::word::*;
use verus_group_theory::presentation::*;

verus! {

//  ============================================================
//  Higman's Embedding Theorem for CEER Groups
//  ============================================================
//
//  Higman's theorem states that every recursively presented group
//  embeds in a finitely presented group.
//
//  The CEER group G = ⟨g₀, g₁, ... | gₐgᵦ⁻¹ for declared (a,b)⟩
//  is recursively presented (the enumerator machine produces the
//  declared pairs computably). By Higman's theorem, G embeds
//  faithfully in some finitely presented group H.
//
//  The proof decomposes into:
//  1. axiom_ceer_relators_benign: the CEER image relators form a
//     benign subgroup of F_2 (Aanderaa-Cohen machine encoding)
//  2. lemma_rope_trick: benign subgroup of F_2 → f.p. embedding
//     (proved in verus-group-theory/higman_operations.rs)
//  3. Bridge lemmas connecting two-gen equivalence ↔ quotient
//     equivalence ↔ CEER equivalence

///  A valid embedding of a CEER into a finitely presented group.
pub open spec fn is_ceer_fp_embedding(
    e: CEER, p: Presentation, emb: spec_fn(nat) -> Word,
) -> bool {
    presentation_valid(p) &&
    (forall|n: nat| #[trigger] word_valid(emb(n), p.num_generators)) &&
    (forall|n: nat, m: nat|
        ceer_equiv(e, n, m) <==>
        #[trigger] equiv_in_presentation(p, emb(n), emb(m)))
}

///  Presentation p admits an embedding of CEER e.
pub open spec fn admits_ceer_embedding(e: CEER, p: Presentation) -> bool {
    exists|emb: spec_fn(nat) -> Word|
        #[trigger] is_ceer_fp_embedding(e, p, emb)
}

///  Higman's Embedding Theorem for CEER groups.
///
///  Every CEER equivalence relation embeds faithfully in the word problem
///  of a finitely presented group: there exist a finite presentation H
///  and a map emb: N → H such that ceer_equiv(n, m) ⟺ emb(n) ≡ emb(m) in H.
///
///  Mathematical justification (Higman's theorem):
///  The CEER group G = ⟨g₀, g₁, ... | gₐgᵦ⁻¹ for declared (a,b)⟩
///  is recursively presented. By Higman's embedding theorem (via HNN
///  extensions + Britton's lemma + the Rope Trick), G embeds faithfully
///  in a finitely presented group.
///
///  Note: an earlier decomposition attempted to factor this through
///  F_2 quotients using equiv_in_two_gen, but that approach is unsound:
///  image relators in F_2 create side-effect commutations that
///  spuriously identify universal words beyond the CEER equivalence.
///  See docs/two-gen-backward-bug.md for details.
#[verifier::external_body]
pub proof fn axiom_ceer_fp_embedding(e: CEER)
    requires
        ceer_wf(e),
    ensures
        exists|p: Presentation, emb: spec_fn(nat) -> Word|
            presentation_valid(p) &&
            #[trigger] is_ceer_fp_embedding(e, p, emb),
{
}

///  Derived form: the CEER admits an embedding in some f.p. group.
pub proof fn lemma_ceer_embeds_in_fp_group_main(e: CEER)
    requires
        ceer_wf(e),
    ensures
        exists|p: Presentation| #[trigger] admits_ceer_embedding(e, p),
{
    axiom_ceer_fp_embedding(e);
    let pair_pe = choose|p: Presentation, emb: spec_fn(nat) -> Word|
        presentation_valid(p) &&
        #[trigger] is_ceer_fp_embedding(e, p, emb);
    let p = pair_pe.0;
    assert(admits_ceer_embedding(e, p));
}

} //  verus!
