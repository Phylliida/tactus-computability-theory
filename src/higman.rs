use vstd::prelude::*;
use crate::ceer::*;
use crate::ceer_group::*;
use crate::ceer_group_backward::*;
use crate::ceer_benign::*;
use crate::zfc_ceer::*;
use verus_group_theory::presentation::*;
use verus_group_theory::word::*;

verus! {

///  An embedding of CEER group equivalence into a finitely presented group.
///  Uses ceer_group_equiv (derivation-based) rather than ceer_equiv directly,
///  so the axiom only states the group-theoretic Higman embedding.
pub open spec fn is_ceer_group_fp_embedding(
    e: CEER, p: Presentation, emb: spec_fn(nat) -> Word,
) -> bool {
    (forall|n: nat| #[trigger] word_valid(emb(n), p.num_generators)) &&
    (forall|n: nat, m: nat|
        ceer_group_equiv(e, generator_word(n), generator_word(m))
            <==> #[trigger] equiv_in_presentation(p, emb(n), emb(m)))
}

///  Presentation p admits a CEER group embedding for e.
pub open spec fn admits_ceer_group_embedding(e: CEER, p: Presentation) -> bool {
    exists|emb: spec_fn(nat) -> Word|
        #[trigger] is_ceer_group_fp_embedding(e, p, emb)
}

///  An embedding of ZFC equivalence into presentation p via map emb is valid.
pub open spec fn is_zfc_group_embedding(
    p: Presentation, emb: spec_fn(nat) -> Word,
) -> bool {
    (forall|n: nat| #[trigger] word_valid(emb(n), p.num_generators)) &&
    (forall|n: nat, m: nat|
        zfc_equiv_nat(n, m) <==> #[trigger] equiv_in_presentation(p, emb(n), emb(m)))
}

///  Presentation p admits a ZFC equivalence embedding.
pub open spec fn admits_zfc_embedding(p: Presentation) -> bool {
    exists|emb: spec_fn(nat) -> Word|
        #[trigger] is_zfc_group_embedding(p, emb)
}

///  Transfer: CEER group embedding + ceer_equiv ↔ zfc_equiv → ZFC embedding.
proof fn lemma_ceer_group_to_zfc_embedding(e: CEER, p: Presentation)
    requires
        admits_ceer_group_embedding(e, p),
        forall|n: nat, m: nat| ceer_equiv(e, n, m) <==> zfc_equiv_nat(n, m),
    ensures
        admits_zfc_embedding(p),
{
    let emb = choose|emb: spec_fn(nat) -> Word|
        #[trigger] is_ceer_group_fp_embedding(e, p, emb);

    assert forall|n: nat| #[trigger] word_valid(emb(n), p.num_generators) by {};
    assert forall|n: nat, m: nat|
        zfc_equiv_nat(n, m) <==> #[trigger] equiv_in_presentation(p, emb(n), emb(m))
    by {
        //  Chain: zfc_equiv ↔ ceer_equiv ↔ ceer_group_equiv ↔ presentation equiv
        lemma_ceer_equiv_iff_group_equiv(e, n, m);
    };
    assert(is_zfc_group_embedding(p, emb));
}

///  Higman's Embedding Theorem: the CEER group (recursively presented)
///  embeds in a finitely presented group.
///
///  Proof: lemma_ceer_embeds_in_fp_group_main gives a f.p. group H and
///  an embedding emb such that ceer_equiv(n, m) ↔ equiv_in_presentation(H, emb(n), emb(m)).
///  We bridge ceer_equiv ↔ ceer_group_equiv via lemma_ceer_equiv_iff_group_equiv.
pub proof fn lemma_higman_embedding(e: CEER)
    requires
        ceer_wf(e),
    ensures
        exists|p: Presentation|
            presentation_valid(p) && #[trigger] admits_ceer_group_embedding(e, p),
{
    //  Step 1: Higman's theorem gives a f.p. group + embedding capturing ceer_equiv
    lemma_ceer_embeds_in_fp_group_main(e);

    //  Extract witnesses using the admits_ceer_embedding wrapper
    let p = choose|p: Presentation| #[trigger] admits_ceer_embedding(e, p);
    let emb = choose|emb: spec_fn(nat) -> Word|
        #[trigger] is_ceer_fp_embedding(e, p, emb);

    //  Step 2: Bridge ceer_equiv ↔ ceer_group_equiv to get ceer_group embedding
    assert forall|n: nat| #[trigger] word_valid(emb(n), p.num_generators) by {};

    assert forall|n: nat, m: nat|
        ceer_group_equiv(e, generator_word(n), generator_word(m))
            <==> #[trigger] equiv_in_presentation(p, emb(n), emb(m))
    by {
        lemma_ceer_equiv_iff_group_equiv(e, n, m);
    };

    assert(is_ceer_group_fp_embedding(e, p, emb));
    assert(admits_ceer_group_embedding(e, p));
}

///  ZFC provable equivalence on sentences embeds in the word problem
///  of a finitely presented group.
///
///  There exist a finite group presentation G and a map f: N -> G
///  such that two Gödel codes n, m encode ZFC-equivalent sentences
///  if and only if f(n) and f(m) represent the same element of G.
pub proof fn theorem_zfc_equiv_in_fp_group()
    ensures
        exists|p: Presentation|
            presentation_valid(p) && #[trigger] admits_zfc_embedding(p)
{
    //  Step 1: ZFC equivalence is a CEER
    lemma_zfc_equiv_is_ceer();
    let e = choose|e: CEER| ceer_wf(e) &&
        forall|n: nat, m: nat| ceer_equiv(e, n, m) <==> zfc_equiv_nat(n, m);

    //  Step 2: Apply Higman embedding
    lemma_higman_embedding(e);
    let p = choose|p: Presentation|
        presentation_valid(p) && admits_ceer_group_embedding(e, p);

    //  Step 3: Chain ceer_equiv ↔ group_equiv ↔ presentation equiv,
    //          then transfer to ZFC embedding
    lemma_ceer_group_to_zfc_embedding(e, p);
}

} //  verus!
