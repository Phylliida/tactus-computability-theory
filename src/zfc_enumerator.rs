use vstd::prelude::*;
use crate::formula::*;
use crate::proof_system::*;
use crate::zfc::*;
use crate::zfc_ceer::*;
use crate::proof_encoding::*;

verus! {

//  ============================================================
//  Enumerator spec: the ideal behavior of a proof-checking machine
//  ============================================================

///  Check if a formula is of the form φ↔ψ where φ,ψ are sentences.
pub open spec fn conclusion_is_iff_of_sentences(f: Formula) -> bool {
    match f {
        Formula::Iff { left, right } => is_sentence(*left) && is_sentence(*right),
        _ => false,
    }
}

///  Extract (encode(φ), encode(ψ)) from a formula φ↔ψ.
pub open spec fn extract_iff_pair(f: Formula) -> (nat, nat) {
    match f {
        Formula::Iff { left, right } => (encode(*left), encode(*right)),
        _ => (0, 0),
    }
}

///  A proof code s is valid if it encodes a valid ZFC proof whose conclusion
///  is mk_iff(φ, ψ) for sentences φ, ψ.
pub open spec fn is_valid_iff_proof_code(s: nat) -> bool {
    exists|p: Proof|
        encode_proof(p) == s &&
        is_valid_proof(p, |f: Formula| is_zfc_axiom(f)) &&
        p.lines.len() > 0 &&
        conclusion_is_iff_of_sentences(proof_conclusion(p))
}

///  The ideal enumerator: on input s (a proof code), check if s encodes a valid
///  ZFC proof of φ↔ψ where φ,ψ are sentences. If so, output (encode(φ), encode(ψ)).
pub open spec fn enumerator_spec(s: nat) -> Option<(nat, nat)> {
    if is_valid_iff_proof_code(s) {
        let p = choose|p: Proof|
            encode_proof(p) == s &&
            is_valid_proof(p, |f: Formula| is_zfc_axiom(f)) &&
            p.lines.len() > 0 &&
            conclusion_is_iff_of_sentences(proof_conclusion(p));
        Some(extract_iff_pair(proof_conclusion(p)))
    } else {
        None
    }
}

//  ============================================================
//  Soundness: enumerator output implies ZFC equivalence
//  ============================================================

///  If the enumerator outputs (n, m), then zfc_equiv_nat(n, m).
pub proof fn lemma_enumerator_soundness(s: nat, n: nat, m: nat)
    requires
        enumerator_spec(s) == Some((n, m)),
    ensures
        zfc_equiv_nat(n, m),
{
    //  Extract the chosen proof
    let p = choose|p: Proof|
        encode_proof(p) == s &&
        is_valid_proof(p, |f: Formula| is_zfc_axiom(f)) &&
        p.lines.len() > 0 &&
        conclusion_is_iff_of_sentences(proof_conclusion(p));

    let conclusion = proof_conclusion(p);

    //  The conclusion is Iff { left, right } with both sentences
    match conclusion {
        Formula::Iff { left, right } => {
            let phi = *left;
            let psi = *right;

            //  extract_iff_pair gives (encode(phi), encode(psi))
            assert(extract_iff_pair(conclusion) == (encode(phi), encode(psi)));
            assert(n == encode(phi));
            assert(m == encode(psi));

            //  From is_valid_proof + conclusion: provable_in_zfc(mk_iff(phi, psi))
            assert(proof_conclusion(p) == mk_iff(phi, psi));
            assert(provable_in_zfc(mk_iff(phi, psi)));
            assert(zfc_equiv(phi, psi));

            //  is_sentence from conclusion_is_iff_of_sentences
            assert(is_sentence(phi));
            assert(is_sentence(psi));

            if n == m {
                //  trivially zfc_equiv_nat(n, n)
            } else {
                //  Build the witness pair
                let witness: (Formula, Formula) = (phi, psi);
                assert(zfc_equiv_witness(n, m, phi, psi));
                assert(zfc_witness_pair(n, m, witness));
            }
        },
        _ => {
            //  conclusion_is_iff_of_sentences is false for non-Iff, contradiction
            assert(false);
        },
    }
}

//  ============================================================
//  Completeness: ZFC equivalence implies enumerator outputs pair
//  ============================================================

///  If n ≠ m and zfc_equiv_nat(n, m), then some stage s has enumerator_spec(s) == Some((n, m)).
pub proof fn lemma_enumerator_completeness(n: nat, m: nat)
    requires
        n != m,
        zfc_equiv_nat(n, m),
    ensures
        exists|s: nat| enumerator_spec(s) == Some((n, m)),
{
    //  Extract formulas from zfc_equiv_nat
    let witness = choose|pair: (Formula, Formula)|
        #[trigger] zfc_witness_pair(n, m, pair);
    let phi = witness.0;
    let psi = witness.1;

    assert(encode(phi) == n);
    assert(encode(psi) == m);
    assert(is_sentence(phi));
    assert(is_sentence(psi));
    assert(zfc_equiv(phi, psi));

    //  zfc_equiv(phi, psi) = provable_in_zfc(mk_iff(phi, psi))
    //  provable_in_zfc = provable_from = exists|proof| ...
    //  Get a proof
    let p = choose|p: Proof|
        is_valid_proof(p, |f: Formula| is_zfc_axiom(f)) &&
        proof_conclusion(p) == mk_iff(phi, psi);

    let s = encode_proof(p);

    //  Show conclusion_is_iff_of_sentences(proof_conclusion(p))
    assert(proof_conclusion(p) == mk_iff(phi, psi));
    assert(conclusion_is_iff_of_sentences(proof_conclusion(p)));

    //  Show is_valid_iff_proof_code(s)
    assert(is_valid_iff_proof_code(s));

    //  Show enumerator_spec(s) == Some((n, m))
    //  The choose in enumerator_spec picks some q with encode_proof(q) == s.
    //  By encode_proof injectivity, q == p, so the output matches.
    assert forall|q: Proof|
        encode_proof(q) == s &&
        is_valid_proof(q, |f: Formula| is_zfc_axiom(f)) &&
        q.lines.len() > 0 &&
        conclusion_is_iff_of_sentences(proof_conclusion(q))
        implies extract_iff_pair(proof_conclusion(q)) == (n, m)
    by {
        lemma_encode_proof_injective(q, p);
        //  q == p, so proof_conclusion(q) == mk_iff(phi, psi)
        //  extract_iff_pair(mk_iff(phi, psi)) == (encode(phi), encode(psi)) == (n, m)
    };

    assert(enumerator_spec(s) == Some((n, m)));
}

} //  verus!
