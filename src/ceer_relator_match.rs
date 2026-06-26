//! # GAP-1 item-3b, brick B2 — the conditional relator-set match (CEER family).
//!
//! `tactus-group-theory/docs/final-gate-axiom-removal-plan.md` §3.4 / §14.4. Co-designed with
//! Danielle (port 8051, 2026-06-26). This is the brick that connects the Miller-collapse direct-limit
//! presentation `p_infty(ceer_decls_fam(e))` (over `{a,t}`) to Cohen's `c_pred(mm,2,m,is_S_canonical)`
//! (over the c-block), via the block-shift relabeling `ρ : Gen(i) ↦ Gen(c_base+i)`.
//!
//! The genuinely new content is the BRIDGE: B1's `decode_word` is a section of the word-numbering
//! `w_c`, so a collapsed family relator `r` (a `{a,t}`-word) shifts to `ρ(r)` (a c-block word) which
//! equals `w_c(c_base,2,m,decode_word(c_base,2,m,ρ(r)))`. The only machine content — that the modular
//! machine's `H₀` realizes exactly the word-numbers of the family relators — is isolated in the
//! hypothesis [`ceer_realizes`] (the sharpened §13 contract: `mm_realizes_declared` strengthened with
//! the BACKWARD exactness clause + the `α≠0` guard; Danielle-confirmed). So this is a SOUND CONDITIONAL
//! lemma — GAP-2-proper (Route C) discharges `ceer_realizes` later; no verifier escape hatches here.
//!
//! With `ceer_realizes` in hand, [`lemma_ceer_item3b`] gives the item-3b iff
//!   `equiv_in_pred_presentation(p_infty(ceer_decls_fam(e)), v, ε)
//!      ⟺ equiv_in_pred_presentation(c_pred(mm,2,m,is_S_canonical(mm,2,m)), ρ(v), ε)`,
//! which chains onto `lemma_ceer_limit_commutation` (item-3a) on the left and the GAP-3 span
//! (`lemma_C_faithful_printable_canonical` + `lemma_C_sound_printable_canonical`) on the right.

use vstd::prelude::*;
use verus_group_theory::symbol::Symbol;
use verus_group_theory::word::{Word, empty_word, word_valid};
use verus_group_theory::pred_presentation::{PredPresentation, equiv_in_pred_presentation,
    pred_presentation_valid, lemma_pred_equiv_refl};
use verus_group_theory::pred_presentation_lemmas::lemma_pred_relator_is_identity;
use verus_group_theory::pred_homomorphism::{apply_hom_pred, lemma_hom_pred_empty};
use verus_group_theory::pred_relabel::{relabel_hom, lemma_equiv_by_relabel,
    lemma_relabel_image_c_alphabet};
use verus_group_theory::word_numbering::{numbers_word, w_c, lemma_w_c_valid};
use verus_group_theory::word_numbering_decode::{decode_word, lemma_decode_section};
use verus_group_theory::miller_collapse_preserve::{dbar, lemma_dbar_valid};
use verus_group_theory::miller_collapse_limit::{p_infty, dbar_union_pred};
use verus_group_theory::cohen_bridge::is_S_canonical;
use verus_group_theory::cohen_retraction::c_pred;
use verus_group_theory::machine_group::{ModMachine, mm_in_H0, mm_terminal, g_m};
use verus_group_theory::layout::{c_base, h2_num_gens};
use crate::ceer::CEER;
use crate::ceer_layer05::{ceer_decls_fam, ceer_decls_fam_at, lemma_ceer_relator_at_valid};

verus! {

// ============================================================================
// Abbreviations
// ============================================================================

/// The c-block base for the Higman tower of `mm` (= `g_m(mm).num_generators`).
pub open spec fn cb_of(mm: ModMachine) -> nat {
    c_base(g_m(mm).num_generators)
}

/// The Miller direct-limit predicate presentation for CEER `e` (2 generators `{a,t}`).
pub open spec fn p1_of(e: CEER) -> PredPresentation {
    p_infty(ceer_decls_fam(e))
}

/// Cohen's predicate presentation `c_pred` at `n=2`, with the canonical machine relator set.
pub open spec fn p2_of(mm: ModMachine, m: nat) -> PredPresentation {
    c_pred(mm, 2, m, is_S_canonical(mm, 2, m))
}

/// The block-shift relabeling `ρ : Gen(i) ↦ Gen(c_base+i)` from `p1_of(e)` into `p2_of(mm,m)`.
pub open spec fn rho(e: CEER, mm: ModMachine, m: nat, w: Word) -> Word {
    apply_hom_pred(relabel_hom(p1_of(e), p2_of(mm, m), cb_of(mm)), w)
}

// ============================================================================
// The machine hypothesis (the sharpened §13 / §3.4 realizes-contract)
// ============================================================================

/// **The GAP-2 obligation, phrased over the family relators (the item-3b consumer form).**  The
/// modular machine `mm` *realizes* the CEER declared-relator family `e` (at word-numbering modulus
/// `m`) iff its origin is terminal and `H₀(mm)` — among nonzero word-numbers — is *exactly* the
/// `decode_word`-images of the collapsed family relators `ρ(r)`:
///   * (FWD) every nonempty family relator's image word-number is in `H₀`;
///   * (BWD) every nonzero word-number in `H₀` is the image word-number of some nonempty family relator.
/// The `α≠0` guard is forced: `mm_in_H0(mm,0,0)` is reflexively true under `mm_terminal`, while the
/// empty relator is never an `enc`-image (it is an identity no-op handled separately). Strengthens the
/// §13 `mm_realizes_declared` (a ⟺ at enc-images only) with the BACKWARD exactness Danielle confirmed.
pub open spec fn ceer_realizes(e: CEER, mm: ModMachine, m: nat) -> bool {
    &&& mm_terminal(mm, 0, 0)
    &&& forall|r: Word| #![trigger dbar_union_pred(ceer_decls_fam(e), r)]
            (dbar_union_pred(ceer_decls_fam(e), r) && r != empty_word())
                ==> mm_in_H0(mm, decode_word(cb_of(mm), 2, m, rho(e, mm, m, r)), 0)
    &&& forall|alpha: nat| #![trigger mm_in_H0(mm, alpha, 0)]
            (numbers_word(2, m, alpha) && alpha != 0 && mm_in_H0(mm, alpha, 0))
                ==> exists|r: Word| dbar_union_pred(ceer_decls_fam(e), r) && r != empty_word()
                        && alpha == decode_word(cb_of(mm), 2, m, rho(e, mm, m, r))
}

// ============================================================================
// Validity helpers
// ============================================================================

/// Every `p_infty`-relator (a collapsed family relator) is a valid 2-generator word.
pub proof fn lemma_dbar_union_valid(e: CEER, r: Word)
    requires
        dbar_union_pred(ceer_decls_fam(e), r),
    ensures
        word_valid(r, 2),
{
    let fam = ceer_decls_fam(e);
    let big_m = choose|big_m: nat| (#[trigger] dbar(big_m, fam(big_m))).contains(r);
    let decls = ceer_decls_fam_at(e, big_m);
    assert(fam(big_m) == decls);
    // every slice relator is valid over big_m generators ⟹ dbar entries valid over 2.
    assert forall|k: int| 0 <= k < decls.len() implies word_valid(#[trigger] decls[k], big_m) by {
        assert(decls[k] == ceer_decls_fam_at(e, big_m)[k]);
        lemma_ceer_relator_at_valid(e, k as nat, big_m);
    }
    lemma_dbar_valid(big_m, decls);
    // r is some dbar entry.
    let k = choose|k: int| 0 <= k < dbar(big_m, decls).len() && dbar(big_m, decls)[k] == r;
    assert(dbar(big_m, decls).contains(r));
}

/// `p_infty(ceer_decls_fam(e))` is a valid predicate presentation.
pub proof fn lemma_p1_valid(e: CEER)
    ensures
        pred_presentation_valid(p1_of(e)),
{
    reveal(pred_presentation_valid);
    let p1 = p1_of(e);
    assert forall|w: Word| #![trigger (p1.relators)(w)] (p1.relators)(w) implies word_valid(w, p1.num_generators) by {
        // (p1.relators)(w) = dbar_union_pred(ceer_decls_fam(e), w); p1.num_generators = 2.
        lemma_dbar_union_valid(e, w);
    }
}

/// `c_pred(mm,2,m,is_S_canonical(mm,2,m))` is a valid predicate presentation.
pub proof fn lemma_p2_valid(mm: ModMachine, m: nat)
    requires
        2 * 2 < m,
    ensures
        pred_presentation_valid(p2_of(mm, m)),
{
    reveal(pred_presentation_valid);
    let p2 = p2_of(mm, m);
    let nk = g_m(mm).num_generators;
    assert forall|w: Word| #![trigger (p2.relators)(w)] (p2.relators)(w) implies word_valid(w, p2.num_generators) by {
        // (p2.relators)(w) = is_S_canonical(mm,2,m)(w): ∃α. numbers_word(2,m,α) ∧ … ∧ w = w_c(c_base(nk),2,m,α).
        let alpha = choose|alpha: nat|
            numbers_word(2, m, alpha) && mm_in_H0(mm, alpha, 0)
            && w == w_c(c_base(nk), 2, m, alpha);
        // c_base(nk)+2 = nk+2 ≤ nk+6 = h2_num_gens(nk,2) = p2.num_generators.
        lemma_w_c_valid(c_base(nk), 2, m, alpha, p2.num_generators);
    }
}

// ============================================================================
// The two relator-set correspondences (conditional on ceer_realizes)
// ============================================================================

/// **Forward correspondence.**  A `p_infty`-relator `r` maps under `ρ` to a trivial word of
/// `c_pred` — for the empty (no-op) relator by reflexivity, for a genuine collapsed relator because
/// `ρ(r) = w_c(c_base,2,m,decode(ρ(r)))` (B1) and `decode(ρ(r)) ∈ H₀` (ceer_realizes FWD), making
/// `ρ(r)` a canonical `S`-relator.
pub proof fn lemma_ceer_relator_fwd(e: CEER, mm: ModMachine, m: nat, r: Word)
    requires
        2 * 2 < m,
        ceer_realizes(e, mm, m),
        dbar_union_pred(ceer_decls_fam(e), r),
    ensures
        equiv_in_pred_presentation(p2_of(mm, m), rho(e, mm, m, r), empty_word()),
{
    let cb = cb_of(mm);
    let p1 = p1_of(e);
    let p2 = p2_of(mm, m);
    if r == empty_word() {
        lemma_hom_pred_empty(relabel_hom(p1, p2, cb));         // ρ(empty) = empty
        assert(rho(e, mm, m, r) =~= empty_word());
        lemma_pred_equiv_refl(p2, empty_word());
    } else {
        lemma_dbar_union_valid(e, r);                           // word_valid(r, 2)
        lemma_relabel_image_c_alphabet(p1, p2, cb, r);          // ρ(r) is a c-block word
        let img = rho(e, mm, m, r);
        lemma_decode_section(cb, 2, m, img);                    // w_c(cb,2,m,decode(img)) = img, numbers_word
        let alpha = decode_word(cb, 2, m, img);
        // ceer_realizes FWD: mm_in_H0(mm, alpha, 0).
        assert(mm_in_H0(mm, alpha, 0));
        // is_S_canonical(mm,2,m)(img) holds with witness α = alpha: numbers, H0, img = w_c(cb,2,m,alpha).
        assert(img == w_c(cb, 2, m, alpha));
        assert((is_S_canonical(mm, 2, m))(img)) by {
            assert(numbers_word(2, m, alpha) && mm_in_H0(mm, alpha, 0)
                && img == w_c(c_base(g_m(mm).num_generators), 2, m, alpha));
        }
        // (p2.relators)(img) = is_S_canonical(mm,2,m)(img) ⟹ equiv(p2, img, ε).
        lemma_pred_relator_is_identity(p2, img);
    }
}

/// **Backward correspondence.**  Every `c_pred`-relator `s` (= `is_S_canonical`-word) is the `ρ`-image
/// of a `p_infty`-trivial word — the empty word for `α=0`, else (by ceer_realizes BWD) a genuine
/// collapsed family relator `r` with `s = w_c(cb,2,m,α) = ρ(r)` (B1).
pub proof fn lemma_ceer_relator_bwd(e: CEER, mm: ModMachine, m: nat, s: Word)
    requires
        2 * 2 < m,
        ceer_realizes(e, mm, m),
        (is_S_canonical(mm, 2, m))(s),
    ensures
        exists|r: Word| #![trigger apply_hom_pred(relabel_hom(p1_of(e), p2_of(mm, m), cb_of(mm)), r)]
            word_valid(r, 2) && equiv_in_pred_presentation(p1_of(e), r, empty_word())
            && s =~= apply_hom_pred(relabel_hom(p1_of(e), p2_of(mm, m), cb_of(mm)), r),
{
    let cb = cb_of(mm);
    let p1 = p1_of(e);
    let p2 = p2_of(mm, m);
    // is_S_canonical(s): choose the word-number α.
    let alpha = choose|alpha: nat|
        numbers_word(2, m, alpha) && mm_in_H0(mm, alpha, 0)
        && s == w_c(c_base(g_m(mm).num_generators), 2, m, alpha);
    assert(numbers_word(2, m, alpha) && mm_in_H0(mm, alpha, 0) && s == w_c(cb, 2, m, alpha));
    if alpha == 0 {
        // s = w_c(cb,2,m,0) = empty; witness r = empty.
        assert(s =~= empty_word());
        lemma_hom_pred_empty(relabel_hom(p1, p2, cb));          // ρ(empty) = empty
        lemma_pred_equiv_refl(p1, empty_word());
        assert(word_valid(empty_word(), 2));
        assert(rho(e, mm, m, empty_word()) =~= empty_word());
        assert(word_valid(empty_word(), 2)
            && equiv_in_pred_presentation(p1, empty_word(), empty_word())
            && s =~= rho(e, mm, m, empty_word()));
    } else {
        // ceer_realizes BWD: ∃ family relator r ≠ ε with α = decode(cb,2,m,ρ(r)).
        let r = choose|r: Word| dbar_union_pred(ceer_decls_fam(e), r) && r != empty_word()
            && alpha == decode_word(cb, 2, m, rho(e, mm, m, r));
        assert(dbar_union_pred(ceer_decls_fam(e), r) && r != empty_word()
            && alpha == decode_word(cb, 2, m, rho(e, mm, m, r)));
        lemma_dbar_union_valid(e, r);                            // word_valid(r, 2)
        lemma_relabel_image_c_alphabet(p1, p2, cb, r);           // ρ(r) is a c-block word
        lemma_decode_section(cb, 2, m, rho(e, mm, m, r));        // w_c(cb,2,m,decode(ρ(r))) = ρ(r)
        // s = w_c(cb,2,m,α) = w_c(cb,2,m,decode(ρ(r))) = ρ(r).
        assert(s =~= rho(e, mm, m, r));
        // equiv(p1, r, ε): (p1.relators)(r) = dbar_union_pred(…, r).
        lemma_pred_relator_is_identity(p1, r);
        assert(word_valid(r, 2)
            && equiv_in_pred_presentation(p1, r, empty_word())
            && s =~= rho(e, mm, m, r));
    }
}

// ============================================================================
// The item-3b iff (conditional on ceer_realizes)
// ============================================================================

/// **B2 / item-3b — the relator-set match made into a word-problem iff.**  Under `ceer_realizes`, the
/// Miller direct-limit presentation and Cohen's `c_pred` present the same word problem on `{a,t}`-words
/// (via the block-shift `ρ`): the genuinely-new bridge of item-3b, conditional only on the GAP-2
/// machine obligation.
pub proof fn lemma_ceer_item3b(e: CEER, mm: ModMachine, m: nat, v: Word)
    requires
        2 * 2 < m,
        ceer_realizes(e, mm, m),
        word_valid(v, 2),
    ensures
        equiv_in_pred_presentation(p1_of(e), v, empty_word())
            <==> equiv_in_pred_presentation(p2_of(mm, m), rho(e, mm, m, v), empty_word()),
{
    let cb = cb_of(mm);
    let p1 = p1_of(e);
    let p2 = p2_of(mm, m);
    lemma_p1_valid(e);
    lemma_p2_valid(mm, m);
    // cb + 2 = nk + 2 ≤ nk + 6 = h2_num_gens(nk,2) = p2.num_generators; p1.num_generators = 2.
    assert(cb + p1.num_generators <= p2.num_generators) by {
        assert(p2.num_generators == h2_num_gens(g_m(mm).num_generators, 2));
        assert(cb == g_m(mm).num_generators);
    }
    // FORWARD correspondence.
    assert forall|r: Word| #![trigger (p1.relators)(r)]
        (p1.relators)(r) implies equiv_in_pred_presentation(p2, apply_hom_pred(relabel_hom(p1, p2, cb), r), empty_word()) by {
        assert(dbar_union_pred(ceer_decls_fam(e), r));         // (p1.relators)(r) unfolds to this
        lemma_ceer_relator_fwd(e, mm, m, r);
    }
    // BACKWARD correspondence.
    assert forall|s: Word| #![trigger (p2.relators)(s)]
        (p2.relators)(s) implies exists|r: Word| #![trigger apply_hom_pred(relabel_hom(p1, p2, cb), r)]
            word_valid(r, 2) && equiv_in_pred_presentation(p1, r, empty_word())
            && s =~= apply_hom_pred(relabel_hom(p1, p2, cb), r) by {
        assert((is_S_canonical(mm, 2, m))(s));                 // (p2.relators)(s) unfolds to this
        lemma_ceer_relator_bwd(e, mm, m, s);
    }
    lemma_equiv_by_relabel(p1, p2, cb, v);
}

} // verus!
