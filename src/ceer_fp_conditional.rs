//! # GAP-1 item-3b — the conditional axiom-removal assembly.
//!
//! `tactus-group-theory/docs/final-gate-axiom-removal-plan.md` §2 / §5 / §14.4. This module chains the
//! three item-3b bricks (B1 decode bridge, B2 relator match, B3 relabel-iso) onto the already-proven
//! endpoints to produce the FULL explicit chain that replaces `axiom_ceer_fp_embedding`:
//!
//! ```text
//!   ceer_group_equiv(e, w, ε)                                          [L0.5: lemma_ceer_native_embeds_in_c_iff]
//!     ⟺ equiv_in_g_limit(ceer_decls_fam(e), n, ceer_to_word(w), ε)
//!     ⟺ equiv_in_pred_presentation(p_infty(ceer_decls_fam(e)), v, ε)    [item-3a: lemma_ceer_limit_commutation]
//!     ⟺ equiv_in_pred_presentation(c_pred(mm,2,m,is_S_canonical), ρ(v), ε)   [item-3b: lemma_ceer_item3b]
//!     ⟺ equiv_in_presentation(h3_pres(mm,2,m), ρ(v), ε)                [GAP-3: faithful + sound]
//! ```
//! where `v = apply_embedding(miller_collapse_emb(n,0,1), ceer_to_word(w))`.
//!
//! Everything is machine-checked EXCEPT the one GAP-2 obligation, carried as the `ceer_realizes`
//! hypothesis (`tactus-computability-theory/src/modular_reduction.rs`: the modular machine `mm`
//! realizes the CEER declared-relator set as `H₀`). With that one obligation discharged (the deferred
//! Route-C reduction), `lemma_ceer_word_problem_in_h3` is exactly the `(p, emb)` witness that
//! `theorem_zfc_equiv_in_fp_group` needs, and `axiom_ceer_fp_embedding` can be removed. No verifier
//! escape hatches are used here — this is a sound conditional theorem.

use vstd::prelude::*;
use verus_group_theory::word::{Word, empty_word, word_valid};
use verus_group_theory::presentation::equiv_in_presentation;
use verus_group_theory::pred_presentation::equiv_in_pred_presentation;
use verus_group_theory::benign::{apply_embedding, lemma_apply_embedding_valid};
use verus_group_theory::miller_collapse::{miller_collapse_emb, lemma_miller_collapse_emb_len,
    lemma_miller_collapse_emb_valid};
use verus_group_theory::machine_group::{ModMachine, mod_machine_wf, mm_terminal, g_m,
    lemma_word_valid_mono};
use verus_group_theory::layout::c_base;
use verus_group_theory::cohen_h2::{is_c_word, c_symbol};
use verus_group_theory::cohen_bridge::{lemma_C_faithful_printable_canonical,
    lemma_C_sound_printable_canonical};
use verus_group_theory::cohen_retraction::c_pred;
use verus_group_theory::cohen_bridge::is_S_canonical;
use verus_group_theory::h3::h3_pres;
use verus_group_theory::pred_relabel::lemma_relabel_image_c_alphabet;
use verus_group_theory::word_numbering_decode::in_c_block;
use crate::ceer::CEER;
use crate::ceer_group::{CeerWord, CeerSymbol, ceer_group_equiv};
use crate::ceer_layer05::{ceer_to_word, ceer_decls_fam, lemma_ceer_limit_commutation};
use crate::ceer_layer05_bridge::lemma_ceer_native_embeds_in_c_iff;
use crate::ceer_relator_match::{cb_of, p1_of, p2_of, rho, ceer_realizes, lemma_ceer_item3b};

verus! {

// ============================================================================
// Step: item-3b ∘ GAP-3 — the p_infty ⟺ h3_pres span
// ============================================================================

/// **item-3b + GAP-3.**  Under `ceer_realizes`, triviality of a `{a,t}`-word `v` in the Miller
/// direct-limit `p_infty(ceer_decls_fam(e))` equals triviality of its relabel `ρ(v)` in the
/// printable finite Higman group `h3_pres(mm,2,m)`.  Combines `lemma_ceer_item3b` (item-3b: the
/// relator-set match) with the GAP-3 span (`lemma_C_faithful_printable_canonical` +
/// `lemma_C_sound_printable_canonical`), since `ρ(v)` is a pure-c word.
pub proof fn lemma_ceer_pinfty_in_h3(e: CEER, mm: ModMachine, m: nat, v: Word)
    requires
        mod_machine_wf(mm),
        2 * 2 < m,
        ceer_realizes(e, mm, m),
        word_valid(v, 2),
    ensures
        equiv_in_pred_presentation(p1_of(e), v, empty_word())
            <==> equiv_in_presentation(h3_pres(mm, 2, m), rho(e, mm, m, v), empty_word()),
{
    let cb = cb_of(mm);
    let p1 = p1_of(e);
    let p2 = p2_of(mm, m);
    let img = rho(e, mm, m, v);
    let nk = g_m(mm).num_generators;

    // item-3b: equiv(p1, v, ε) ⟺ equiv(p2 = c_pred, img, ε).
    lemma_ceer_item3b(e, mm, m, v);

    // ρ(v) is a pure-c word: c_alphabet_word(cb,2,img) is definitionally is_c_word(nk,2,img).
    lemma_relabel_image_c_alphabet(p1, p2, cb, v);
    assert(is_c_word(nk, 2, img)) by {
        assert forall|i: int| 0 <= i < img.len() implies c_symbol(nk, 2, #[trigger] img[i]) by {
            // c_alphabet_word(cb,2,img) gives in_c_block(cb,2,img[i]); cb == c_base(nk), and
            // in_c_block(c_base(nk),2,s) == c_symbol(nk,2,s) (same generator-index window).
            assert(in_c_block(cb, 2, img[i]));
            assert(cb == c_base(nk));
        }
    }

    // GAP-3: equiv(c_pred, img, ε) ⟺ equiv(h3_pres, img, ε).   (p2 == c_pred(mm,2,m,is_S_canonical(mm,2,m)))
    assert(equiv_in_pred_presentation(p2, img, empty_word())
        ==> equiv_in_presentation(h3_pres(mm, 2, m), img, empty_word())) by {
        if equiv_in_pred_presentation(p2, img, empty_word()) {
            assert(equiv_in_pred_presentation(c_pred(mm, 2, m, is_S_canonical(mm, 2, m)), img, empty_word()));
            lemma_C_sound_printable_canonical(mm, 2, m, img);
        }
    }
    assert(equiv_in_presentation(h3_pres(mm, 2, m), img, empty_word())
        ==> equiv_in_pred_presentation(p2, img, empty_word())) by {
        if equiv_in_presentation(h3_pres(mm, 2, m), img, empty_word()) {
            lemma_C_faithful_printable_canonical(mm, 2, m, img);
        }
    }
}

// ============================================================================
// The full conditional chain — ceer_group_equiv ⟺ h3_pres word problem
// ============================================================================

/// **GAP-1 item-3b headline (conditional).**  The CEER group's word problem equals the word problem of
/// the printable finite Higman group `h3_pres(mm,2,m)`, under the single GAP-2 hypothesis
/// `ceer_realizes`.  This is the explicit `(p = h3_pres, emb = ρ ∘ collapse ∘ ceer_to_word)` chain that
/// replaces `axiom_ceer_fp_embedding` — every step machine-checked except the deferred Route-C modular
/// reduction (`ceer_realizes`).
pub proof fn lemma_ceer_word_problem_in_h3(e: CEER, mm: ModMachine, m: nat, n: nat, w: CeerWord)
    requires
        mod_machine_wf(mm),
        2 * 2 < m,
        ceer_realizes(e, mm, m),
        word_valid(ceer_to_word(w), n),
    ensures
        ceer_group_equiv(e, w, Seq::<CeerSymbol>::empty())
            <==> equiv_in_presentation(h3_pres(mm, 2, m),
                    rho(e, mm, m, apply_embedding(miller_collapse_emb(n, 0, 1), ceer_to_word(w))),
                    empty_word()),
{
    let cw = ceer_to_word(w);
    let emb = miller_collapse_emb(n, 0, 1);
    let v = apply_embedding(emb, cw);

    // v is a valid 2-generator word (the collapse image of an n-generator CEER word).
    lemma_miller_collapse_emb_len(n, 0, 1);              // emb.len() == n + 3
    lemma_miller_collapse_emb_valid(n, 0, 1, 2);          // every emb image valid in 2
    lemma_word_valid_mono(cw, n, (n + 3) as nat);         // cw valid in n ⟹ in n+3 == emb.len()
    lemma_apply_embedding_valid(emb, cw, 2);              // v valid in 2

    // The three iff links, composed transitively.
    lemma_ceer_native_embeds_in_c_iff(e, n, w);           // ceer_group_equiv ⟺ equiv_in_g_limit
    lemma_ceer_limit_commutation(e, n, w);                // equiv_in_g_limit ⟺ equiv_in_pred(p_infty, v, ε)
    lemma_ceer_pinfty_in_h3(e, mm, m, v);                 // equiv_in_pred(p_infty, v, ε) ⟺ equiv(h3_pres, ρ(v), ε)
}

} // verus!
