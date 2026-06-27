//! # GAP-2 G2-F Route (i) brick R-relnum-gen (spec) — ρ drops out of the digit analysis.
//!
//! `relnum(e,mm,m,a,b) = decode_word(cb, 2, m, ρ(fam_relator(a,b)))`, where `ρ = relabel_hom(...,cb)` is
//! the block-shift `Gen(i) ↦ Gen(cb+i)`, `Inv(i) ↦ Inv(cb+i)`. But `decode_word`'s `letter_digit(cb,2,·)`
//! *un-shifts* by the same `cb`: `letter_digit(cb,2,Gen(cb+i)) = i+1 = letter_digit(0,2,Gen(i))`, and
//! likewise for `Inv`. So `decode_word(cb,2,m,ρ(w)) == decode_word(0,2,m,w)` — **the relabeling ρ is
//! invisible to the word-number.** [`lemma_relnum_no_rho`] therefore reduces the emitter's target to
//! `decode_word(0, 2, m, fam_relator(a,b))`, eliminating the relabel wrapper from every downstream
//! digit-pattern proof (R-relnum-gen / R-cmp).
//!
//! `docs/gap2-input-loader-plan.md` §5 (R-relnum-gen). Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::symbol::{Symbol, generator_index};
use verus_group_theory::word::{Word, word_valid, inverse_word, concat, lemma_inverse_singleton};
use verus_group_theory::pred_presentation::PredPresentation;
use verus_group_theory::pred_relabel::relabel_hom;
use verus_group_theory::pred_homomorphism::{apply_hom_pred, apply_hom_symbol_pred,
    lemma_hom_pred_respects_concat};
use verus_group_theory::word_numbering_decode::{decode_word, letter_digit};
use verus_group_theory::miller_collapse::{miller_collapse_emb, miller_collapse_word, b_sub,
    lemma_miller_collapse_word_valid};
use verus_group_theory::benign::{apply_embedding, lemma_apply_embedding_valid};
use verus_group_theory::miller_collapse_limit::p_infty;
use crate::ceer::CEER;
use crate::ceer_group::ceer_relator;
use crate::ceer_layer05::{ceer_to_word, ceer_decls_fam};
use crate::ceer_relator_match::{cb_of, rho, p1_of, p2_of};
use crate::gap2_relnum::{relnum, fam_relator, rel_slice, lemma_ceer_relator_word_valid};
use crate::gap2_relnum_digits::{decode_digit_seq, lemma_decode_word_is_dpack};
use crate::tm_dstring::dpack;
use verus_group_theory::machine_group::ModMachine;

verus! {

/// The block-shift image of a single symbol under `relabel_hom(...,off)`: `Gen(i) ↦ Gen(off+i)`,
/// `Inv(i) ↦ Inv(off+i)`.
pub open spec fn shift_sym(s: Symbol, off: nat) -> Symbol {
    match s {
        Symbol::Gen(i) => Symbol::Gen((off + i) as nat),
        Symbol::Inv(i) => Symbol::Inv((off + i) as nat),
    }
}

/// **Per-symbol relabel.** For a relabeling `h = relabel_hom(p1,p2,off)` and a symbol whose generator
/// index is in range (`< p1.num_generators`), `apply_hom_symbol_pred(h,s)` is the single-symbol word
/// `[shift_sym(s,off)]`.
pub proof fn lemma_relabel_symbol(p1: PredPresentation, p2: PredPresentation, off: nat, s: Symbol)
    requires
        generator_index(s) < p1.num_generators,
    ensures
        apply_hom_symbol_pred(relabel_hom(p1, p2, off), s) =~= seq![shift_sym(s, off)],
{
    let h = relabel_hom(p1, p2, off);
    match s {
        Symbol::Gen(i) => {
            assert(generator_index(s) == i);
            assert(h.generator_images[i as int] == Seq::new(1nat as nat, |_j: int| Symbol::Gen((off + i) as nat)));
            assert(apply_hom_symbol_pred(h, s) =~= seq![Symbol::Gen((off + i) as nat)]);
        },
        Symbol::Inv(i) => {
            assert(generator_index(s) == i);
            assert(h.generator_images[i as int] == Seq::new(1nat as nat, |_j: int| Symbol::Gen((off + i) as nat)));
            assert(h.generator_images[i as int] =~= seq![Symbol::Gen((off + i) as nat)]);
            lemma_inverse_singleton(Symbol::Gen((off + i) as nat));
            // inverse_word([Gen(off+i)]) == [Inv(off+i)].
            assert(apply_hom_symbol_pred(h, s) == inverse_word(h.generator_images[i as int]));
        },
    }
}

/// **`letter_digit` un-shifts the relabel.** `letter_digit(off, n, shift_sym(s,off)) ==
/// letter_digit(0, n, s)` — the `cb` offset added by ρ is exactly subtracted by `letter_digit`'s
/// `g - c_base`. (`Gen(i) ↦ i+1`, `Inv(i) ↦ i+1+n`, independent of `off`.)
pub proof fn lemma_letter_digit_unshift(off: nat, n: nat, s: Symbol)
    ensures
        letter_digit(off, n, shift_sym(s, off)) == letter_digit(0, n, s),
{
    match s {
        Symbol::Gen(i) => {
            // letter_digit(off,n,Gen(off+i)) = (off+i) - off + 1 = i+1 = letter_digit(0,n,Gen(i)).
        },
        Symbol::Inv(i) => {
            // letter_digit(off,n,Inv(off+i)) = (off+i) - off + 1 + n = i+1+n = letter_digit(0,n,Inv(i)).
        },
    }
}

/// **ρ is invisible to the word-number (the headline).** For a word `w` valid over `p1`'s generators,
/// `decode_word(off, n, m, ρ(w)) == decode_word(0, n, m, w)` where `ρ = relabel_hom(p1,p2,off)`. Induction
/// on `w`: peel the last symbol via [`lemma_hom_pred_respects_concat`], use [`lemma_relabel_symbol`]
/// (the relabel is per-symbol so `ρ(w).last() = shift_sym(w.last())`, `ρ(w).drop_last() = ρ(w.drop_last())`)
/// and [`lemma_letter_digit_unshift`].
pub proof fn lemma_decode_rho_unshift(p1: PredPresentation, p2: PredPresentation, off: nat, n: nat,
    m: nat, w: Word)
    requires
        word_valid(w, p1.num_generators),
    ensures
        decode_word(off, n, m, apply_hom_pred(relabel_hom(p1, p2, off), w)) == decode_word(0, n, m, w),
    decreases w.len(),
{
    let h = relabel_hom(p1, p2, off);
    if w.len() == 0 {
        // ρ([]) == [] ; both decode to 0.
        assert(apply_hom_pred(h, w) =~= Seq::<Symbol>::empty());
    } else {
        let last = w.last();
        let pre = w.drop_last();
        // w == pre + [last].
        assert(w =~= concat(pre, seq![last]));
        // generator_index(last) < p1.num_generators (last index of a valid word).
        assert(generator_index(last) < p1.num_generators) by {
            assert(last == w[w.len() - 1]);
        }
        // ρ(w) == ρ(pre) + ρ([last]) == ρ(pre) + [shift_sym(last,off)].
        lemma_hom_pred_respects_concat(h, pre, seq![last]);
        assert(apply_hom_pred(h, seq![last]) =~= apply_hom_symbol_pred(h, last)) by {
            assert(seq![last].len() == 1);
            assert(seq![last].first() == last);
            assert(seq![last].drop_first() =~= Seq::<Symbol>::empty());
            assert(apply_hom_pred(h, seq![last].drop_first()) =~= Seq::<Symbol>::empty());
        }
        lemma_relabel_symbol(p1, p2, off, last);
        let shifted = shift_sym(last, off);
        let rho_pre = apply_hom_pred(h, pre);
        assert(apply_hom_pred(h, w) =~= concat(rho_pre, seq![shifted]));
        // last / drop_last of (rho_pre + [shifted]).
        let rho_w = apply_hom_pred(h, w);
        assert(rho_w =~= rho_pre.push(shifted)) by {
            assert(concat(rho_pre, seq![shifted]) =~= rho_pre.push(shifted));
        }
        assert(rho_w.len() == rho_pre.len() + 1);
        assert(rho_w.last() == shifted);
        assert(rho_w.drop_last() =~= rho_pre);
        // IH on pre (valid over p1.num_generators).
        assert(word_valid(pre, p1.num_generators)) by {
            assert forall|k: int| 0 <= k < pre.len() implies
                generator_index(#[trigger] pre[k]) < p1.num_generators by {
                assert(pre[k] == w[k]);
            }
        }
        lemma_decode_rho_unshift(p1, p2, off, n, m, pre);
        lemma_letter_digit_unshift(off, n, last);
        // decode_word(off,n,m,ρ(w)) == decode_word(off,n,m,ρ(pre))·m + letter_digit(off,n,shifted)
        //   == decode_word(0,n,m,pre)·m + letter_digit(0,n,last) == decode_word(0,n,m,w).
        assert(decode_word(off, n, m, rho_w)
            == decode_word(off, n, m, rho_w.drop_last()) * m + letter_digit(off, n, rho_w.last()));
        assert(decode_word(0, n, m, w)
            == decode_word(0, n, m, w.drop_last()) * m + letter_digit(0, n, w.last()));
    }
}

// ============================================================================
// Application to relnum
// ============================================================================

/// `fam_relator(a,b)` is a word over the 2 generators `{a = Gen(0), t = Gen(1)}` (the collapse
/// alphabet). The embedding images (`miller_collapse_word`s + `a`/`b`/`t`) are all `{a,t}`-words, and
/// `apply_embedding` preserves validity.
pub proof fn lemma_fam_relator_word_valid(a: nat, b: nat)
    ensures
        word_valid(fam_relator(a, b), 2),
{
    let big = rel_slice(a, b);
    let images = miller_collapse_emb(big, 0, 1);
    let w = ceer_to_word(ceer_relator(a, b));
    // images.len() == big + 3.
    assert(images.len() == big + 3) by {
        assert(Seq::new(big, |j: int| miller_collapse_word(j as nat, 0, 1)).len() == big);
    }
    // w = [Gen(a), Inv(b)] is valid over images.len() (a, b < big ≤ big+3).
    assert(a < big && b < big);
    lemma_ceer_relator_word_valid(a, b, images.len());
    // every image is a valid {a,t}-word (over 2 generators).
    assert forall|i: int| 0 <= i < images.len() implies word_valid(#[trigger] images[i], 2) by {
        if i < big {
            assert(images[i] == miller_collapse_word(i as nat, 0, 1));
            lemma_miller_collapse_word_valid(i as nat, 0, 1, 2);
        } else if i == big {
            // a ↦ [Gen(0)].
            assert(images[i] =~= seq![Symbol::Gen(0nat)]);
        } else if i == big + 1 {
            // b ↦ t a t⁻¹ = b_sub(0,1).
            assert(images[i] == b_sub(0, 1));
            assert forall|k: int| 0 <= k < b_sub(0, 1).len()
                implies #[trigger] generator_index(b_sub(0, 1)[k]) < 2 by { }
        } else {
            // t ↦ [Gen(1)].
            assert(i == big + 2);
            assert(images[i] =~= seq![Symbol::Gen(1nat)]);
        }
    }
    lemma_apply_embedding_valid(images, w, 2);
}

/// **The emitter's reduced spec target.** `relnum(e,mm,m,a,b) == decode_word(0, 2, m, fam_relator(a,b))`
/// — ρ removed. The R-relnum-gen emitter need only generate the digits of the *un-relabeled* collapsed
/// relator `fam_relator(a,b) = u_a · u_b⁻¹` over `{a→1, t→2, a⁻¹→3, t⁻¹→4}`.
pub proof fn lemma_relnum_no_rho(e: CEER, mm: ModMachine, m: nat, a: nat, b: nat)
    ensures
        relnum(e, mm, m, a, b) == decode_word(0, 2, m, fam_relator(a, b)),
{
    let cb = cb_of(mm);
    let p1 = p1_of(e);
    let p2 = p2_of(mm, m);
    // p1_of(e) = p_infty(...) has num_generators == 2.
    assert(p1.num_generators == 2) by {
        assert(p1 == p_infty(ceer_decls_fam(e)));
    }
    lemma_fam_relator_word_valid(a, b);
    // relnum = decode_word(cb, 2, m, ρ(fam_relator)) = decode_word(cb,2,m, apply_hom_pred(relabel_hom(p1,p2,cb), fam_relator)).
    assert(rho(e, mm, m, fam_relator(a, b))
        == apply_hom_pred(relabel_hom(p1, p2, cb), fam_relator(a, b)));
    lemma_decode_rho_unshift(p1, p2, cb, 2, m, fam_relator(a, b));
}

/// **Consolidated emitter spec target (capstone).** `relnum(e,mm,m,a,b) ==
/// dpack(decode_digit_seq(0, 2, fam_relator(a,b)), m)` — relnum is exactly the base-`m` number whose
/// low-first digit block is the reversed letter-digits of the *un-relabeled* collapse relator
/// `u_a · u_b⁻¹` (digits over `{a→1, t→2, a⁻¹→3, t⁻¹→4}`). Composes [`lemma_relnum_no_rho`] (ρ removed)
/// with [`lemma_decode_word_is_dpack`] (`decode_word == dpack ∘ decode_digit_seq`). This is the single
/// fact the R-relnum-gen emitter and the R-cmp compare are proved against.
pub proof fn lemma_relnum_is_decode_digit_seq(e: CEER, mm: ModMachine, m: nat, a: nat, b: nat)
    ensures
        relnum(e, mm, m, a, b) == dpack(decode_digit_seq(0, 2, fam_relator(a, b)), m),
{
    lemma_relnum_no_rho(e, mm, m, a, b);                 // relnum == decode_word(0,2,m,fam_relator)
    lemma_decode_word_is_dpack(0, 2, m, fam_relator(a, b));   // decode_word == dpack(decode_digit_seq)
}

} // verus!
