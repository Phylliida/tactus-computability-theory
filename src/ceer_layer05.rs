//! Layer 0.5 wiring — instantiate the abstract Miller embedding `C₀ ↪ C`
//! (`verus_group_theory::cohen_layer05::lemma_c0_embeds_in_c_iff`) with the *actual* CEER
//! group's declared relators.
//!
//! `cohen_layer05` proves the embedding for an ABSTRACT declared-relator family
//! `fam: spec_fn(nat) -> Seq<Word>` satisfying `decls_family_valid`. Here we supply the
//! concrete family coming from the CEER enumerator: at "level `M`" the declared relators are
//! `Gen(a)·Inv(b)⁻¹`-style words `[Gen(a), Inv(b)]` for every stage `s < M` whose declared
//! pair `(a,b)` already fits in the `M`-generator slice (`a,b < M`); other stages contribute
//! the inert empty relator. As `M → ∞` this exhausts every declared pair, so the direct-limit
//! group `C₀` of these slices IS the CEER group `⟨gₙ | gₐgᵦ⁻¹ : a~b⟩`.
//!
//! Alphabet translation: the CEER group uses its own `CeerSymbol{Gen,Inv}` infinite alphabet;
//! `verus_group_theory` uses `Symbol{Gen(nat),Inv(nat)}`. `ceer_to_word` is the (index-preserving)
//! bijection on symbols, lifted to words.

use vstd::prelude::*;
use crate::ceer::*;
use crate::ceer_group::*;
use verus_group_theory::symbol::*;
use verus_group_theory::word::{Word, empty_word, word_valid};
use verus_group_theory::cohen_layer05::{decls_family_valid, equiv_in_g_limit, equiv_in_c0_limit,
    lemma_c0_embeds_in_c_iff};
use verus_group_theory::benign::apply_embedding;
use verus_group_theory::miller_collapse::miller_collapse_emb;
use verus_group_theory::miller_collapse_preserve::dbar;
use verus_group_theory::miller_collapse_limit::{dbar_family_monotone, p_infty,
    lemma_emb_slice_independent, lemma_seq_index_contains, lemma_limit_commutation};
use verus_group_theory::pred_presentation::equiv_in_pred_presentation;

verus! {

// ===========================================================================
// 1. Alphabet translation  CeerSymbol → Symbol,  CeerWord → Word.
// ===========================================================================

/// Translate a CEER symbol to a `verus_group_theory` symbol (index-preserving).
pub open spec fn ceer_sym_to_sym(s: CeerSymbol) -> Symbol {
    match s {
        CeerSymbol::Gen { index } => Symbol::Gen(index),
        CeerSymbol::Inv { index } => Symbol::Inv(index),
    }
}

/// Translate a CEER word to a `verus_group_theory` word.
pub open spec fn ceer_to_word(w: CeerWord) -> Word {
    Seq::new(w.len(), |i: int| ceer_sym_to_sym(w[i]))
}

// ===========================================================================
// 2. The concrete declared-relator family.
// ===========================================================================

/// The relator contributed by stage `s` at level `big_m`: the translated CEER relator
/// `[Gen(a), Inv(b)]` if stage `s` declares `(a,b)` with both indices in range, else the
/// (inert) empty relator.
pub open spec fn ceer_relator_at(e: CEER, s: nat, big_m: nat) -> Word {
    match declared_pair(e, s) {
        Some(pair) =>
            if pair.0 < big_m && pair.1 < big_m {
                ceer_to_word(ceer_relator(pair.0, pair.1))
            } else {
                empty_word()
            },
        None => empty_word(),
    }
}

/// The declared-relator slice at level `big_m`: one entry per stage `s < big_m`.
pub open spec fn ceer_decls_fam_at(e: CEER, big_m: nat) -> Seq<Word> {
    Seq::new(big_m, |s: int| ceer_relator_at(e, s as nat, big_m))
}

/// The monotone declared-relator family for the CEER group `e`, as the abstract Miller
/// family `cohen_layer05` is parameterized over.
pub open spec fn ceer_decls_fam(e: CEER) -> spec_fn(nat) -> Seq<Word> {
    |big_m: nat| ceer_decls_fam_at(e, big_m)
}

// ===========================================================================
// 3. Validity of the family.
// ===========================================================================

/// Every contributed relator is a valid word over the `big_m`-generator slice: the empty
/// relator trivially, and a real relator `[Gen(a), Inv(b)]` because the `ceer_relator_at`
/// guard forces `a, b < big_m`.
pub proof fn lemma_ceer_relator_at_valid(e: CEER, s: nat, big_m: nat)
    ensures
        word_valid(ceer_relator_at(e, s, big_m), big_m),
{
    match declared_pair(e, s) {
        Some(pair) => {
            if pair.0 < big_m && pair.1 < big_m {
                let a = pair.0;
                let b = pair.1;
                let rel = ceer_relator(a, b);
                let w = ceer_to_word(rel);
                // rel = [Gen{a}, Inv{b}], so w = [Symbol::Gen(a), Symbol::Inv(b)], length 2.
                assert(rel.len() == 2);
                assert(w.len() == 2);
                assert(w[0] == Symbol::Gen(a));
                assert(w[1] == Symbol::Inv(b));
                assert forall|i: int| 0 <= i < w.len() implies
                    symbol_valid(#[trigger] w[i], big_m) by {
                    if i == 0 {
                        assert(generator_index(w[0]) == a);
                    } else {
                        assert(i == 1);
                        assert(generator_index(w[1]) == b);
                    }
                }
                assert(word_valid(w, big_m));
            } else {
                assert(ceer_relator_at(e, s, big_m) == empty_word());
            }
        },
        None => {
            assert(ceer_relator_at(e, s, big_m) == empty_word());
        },
    }
}

/// The CEER declared-relator family satisfies `decls_family_valid` — every level-`M` relator
/// is a valid word over `M` generators.
pub proof fn lemma_ceer_decls_family_valid(e: CEER)
    ensures
        decls_family_valid(ceer_decls_fam(e)),
{
    assert forall|big_m: nat, j: int| 0 <= j < ceer_decls_fam(e)(big_m).len() implies
        word_valid(#[trigger] ceer_decls_fam(e)(big_m)[j], big_m) by {
        // ceer_decls_fam(e)(big_m) = ceer_decls_fam_at(e, big_m) = Seq::new(big_m, ...)
        assert(ceer_decls_fam(e)(big_m) == ceer_decls_fam_at(e, big_m));
        assert(ceer_decls_fam(e)(big_m)[j] == ceer_relator_at(e, j as nat, big_m));
        lemma_ceer_relator_at_valid(e, j as nat, big_m);
    }
}

// ===========================================================================
// 4. Consume the Miller embedding for the concrete CEER family.
// ===========================================================================

/// **THE LAYER-0.5 EMBEDDING, INSTANTIATED FOR THE CEER GROUP.** For any CEER word `w` whose
/// generators all fit in the `n`-generator slice, triviality in the direct-limit finitely
/// generated recursively-presented Miller group `C` is EQUIVALENT to triviality in the
/// countable CEER group `C₀` — both taken over the concrete declared-relator family
/// `ceer_decls_fam(e)`. This is `lemma_c0_embeds_in_c_iff` specialized to the real CEER group.
pub proof fn lemma_ceer_c0_embeds_in_c_iff(e: CEER, n: nat, w: CeerWord)
    requires
        word_valid(ceer_to_word(w), n),
    ensures
        equiv_in_g_limit(ceer_decls_fam(e), n, ceer_to_word(w), empty_word())
            <==> equiv_in_c0_limit(ceer_decls_fam(e), n, ceer_to_word(w), empty_word()),
{
    lemma_ceer_decls_family_valid(e);
    lemma_c0_embeds_in_c_iff(ceer_decls_fam(e), n, ceer_to_word(w));
}

// ===========================================================================
// 5. Directedness (`dbar_family_monotone`) of the concrete CEER family, and the
//    limit-commutation iff instantiated for it (GAP-1 item-3a, concrete).
// ===========================================================================

/// A non-empty contributed relator is *stable* across slices: once a stage `s` declares a pair
/// that fits the `m1`-slice, it declares the SAME relator at every larger slice `m2 ≥ m1`.
proof fn lemma_ceer_relator_at_stable(e: CEER, s: nat, m1: nat, m2: nat)
    requires
        ceer_relator_at(e, s, m1) != empty_word(),
        m1 <= m2,
    ensures
        ceer_relator_at(e, s, m2) == ceer_relator_at(e, s, m1),
{
    match declared_pair(e, s) {
        Some(pair) => {
            // non-empty at m1 forces the fitting branch: pair.0 < m1 && pair.1 < m1
            if !(pair.0 < m1 && pair.1 < m1) {
                assert(ceer_relator_at(e, s, m1) == empty_word());
            }
            assert(pair.0 < m1 && pair.1 < m1);
            // a, b < m1 <= m2, so the m2 evaluation also takes the fitting branch with the same pair
            assert(pair.0 < m2 && pair.1 < m2);
        },
        None => {
            assert(ceer_relator_at(e, s, m1) == empty_word());
        },
    }
}

/// **DIRECTEDNESS of the CEER family.** A non-empty collapsed relator visible at slice `m1` is
/// visible at every larger slice `m2 ≥ m1`. The empty/trivial relator is excluded by the weakened
/// `dbar_family_monotone` (it is administrative padding, not slice-monotone — see the group-theory
/// `dbar_family_monotone` doc). The genuine relators `u_a·u_b⁻¹` are slice-independent
/// (`lemma_emb_slice_independent`), hence stable.
proof fn lemma_ceer_dbar_mono_at(e: CEER, m1: nat, m2: nat, r: Word)
    requires
        r != empty_word(),
        m1 <= m2,
        dbar(m1, ceer_decls_fam(e)(m1)).contains(r),
    ensures
        dbar(m2, ceer_decls_fam(e)(m2)).contains(r),
{
    let fam = ceer_decls_fam(e);
    assert(fam(m1) == ceer_decls_fam_at(e, m1));
    assert(fam(m2) == ceer_decls_fam_at(e, m2));
    let d1 = dbar(m1, fam(m1));
    let emb1 = miller_collapse_emb(m1, 0, 1);
    let emb2 = miller_collapse_emb(m2, 0, 1);

    // 1. unfold contains: pick a witness index s into d1
    assert(d1.len() == m1);
    let s = choose|s: int| 0 <= s < d1.len() && d1[s] == r;
    assert(0 <= s < d1.len() && d1[s] == r);
    let rel1 = ceer_relator_at(e, s as nat, m1);
    assert(d1[s] == apply_embedding(emb1, rel1));

    // 2. r != empty ⟹ rel1 != empty (apply_embedding maps empty to empty)
    assert(rel1 != empty_word()) by {
        if rel1 == empty_word() {
            assert(apply_embedding(emb1, empty_word()) == empty_word());
        }
    }

    // 3. the relator is the same at m2, and is valid over the m1-slice
    lemma_ceer_relator_at_stable(e, s as nat, m1, m2);
    assert(ceer_relator_at(e, s as nat, m2) == rel1);
    lemma_ceer_relator_at_valid(e, s as nat, m1);   // word_valid(rel1, m1)

    // 4. slice independence: apply_embedding(emb2, rel1) == apply_embedding(emb1, rel1) == r
    lemma_emb_slice_independent(m1, m2, rel1);
    assert(apply_embedding(emb2, rel1) == apply_embedding(emb1, rel1));

    // 5. d2[s] == r, and s < m1 <= m2 is a valid index ⟹ d2.contains(r)
    let d2 = dbar(m2, fam(m2));
    assert(d2.len() == m2);
    assert(0 <= s < m2);
    assert(d2[s] == apply_embedding(emb2, ceer_relator_at(e, s as nat, m2)));
    assert(d2[s] == r);
    lemma_seq_index_contains(d2, s);
}

/// The CEER declared-relator family is directed (`dbar_family_monotone`) — the second hypothesis
/// of `lemma_limit_commutation`, now TRUE & provable thanks to the empty-relator-robust weakening.
pub proof fn lemma_ceer_dbar_family_monotone(e: CEER)
    ensures
        dbar_family_monotone(ceer_decls_fam(e)),
{
    let fam = ceer_decls_fam(e);
    assert forall|m1: nat, m2: nat, r: Word|
        #![trigger dbar(m1, fam(m1)).contains(r), dbar(m2, fam(m2)).contains(r)]
        r != empty_word() && m1 <= m2 && dbar(m1, fam(m1)).contains(r)
        implies dbar(m2, fam(m2)).contains(r) by {
        lemma_ceer_dbar_mono_at(e, m1, m2, r);
    }
}

/// **GAP-1 ITEM-3a, INSTANTIATED FOR THE CEER GROUP.** The limit-commutation iff for the concrete
/// CEER declared-relator family: triviality of a CEER word in the direct-limit Miller group `C`
/// equals triviality of its Miller-collapse image in the fixed-`{a,t}` union presentation
/// `P_∞ = ⟨a,t | ⋃_M D̄_M⟩`. Both family hypotheses (`decls_family_valid`, `dbar_family_monotone`)
/// are discharged for `ceer_decls_fam(e)`; this leaves only the machine-gated relator-set match
/// `⋃_M D̄_M ↔ is_S_canonical(mm,…)` (item-3b, needs GAP-2's modular machine).
pub proof fn lemma_ceer_limit_commutation(e: CEER, n: nat, w: CeerWord)
    requires
        word_valid(ceer_to_word(w), n),
    ensures
        equiv_in_g_limit(ceer_decls_fam(e), n, ceer_to_word(w), empty_word())
            <==> equiv_in_pred_presentation(p_infty(ceer_decls_fam(e)),
                    apply_embedding(miller_collapse_emb(n, 0, 1), ceer_to_word(w)), empty_word()),
{
    lemma_ceer_decls_family_valid(e);
    lemma_ceer_dbar_family_monotone(e);
    lemma_limit_commutation(ceer_decls_fam(e), n, ceer_to_word(w));
}

} // verus!
