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

} // verus!
