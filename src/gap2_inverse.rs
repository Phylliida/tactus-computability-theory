//! # GAP-2 R-relnum-gen — `inverse_word` over the block constructors (the 8-piece rewrite prep).
//!
//! `fam_relator(a,b) = u_a ++ inverse_word(u_b)`. Per Danielle's (B) design, the `inverse_word(u_b)` half
//! is handled by **structurally rewriting it back into the same primitive shapes as `u_a`** (singletons +
//! `word_power`/`symbol_power` blocks), so the digit-seq piece-lemmas ([`crate::gap2_relnum_dds`]) reapply
//! verbatim. This module supplies the two block-level distribution laws `inverse_word` obeys:
//!
//!   - `inverse_word(symbol_power(s,k)) == symbol_power(inverse_symbol(s), k)`  (reverse of a constant run
//!     is the same constant run, inverted);
//!   - `inverse_word(word_power(w,k)) == word_power(inverse_word(w), k)`        (reverse of a repeat is the
//!     repeat of the reverse — the reversal of factor ORDER cancels against the snoc, since all factors
//!     are equal).
//!
//! `docs/gap2-input-loader-plan.md` §5 (R-relnum-gen, the inverse_word(u_b) rewrite). Fully verified, no
//! verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::word::{Word, empty_word, inverse_word, concat, lemma_inverse_concat};
use verus_group_theory::symbol::{Symbol, inverse_symbol};
use verus_group_theory::machine_group::{word_power, symbol_power};
use crate::gap2_relnum_digits::lemma_word_power_snoc;

verus! {

/// **`inverse_word` of a `symbol_power` run.** `inverse_word(symbol_power(s,k)) ==
/// symbol_power(inverse_symbol(s), k)` — reversing `k` copies of `s` (and inverting each) is `k` copies of
/// `s⁻¹`. Direct induction via `inverse_word`'s `drop_first` recurrence (`symbol_power(s,k).first() = s`,
/// `.drop_first() = symbol_power(s,k-1)`).
pub proof fn lemma_inverse_symbol_power(s: Symbol, k: nat)
    ensures
        inverse_word(symbol_power(s, k)) =~= symbol_power(inverse_symbol(s), k),
    decreases k,
{
    let invs = inverse_symbol(s);
    if k == 0 {
        assert(symbol_power(s, 0) =~= empty_word());
        assert(inverse_word(empty_word()) =~= empty_word());
        assert(symbol_power(invs, 0) =~= empty_word());
    } else {
        let k1 = (k - 1) as nat;
        assert(symbol_power(s, k).len() == k);
        assert(symbol_power(s, k).first() == s) by {
            assert(symbol_power(s, k)[0] == s);
        }
        assert(symbol_power(s, k).drop_first() =~= symbol_power(s, k1));
        lemma_inverse_symbol_power(s, k1);   // IH: inverse_word(sp(s,k1)) == sp(invs, k1)
        // inverse_word(sp(s,k)) = inverse_word(sp(s,k1)) + [invs] = sp(invs,k1) + [invs] = sp(invs,k)
        assert(inverse_word(symbol_power(s, k))
            =~= inverse_word(symbol_power(s, k1)) + Seq::new(1, |_i: int| invs));
        assert(symbol_power(invs, k1) + Seq::new(1, |_i: int| invs) =~= symbol_power(invs, k));
    }
}

/// **`inverse_word` of a `word_power` block.** `inverse_word(word_power(w,k)) ==
/// word_power(inverse_word(w), k)` — reversing `k` copies of `w` reverses the FACTOR order, but since all
/// factors are equal that order is symmetric; what remains is each factor reversed. So
/// `inverse_word(b^k) = binv^k`, `inverse_word(binv^k) = b^k`. Induction on `k` via
/// [`lemma_inverse_concat`] (the reversal) + [`lemma_word_power_snoc`] (which absorbs it).
pub proof fn lemma_inverse_word_power(w: Word, k: nat)
    ensures
        inverse_word(word_power(w, k)) =~= word_power(inverse_word(w), k),
    decreases k,
{
    let iw = inverse_word(w);
    if k == 0 {
        assert(word_power(w, 0) =~= empty_word());
        assert(inverse_word(empty_word()) =~= empty_word());
        assert(word_power(iw, 0) =~= empty_word());
    } else {
        let k1 = (k - 1) as nat;
        assert(word_power(w, k) == concat(w, word_power(w, k1)));   // w + wp(w,k1)
        lemma_inverse_concat(w, word_power(w, k1));
        // inverse_word(w + wp(k1)) =~= inverse_word(wp(k1)) + inverse_word(w)
        lemma_inverse_word_power(w, k1);          // IH: inverse_word(wp(k1)) == wp(iw, k1)
        lemma_word_power_snoc(iw, k);             // wp(iw,k) == wp(iw,k1) + iw
        assert(inverse_word(word_power(w, k)) =~= word_power(iw, k1) + iw);
    }
}

} // verus!
