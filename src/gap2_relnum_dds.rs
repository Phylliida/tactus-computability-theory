//! # GAP-2 R-relnum-gen — the digit-sequence structural library (Production-proof side).
//!
//! Per the (B) digit-seq design (Danielle, port 8051): the emitter's correctness splits into a
//! **Production Proof** (TM ⟹ tape holds an explicit `decode_digit_seq` block concatenation) and an
//! **Evaluation Proof** (`dpack` of those digits == the `relnum` value, via the numeric closed forms in
//! [`crate::gap2_relnum_digits`]). This module is the Production side's algebra: how `decode_digit_seq`
//! distributes over the word constructors `++`, `word_power`, `symbol_power`, and singletons — so the
//! collapse relator `fam_relator(a,b) = u_a ++ inverse_word(u_b)` decomposes into the explicit digit
//! blocks the emitter lays down one loop iteration at a time.
//!
//! KEY: `decode_digit_seq` peels the LAST symbol as the LOWEST digit (dpack/low-first order), so it
//! **reverses** — `dds(w1 ++ w2) == dds(w2) ++ dds(w1)` ([`lemma_dds_concat`]). The emitter therefore
//! emits the reversed (low-first) order; the plan's "forward pattern" is human intuition only.
//!
//! `docs/gap2-input-loader-plan.md` §5 (R-relnum-gen). Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::word::{Word, empty_word};
use verus_group_theory::symbol::Symbol;
use verus_group_theory::machine_group::{word_power, symbol_power};
use verus_group_theory::word_numbering_decode::letter_digit;
use crate::gap2_relnum_digits::decode_digit_seq;

verus! {

/// Generic `k`-fold concatenation of a `Seq<A>` — the element-type-agnostic analog of
/// [`word_power`](verus_group_theory::machine_group::word_power) for digit sequences (`Seq<nat>`).
pub open spec fn seq_pow<A>(s: Seq<A>, k: nat) -> Seq<A>
    decreases k,
{
    if k == 0 { Seq::<A>::empty() } else { s + seq_pow(s, (k - 1) as nat) }
}

/// **`seq_pow` snoc form.** `seq_pow(s,k) =~= seq_pow(s,k-1) + s` (k ≥ 1) — the generic analog of
/// `lemma_word_power_snoc`; the last copy peels off the right. Induction via concatenation associativity.
pub proof fn lemma_seq_pow_snoc<A>(s: Seq<A>, k: nat)
    requires
        k >= 1,
    ensures
        seq_pow(s, k) =~= seq_pow(s, (k - 1) as nat) + s,
    decreases k,
{
    if k == 1 {
        assert(seq_pow(s, 1) == s + seq_pow(s, 0));
        assert(seq_pow(s, 0) =~= Seq::<A>::empty());
        assert(seq_pow(s, 1) =~= s);
        assert(seq_pow(s, 0) + s =~= s);
    } else {
        let k1 = (k - 1) as nat;
        lemma_seq_pow_snoc(s, k1);   // seq_pow(s,k1) == seq_pow(s,k1-1) + s
        assert(seq_pow(s, k) == s + seq_pow(s, k1));
        assert(s + seq_pow(s, k1) =~= s + (seq_pow(s, (k1 - 1) as nat) + s));
        assert(s + (seq_pow(s, (k1 - 1) as nat) + s) =~= (s + seq_pow(s, (k1 - 1) as nat)) + s);
        assert(s + seq_pow(s, (k1 - 1) as nat) == seq_pow(s, k1));
        assert(seq_pow(s, k) =~= seq_pow(s, k1) + s);
    }
}

/// **`decode_digit_seq` over concatenation (the REVERSAL law).** Since `decode_digit_seq` makes the LAST
/// symbol the LOWEST digit, the low digits of `w1 ++ w2` come from `w2`:
/// `dds(w1 ++ w2) == dds(w2) ++ dds(w1)`. The tool for decomposing `fam_relator = u_a ++ inverse_word(u_b)`
/// (and each `u_j` into its eight pieces) into emitter digit blocks. Induction on `w2` (peeling its last
/// symbol = the whole word's last).
pub proof fn lemma_dds_concat(c_base: nat, n: nat, w1: Word, w2: Word)
    ensures
        decode_digit_seq(c_base, n, w1 + w2)
            =~= decode_digit_seq(c_base, n, w2) + decode_digit_seq(c_base, n, w1),
    decreases w2.len(),
{
    if w2.len() == 0 {
        assert(w1 + w2 =~= w1);
        assert(decode_digit_seq(c_base, n, w2) =~= Seq::<nat>::empty());
        assert(decode_digit_seq(c_base, n, w1 + w2) =~= decode_digit_seq(c_base, n, w1));
        assert(decode_digit_seq(c_base, n, w2) + decode_digit_seq(c_base, n, w1)
            =~= decode_digit_seq(c_base, n, w1));
    } else {
        let pre2 = w2.drop_last();
        let last2 = w2.last();
        assert((w1 + w2).len() > 0);
        assert((w1 + w2).last() == last2);
        assert((w1 + w2).drop_last() =~= w1 + pre2);
        let d = letter_digit(c_base, n, last2);
        // dds(w1+w2) = [d] + dds(w1 + pre2)   (peel the shared last symbol)
        assert(decode_digit_seq(c_base, n, w1 + w2)
            =~= seq![d] + decode_digit_seq(c_base, n, w1 + pre2));
        lemma_dds_concat(c_base, n, w1, pre2);   // IH: dds(w1+pre2) == dds(pre2) + dds(w1)
        // dds(w2) = [d] + dds(pre2)
        assert(decode_digit_seq(c_base, n, w2) =~= seq![d] + decode_digit_seq(c_base, n, pre2));
        // [d] + (dds(pre2)+dds(w1)) =~= ([d]+dds(pre2)) + dds(w1) = dds(w2)+dds(w1)
        assert(seq![d] + (decode_digit_seq(c_base, n, pre2) + decode_digit_seq(c_base, n, w1))
            =~= (seq![d] + decode_digit_seq(c_base, n, pre2)) + decode_digit_seq(c_base, n, w1));
    }
}

/// **`decode_digit_seq` of a singleton.** `dds([s]) == [letter_digit(s)]` — the digit of the single-symbol
/// pieces (`t`, `a`, `t⁻¹`, `a⁻¹`) of `u_j`.
pub proof fn lemma_dds_singleton(c_base: nat, n: nat, s: Symbol)
    ensures
        decode_digit_seq(c_base, n, seq![s]) =~= seq![letter_digit(c_base, n, s)],
{
    assert(seq![s].len() == 1);
    assert(seq![s].last() == s);
    assert(seq![s].drop_last() =~= empty_word());
    assert(decode_digit_seq(c_base, n, empty_word()) =~= Seq::<nat>::empty());
}

/// **`decode_digit_seq` of a `word_power` block.** `dds(word_power(w,k)) == seq_pow(dds(w), k)` — the digit
/// block of `w` repeated `k` times (the per-block inner-loop production target for the
/// `(t a⁻¹ t⁻¹)ⁱ`/`(t a t⁻¹)ⁱ` blocks). Induction on `k` via [`lemma_dds_concat`] (reversal) +
/// [`lemma_seq_pow_snoc`] (the reversal and the snoc cancel: the LOW copy peels onto the right of both).
pub proof fn lemma_dds_word_power(c_base: nat, n: nat, w: Word, k: nat)
    ensures
        decode_digit_seq(c_base, n, word_power(w, k)) =~= seq_pow(decode_digit_seq(c_base, n, w), k),
    decreases k,
{
    let dw = decode_digit_seq(c_base, n, w);
    if k == 0 {
        assert(word_power(w, 0) =~= empty_word());
        assert(decode_digit_seq(c_base, n, empty_word()) =~= Seq::<nat>::empty());
        assert(seq_pow(dw, 0) =~= Seq::<nat>::empty());
    } else {
        let k1 = (k - 1) as nat;
        assert(word_power(w, k) == w + word_power(w, k1));
        lemma_dds_concat(c_base, n, w, word_power(w, k1));   // dds(w + wp(k1)) == dds(wp(k1)) + dds(w)
        lemma_dds_word_power(c_base, n, w, k1);              // IH: dds(wp(k1)) == seq_pow(dw, k1)
        lemma_seq_pow_snoc(dw, k);                           // seq_pow(dw,k) == seq_pow(dw,k1) + dw
        assert(decode_digit_seq(c_base, n, word_power(w, k)) =~= seq_pow(dw, k));
    }
}

/// **`decode_digit_seq` of a `symbol_power` block.** `dds(symbol_power(s,k)) ==
/// seq_pow([letter_digit(s)], k)` — a constant digit repeated `k` times (the `a⁻ⁱ = (3)ⁱ` and `aⁱ = (1)ⁱ`
/// blocks of `u_j`). Direct induction (`symbol_power(s,k).drop_last() = symbol_power(s,k-1)`, `.last() =
/// s`).
pub proof fn lemma_dds_symbol_power(c_base: nat, n: nat, s: Symbol, k: nat)
    ensures
        decode_digit_seq(c_base, n, symbol_power(s, k))
            =~= seq_pow(seq![letter_digit(c_base, n, s)], k),
    decreases k,
{
    let d = letter_digit(c_base, n, s);
    if k == 0 {
        assert(symbol_power(s, 0) =~= empty_word());
        assert(decode_digit_seq(c_base, n, empty_word()) =~= Seq::<nat>::empty());
        assert(seq_pow(seq![d], 0) =~= Seq::<nat>::empty());
    } else {
        let k1 = (k - 1) as nat;
        assert(symbol_power(s, k).last() == s);
        assert(symbol_power(s, k).drop_last() =~= symbol_power(s, k1));
        lemma_dds_symbol_power(c_base, n, s, k1);   // IH: dds(sp(k1)) == seq_pow([d], k1)
        assert(decode_digit_seq(c_base, n, symbol_power(s, k))
            =~= seq![d] + decode_digit_seq(c_base, n, symbol_power(s, k1)));
        assert(seq_pow(seq![d], k) == seq![d] + seq_pow(seq![d], k1));
    }
}

} // verus!
