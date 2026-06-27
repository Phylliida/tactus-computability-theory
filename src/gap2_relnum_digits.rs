//! # GAP-2 G2-F Route (i) brick R-relnum-gen (spec foundation) — `relnum` as a `dpack` digit sequence.
//!
//! The relator-decider TM `psc_tm(e)` accepts `α` iff `α == relnum(a,b)` for some declared pair, where
//! [`relnum`](crate::gap2_relnum::relnum)`= decode_word(cb, 2, m, ρ(fam_relator(a,b)))`. The machine
//! holds numbers on the tape as base-`m` **`dpack`** digit blocks ([`crate::tm_dstring`]); to compare
//! `α` against `relnum` it must know `relnum` *as a `dpack` of explicit digits*. This module supplies the
//! linchpin: `decode_word` and `dpack` describe the same number, with the digit ORDER pinned down.
//!
//! [`decode_word`] folds the **last** symbol of the word as the **lowest** base-`m` digit
//! (`decode(w) = decode(w.drop_last())·m + letter_digit(w.last())`); `dpack` packs `ds[0]` as the lowest
//! digit. So the `dpack` digit sequence of a word's word-number is the **reversed** letter-digit
//! sequence — [`decode_digit_seq`]. The headline [`lemma_decode_word_is_dpack`] proves
//! `decode_word(c_base,n,m,w) == dpack(decode_digit_seq(c_base,n,w), m)`, and [`lemma_relnum_is_dpack`]
//! specializes it to `relnum`. This resolves the plan's ⚠ digit-order question and gives the emitter
//! (R-relnum-gen) its exact target and the compare (R-cmp) its exact invariant.
//!
//! For `n = 2` (the `{a,t}` collapse alphabet) the letter-digits land in `1..4` — fitting the n=4 tape
//! ([`lemma_decode_digit_seq_bound`]) — and the block length equals the word length
//! ([`lemma_decode_digit_seq_len`]).
//!
//! `docs/gap2-input-loader-plan.md` §5 (R-relnum-gen). Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::word::Word;
use verus_group_theory::word_numbering_decode::{decode_word, letter_digit, in_c_block,
    c_alphabet_word, lemma_alphabet_letter_section};
use verus_group_theory::machine_group::ModMachine;
use crate::ceer::CEER;
use crate::gap2_relnum::{relnum, fam_relator};
use crate::ceer_relator_match::{cb_of, rho};
use crate::tm_dstring::{dpack, lemma_dpack_push, lemma_dpack_empty};

verus! {

/// The low-first base-`m` digit sequence of a c-block word's word-number: the letter-digits of `w`'s
/// symbols in **reversed** order (since `decode_word` makes the LAST symbol the LOWEST digit).
/// `decode_digit_seq(w) = [letter_digit(w.last())] ++ decode_digit_seq(w.drop_last())` — built to match
/// `dpack`'s low-first push recurrence one for one.
pub open spec fn decode_digit_seq(c_base: nat, n: nat, w: Word) -> Seq<nat>
    decreases w.len()
{
    if w.len() == 0 {
        Seq::empty()
    } else {
        seq![letter_digit(c_base, n, w.last())] + decode_digit_seq(c_base, n, w.drop_last())
    }
}

/// The digit block has one digit per symbol.
pub proof fn lemma_decode_digit_seq_len(c_base: nat, n: nat, w: Word)
    ensures
        decode_digit_seq(c_base, n, w).len() == w.len(),
    decreases w.len()
{
    if w.len() == 0 {
    } else {
        lemma_decode_digit_seq_len(c_base, n, w.drop_last());
        assert(decode_digit_seq(c_base, n, w)
            == seq![letter_digit(c_base, n, w.last())] + decode_digit_seq(c_base, n, w.drop_last()));
    }
}

/// **The `decode_word` ↔ `dpack` bridge (digit-order linchpin).** A word's word-number is the base-`m`
/// number whose low-first digit sequence is the reversed letter-digits of the word:
/// `decode_word(c_base,n,m,w) == dpack(decode_digit_seq(c_base,n,w), m)`. Clean induction on `w` — both
/// recurrences peel one end (`decode_word` the last symbol, `dpack`/`decode_digit_seq` the low digit).
pub proof fn lemma_decode_word_is_dpack(c_base: nat, n: nat, m: nat, w: Word)
    ensures
        decode_word(c_base, n, m, w) == dpack(decode_digit_seq(c_base, n, w), m),
    decreases w.len()
{
    if w.len() == 0 {
        lemma_dpack_empty(m);
        // decode_word([]) == 0 == dpack(empty).
    } else {
        let d0 = letter_digit(c_base, n, w.last());
        let rest = decode_digit_seq(c_base, n, w.drop_last());
        assert(decode_digit_seq(c_base, n, w) == seq![d0] + rest);
        lemma_decode_word_is_dpack(c_base, n, m, w.drop_last());   // IH: decode_word(drop_last) == dpack(rest)
        lemma_dpack_push(d0, rest, m);                             // dpack([d0]+rest) == d0 + m·dpack(rest)
        // decode_word(w) == decode_word(drop_last)·m + d0 == m·dpack(rest) + d0 == d0 + m·dpack(rest).
        assert(decode_word(c_base, n, m, w) == decode_word(c_base, n, m, w.drop_last()) * m + d0);
        assert(decode_word(c_base, n, m, w.drop_last()) * m == m * dpack(rest, m)) by(nonlinear_arith)
            requires decode_word(c_base, n, m, w.drop_last()) == dpack(rest, m);
    }
}

/// **Digit bound.** For a c-block word `w` (letters `c_i^{±1}`, `1 ≤ i ≤ n`), every digit of
/// `decode_digit_seq(c_base,n,w)` lies in `1..=2n` — so for `n = 2` (the collapse alphabet) the digits
/// fit the n=4 relator-decider tape. By induction; the head digit is `letter_digit(w.last())` (in range
/// via [`lemma_alphabet_letter_section`]).
pub proof fn lemma_decode_digit_seq_bound(c_base: nat, n: nat, w: Word)
    requires
        c_alphabet_word(c_base, n, w),
    ensures
        forall|k: int| 0 <= k < decode_digit_seq(c_base, n, w).len() ==>
            1 <= #[trigger] decode_digit_seq(c_base, n, w)[k] <= 2 * n,
    decreases w.len()
{
    lemma_decode_digit_seq_len(c_base, n, w);
    if w.len() == 0 {
    } else {
        let ds = decode_digit_seq(c_base, n, w);
        let rest = decode_digit_seq(c_base, n, w.drop_last());
        assert(ds == seq![letter_digit(c_base, n, w.last())] + rest);
        // w.last() is in the c-block (last index of the c-alphabet word).
        assert(in_c_block(c_base, n, w.last())) by {
            assert(w.last() == w[w.len() - 1]);
        }
        lemma_alphabet_letter_section(c_base, n, w.last());   // 1 ≤ letter_digit(w.last()) ≤ 2n
        // w.drop_last() inherits c_alphabet_word.
        assert(c_alphabet_word(c_base, n, w.drop_last())) by {
            assert forall|k: int| 0 <= k < w.drop_last().len() implies
                in_c_block(c_base, n, #[trigger] w.drop_last()[k]) by {
                assert(w.drop_last()[k] == w[k]);
            }
        }
        lemma_decode_digit_seq_bound(c_base, n, w.drop_last());
        lemma_decode_digit_seq_len(c_base, n, w.drop_last());
        // assemble: digit 0 is letter_digit(w.last()); digits 1.. are rest's (in range by IH).
        assert forall|k: int| 0 <= k < ds.len() implies 1 <= #[trigger] ds[k] <= 2 * n by {
            if k == 0 {
                assert(ds[0] == letter_digit(c_base, n, w.last()));
            } else {
                assert(ds[k] == rest[k - 1]);
            }
        }
    }
}

/// **`relnum` as a `dpack` digit block (the emitter's spec target).** `relnum(e,mm,m,a,b)` equals
/// `dpack(decode_digit_seq(cb, 2, ρ(fam_relator(a,b))), m)` — the base-`m` number the R-relnum-gen
/// emitter must lay on the tape (and R-cmp must match against the parked `α`). Direct specialization of
/// [`lemma_decode_word_is_dpack`] at `relnum`'s definition (`n = 2`, `c_base = cb_of(mm)`,
/// `w = ρ(fam_relator(a,b))`).
pub proof fn lemma_relnum_is_dpack(e: CEER, mm: ModMachine, m: nat, a: nat, b: nat)
    ensures
        relnum(e, mm, m, a, b)
            == dpack(decode_digit_seq(cb_of(mm), 2, rho(e, mm, m, fam_relator(a, b))), m),
{
    lemma_decode_word_is_dpack(cb_of(mm), 2, m, rho(e, mm, m, fam_relator(a, b)));
    // relnum == decode_word(cb, 2, m, ρ(fam_relator(a,b))) by definition.
}

} // verus!
