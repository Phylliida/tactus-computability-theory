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
use verus_group_theory::word::{Word, empty_word};
use verus_group_theory::symbol::Symbol;
use verus_group_theory::machine_group::{symbol_power, word_power};
use verus_group_theory::word_numbering_decode::{decode_word, letter_digit, in_c_block,
    c_alphabet_word, lemma_alphabet_letter_section};
use crate::tm_two_counter::{repunit_m, lemma_repunit_step};
use verus_group_theory::machine_group::ModMachine;
use crate::ceer::CEER;
use crate::gap2_relnum::{relnum, fam_relator};
use crate::ceer_relator_match::{cb_of, rho};
use crate::tm_dstring::{dpack, pow_nat, lemma_dpack_push, lemma_dpack_empty, lemma_pow_nat_unfold};

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

/// **`decode_word` over concatenation (Horner split).** `decode_word(w1 + w2)` places `w1`'s digits
/// above `w2`'s: `decode_word(w1+w2) == decode_word(w1)·m^{|w2|} + decode_word(w2)`. The tool for
/// breaking `fam_relator = u_a · u_b⁻¹` (and each `u_j` into its eight pieces) for the explicit
/// digit-pattern characterization. Induction on `w2` (peeling its last symbol = the whole word's last).
pub proof fn lemma_decode_word_concat(c_base: nat, n: nat, m: nat, w1: Word, w2: Word)
    ensures
        decode_word(c_base, n, m, w1 + w2)
            == decode_word(c_base, n, m, w1) * pow_nat(m, w2.len()) + decode_word(c_base, n, m, w2),
    decreases w2.len()
{
    if w2.len() == 0 {
        assert(w1 + w2 =~= w1);
        assert(pow_nat(m, 0) == 1);
        // decode_word(w2) == 0; decode_word(w1)·1 + 0 == decode_word(w1).
    } else {
        let pre2 = w2.drop_last();
        let last2 = w2.last();
        assert((w1 + w2).drop_last() =~= w1 + pre2);
        assert((w1 + w2).last() == last2);
        lemma_decode_word_concat(c_base, n, m, w1, pre2);   // IH
        let aa = decode_word(c_base, n, m, w1);
        let pp = pow_nat(m, (w2.len() - 1) as nat);
        let rr = decode_word(c_base, n, m, pre2);
        let ll = letter_digit(c_base, n, last2);
        assert(pre2.len() == w2.len() - 1);
        lemma_pow_nat_unfold(m, w2.len());                  // pow_nat(m,k) == m·pow_nat(m,k-1)
        assert(pow_nat(m, w2.len()) == pp * m) by(nonlinear_arith)
            requires pow_nat(m, w2.len()) == m * pp;
        // decode_word(w1+w2) == (aa·pp + rr)·m + ll == aa·(pp·m) + (rr·m + ll).
        assert(decode_word(c_base, n, m, w1 + w2) == (aa * pp + rr) * m + ll);
        assert((aa * pp + rr) * m + ll == aa * (pp * m) + (rr * m + ll)) by(nonlinear_arith);
        assert(decode_word(c_base, n, m, w2) == rr * m + ll);
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

/// **`decode_word` of a `symbol_power` block.** A run of `k` copies of a single symbol `s` contributes
/// `letter_digit(c,n,s) · repunit_m(k, m)` to the word-number (its digit appears at every place value
/// `1, m, …, m^{k-1}`). The closed form for the `a⁻ⁱ = symbol_power(Inv(0),i)` and `aⁱ =
/// symbol_power(Gen(0),i)` blocks of the collapse relator `u_j`. Direct induction on `k` via
/// `decode_word`'s last-symbol recurrence (`symbol_power(s,k).drop_last() = symbol_power(s,k-1)`,
/// `.last() = s`) and the low-end repunit recurrence `repunit_m(k) = m·repunit_m(k-1) + 1`.
pub proof fn lemma_decode_word_symbol_power(c_base: nat, n: nat, m: nat, s: Symbol, k: nat)
    ensures
        decode_word(c_base, n, m, symbol_power(s, k)) == letter_digit(c_base, n, s) * repunit_m(k, m),
    decreases k,
{
    if k == 0 {
        assert(symbol_power(s, 0) =~= Seq::<Symbol>::empty());
        assert(repunit_m(0, m) == 0);
        assert(letter_digit(c_base, n, s) * 0 == 0) by(nonlinear_arith);
    } else {
        // symbol_power(s,k) = symbol_power(s,k-1) ++ [s].
        assert(symbol_power(s, k).last() == s);
        assert(symbol_power(s, k).drop_last() =~= symbol_power(s, (k - 1) as nat));
        lemma_decode_word_symbol_power(c_base, n, m, s, (k - 1) as nat);   // IH
        let d = letter_digit(c_base, n, s);
        // decode_word(k) == decode_word(k-1)·m + d == (d·repunit(k-1))·m + d == d·(m·repunit(k-1)+1).
        assert(decode_word(c_base, n, m, symbol_power(s, k))
            == decode_word(c_base, n, m, symbol_power(s, (k - 1) as nat)) * m + d);
        assert((d * repunit_m((k - 1) as nat, m)) * m + d == d * (m * repunit_m((k - 1) as nat, m) + 1))
            by(nonlinear_arith);
        assert(repunit_m(k, m) == m * repunit_m((k - 1) as nat, m) + 1);
    }
}

/// **`word_power` append (snoc) form.** `word_power(w, k) =~= word_power(w, k-1) + w` for `k ≥ 1` — the
/// low (last) copy peels off the right. The defining recurrence peels the FRONT copy
/// (`word_power(w,k) = w + word_power(w,k-1)`); this commuted form is what lets
/// [`lemma_decode_word_word_power`]'s induction land on `decode_word`'s last-symbol-is-lowest-digit fold
/// and the existing low-end `repunit_m` recurrence. Induction on `k` via concatenation associativity.
pub proof fn lemma_word_power_snoc(w: Word, k: nat)
    requires
        k >= 1,
    ensures
        word_power(w, k) =~= word_power(w, (k - 1) as nat) + w,
    decreases k,
{
    if k == 1 {
        assert(word_power(w, 1) == w + word_power(w, 0));
        assert(word_power(w, 0) =~= empty_word());
        assert(word_power(w, 1) =~= w);
        assert(word_power(w, 0) + w =~= w);
    } else {
        let k1 = (k - 1) as nat;
        lemma_word_power_snoc(w, k1);   // word_power(w,k1) == word_power(w,k1-1) + w
        assert(word_power(w, k) == w + word_power(w, k1));
        // w + word_power(w,k1) == w + (word_power(w,k1-1) + w) == (w + word_power(w,k1-1)) + w
        assert(w + word_power(w, k1) =~= w + (word_power(w, (k1 - 1) as nat) + w));
        assert(w + (word_power(w, (k1 - 1) as nat) + w)
            =~= (w + word_power(w, (k1 - 1) as nat)) + w);
        assert(w + word_power(w, (k1 - 1) as nat) == word_power(w, k1));
        assert(word_power(w, k) =~= word_power(w, k1) + w);
    }
}

/// **`decode_word` of a `word_power` block (the geometric closed form).** A run of `k` copies of a word
/// `w` has word-number `decode_word(w) · repunit_m(k, m^{|w|})` — `w`'s digit block repeats at place
/// values `1, m^{|w|}, m^{2|w|}, …`. The closed form for the `(t a⁻¹ t⁻¹)ⁱ = word_power(binv_sub,i)`
/// (digits `(234)ⁱ`) and `(t a t⁻¹)ⁱ = word_power(b_sub,i)` (digits `(214)ⁱ`) blocks of the collapse
/// relator `u_j`, and the value invariant the R-relnum-gen emitter's inner loop maintains. Induction on
/// `k` peeling the LOW copy ([`lemma_word_power_snoc`] + [`lemma_decode_word_concat`]) onto the existing
/// low-end `repunit_m` recurrence (`repunit_m(k,P) = P·repunit_m(k-1,P) + 1`, here `P = m^{|w|}`).
pub proof fn lemma_decode_word_word_power(c_base: nat, n: nat, m: nat, w: Word, k: nat)
    ensures
        decode_word(c_base, n, m, word_power(w, k))
            == decode_word(c_base, n, m, w) * repunit_m(k, pow_nat(m, w.len())),
    decreases k,
{
    let bigp = pow_nat(m, w.len());
    let d = decode_word(c_base, n, m, w);
    if k == 0 {
        assert(word_power(w, 0) =~= empty_word());
        assert(decode_word(c_base, n, m, word_power(w, 0)) == 0) by {
            assert(empty_word().len() == 0);
        }
        assert(repunit_m(0, bigp) == 0);
        assert(d * 0 == 0) by(nonlinear_arith);
    } else {
        let k1 = (k - 1) as nat;
        lemma_word_power_snoc(w, k);                          // word_power(w,k) == word_power(w,k1) + w
        assert(word_power(w, k) == word_power(w, k1) + w);
        lemma_decode_word_concat(c_base, n, m, word_power(w, k1), w);
        // decode_word(word_power(w,k1)+w) == decode_word(word_power(w,k1))·pow_nat(m,|w|) + d
        lemma_decode_word_word_power(c_base, n, m, w, k1);   // IH: decode_word(wp(k1)) == d·repunit_m(k1,bigp)
        assert((k1 + 1) as nat == k);
        lemma_repunit_step(k1, bigp);                        // repunit_m(k,bigp) == bigp·repunit_m(k1,bigp)+1
        assert(repunit_m(k, bigp) == bigp * repunit_m(k1, bigp) + 1);
        assert(decode_word(c_base, n, m, word_power(w, k)) == (d * repunit_m(k1, bigp)) * bigp + d);
        assert((d * repunit_m(k1, bigp)) * bigp + d == d * (bigp * repunit_m(k1, bigp) + 1))
            by(nonlinear_arith);
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
