//! # GAP-2 R-relnum-gen — the explicit `decode_digit_seq(fam_relator)` pattern (the emitter's target).
//!
//! The culmination of plan §5 step 1. Combining the `fam_relator` decomposition
//! ([`crate::gap2_fam_split`]) with the digit-seq structural laws ([`crate::gap2_relnum_dds`]), this
//! module characterizes `decode_digit_seq(0, 2, fam_relator(a,b))` — the low-first base-`m` digit block of
//! `relnum(a,b)` (capstone [`crate::gap2_relnum_digits::lemma_relnum_is_decode_digit_seq`]) — as an
//! **explicit concatenation of `seq_pow` blocks and singleton digits** ([`fam_digits`]). This is the
//! sequence the R-relnum-gen two-counter emitter must lay on the tape, one loop iteration per `seq_pow`
//! block; the digit-by-digit compare (R-cmp) matches it against the parked `α`.
//!
//! All digits are concrete (`{a→1, t→2, a⁻¹→3, t⁻¹→4}` = `letter_digit(0,2,·)`), and the order is the
//! REVERSED (low-first) one — `decode_digit_seq` peels the last symbol as the lowest digit, so the
//! emitter emits high-symbol-last.
//!
//! `docs/gap2-input-loader-plan.md` §5 (R-relnum-gen). Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::word::{Word, inverse_word, concat};
use verus_group_theory::symbol::Symbol;
use verus_group_theory::machine_group::{word_power, symbol_power};
use verus_group_theory::miller_collapse::{miller_collapse_word, b_sub, binv_sub};
use verus_group_theory::word_numbering_decode::letter_digit;
use crate::gap2_relnum_digits::decode_digit_seq;
use crate::gap2_relnum_dds::{seq_pow, lemma_dds_concat, lemma_dds_singleton, lemma_dds_word_power,
    lemma_dds_symbol_power};
use crate::gap2_relnum::{fam_relator, relnum};
use crate::gap2_rho_unshift::lemma_relnum_is_decode_digit_seq;
use crate::gap2_fam_split::{lemma_fam_relator_split, lemma_inverse_collapse_word};
use crate::tm_dstring::dpack;
use crate::ceer::CEER;
use verus_group_theory::machine_group::ModMachine;

verus! {

// ============================================================================
// 3-letter dds helpers (concrete digit values)
// ============================================================================

/// `dds([s0,s1,s2]) == [ld(s2), ld(s1), ld(s0)]` — the digit-seq reversal at length 3. Mirror of the
/// inverse-triple helper, via [`lemma_dds_concat`] + [`lemma_dds_singleton`].
pub proof fn lemma_dds_triple(s0: Symbol, s1: Symbol, s2: Symbol)
    ensures
        decode_digit_seq(0, 2, seq![s0, s1, s2])
            =~= seq![letter_digit(0, 2, s2), letter_digit(0, 2, s1), letter_digit(0, 2, s0)],
{
    assert(seq![s0, s1, s2] =~= concat(concat(seq![s0], seq![s1]), seq![s2]));
    lemma_dds_concat(0, 2, concat(seq![s0], seq![s1]), seq![s2]);
    lemma_dds_concat(0, 2, seq![s0], seq![s1]);
    lemma_dds_singleton(0, 2, s0);
    lemma_dds_singleton(0, 2, s1);
    lemma_dds_singleton(0, 2, s2);
}

/// `dds(binv_sub(0,1)) == [4,3,2]` — the `b⁻¹ = t a⁻¹ t⁻¹` block reversed (`[2,3,4]` low-first → `[4,3,2]`).
pub proof fn lemma_dds_binv_sub()
    ensures
        decode_digit_seq(0, 2, binv_sub(0, 1)) =~= seq![4nat, 3nat, 2nat],
{
    assert(binv_sub(0, 1) =~= seq![Symbol::Gen(1nat), Symbol::Inv(0nat), Symbol::Inv(1nat)]);
    lemma_dds_triple(Symbol::Gen(1nat), Symbol::Inv(0nat), Symbol::Inv(1nat));
    // ld(Inv1)=4, ld(Inv0)=3, ld(Gen1)=2
}

/// `dds(b_sub(0,1)) == [4,1,2]` — the `b = t a t⁻¹` block reversed (`[2,1,4]` low-first → `[4,1,2]`).
pub proof fn lemma_dds_b_sub()
    ensures
        decode_digit_seq(0, 2, b_sub(0, 1)) =~= seq![4nat, 1nat, 2nat],
{
    assert(b_sub(0, 1) =~= seq![Symbol::Gen(1nat), Symbol::Gen(0nat), Symbol::Inv(1nat)]);
    lemma_dds_triple(Symbol::Gen(1nat), Symbol::Gen(0nat), Symbol::Inv(1nat));
    // ld(Inv1)=4, ld(Gen0)=1, ld(Gen1)=2
}

// ============================================================================
// The explicit digit blocks of u_j and inverse_word(u_b)
// ============================================================================

/// The explicit low-first digit block of `u_j = miller_collapse_word(j,0,1)` (i = j+1). The reversed
/// concatenation of the 8 piece digit-blocks (`decode_digit_seq` peels last-symbol-first):
/// `(1)ⁱ·[4,3,2]·(3)ⁱ·[4]·(4,1,2)ⁱ·[1]·(4,3,2)ⁱ·[2]`.
pub open spec fn u_digits(j: nat) -> Seq<nat> {
    let i = (j + 1) as nat;
    seq_pow(seq![1nat], i)
        + seq![4nat, 3nat, 2nat]
        + seq_pow(seq![3nat], i)
        + seq![4nat]
        + seq_pow(seq![4nat, 1nat, 2nat], i)
        + seq![1nat]
        + seq_pow(seq![4nat, 3nat, 2nat], i)
        + seq![2nat]
}

/// The explicit low-first digit block of `inverse_word(u_b)` (i = b+1). The reversed concatenation of the
/// 8 inverse-piece digit-blocks: `[4]·(4,1,2)ⁱ·[3]·(4,3,2)ⁱ·[2]·(1)ⁱ·[4,1,2]·(3)ⁱ`.
pub open spec fn uinv_digits(b: nat) -> Seq<nat> {
    let i = (b + 1) as nat;
    seq![4nat]
        + seq_pow(seq![4nat, 1nat, 2nat], i)
        + seq![3nat]
        + seq_pow(seq![4nat, 3nat, 2nat], i)
        + seq![2nat]
        + seq_pow(seq![1nat], i)
        + seq![4nat, 1nat, 2nat]
        + seq_pow(seq![3nat], i)
}

/// **`relnum`'s digit block (the emitter's target).** `decode_digit_seq(0,2, fam_relator(a,b)) ==
/// uinv_digits(b) ++ u_digits(a)` — the low digits from `inverse_word(u_b)`, the high digits from `u_a`
/// (`decode_digit_seq` reverses the `u_a ++ inverse_word(u_b)` order).
pub open spec fn fam_digits(a: nat, b: nat) -> Seq<nat> {
    uinv_digits(b) + u_digits(a)
}

// ============================================================================
// u_j and inverse_word(u_b) digit expansions
// ============================================================================

/// **`dds(u_j) == u_digits(j)`.** The 8-fold reversed `dds_concat` peel of `miller_collapse_word(j,0,1)`
/// + per-piece digit evaluations (singletons, `dds_symbol_power`, `dds_word_power`, the 3-letter dds).
pub proof fn lemma_dds_collapse_word(j: nat)
    ensures
        decode_digit_seq(0, 2, miller_collapse_word(j, 0, 1)) =~= u_digits(j),
{
    let i = (j + 1) as nat;
    let p1 = seq![Symbol::Gen(1nat)];
    let p2 = word_power(binv_sub(0, 1), i);
    let p3 = seq![Symbol::Gen(0nat)];
    let p4 = word_power(b_sub(0, 1), i);
    let p5 = seq![Symbol::Inv(1nat)];
    let p6 = symbol_power(Symbol::Inv(0nat), i);
    let p7 = binv_sub(0, 1);
    let p8 = symbol_power(Symbol::Gen(0nat), i);
    let x1 = p1;
    let x2 = x1 + p2;
    let x3 = x2 + p3;
    let x4 = x3 + p4;
    let x5 = x4 + p5;
    let x6 = x5 + p6;
    let x7 = x6 + p7;
    let x8 = x7 + p8;
    assert(miller_collapse_word(j, 0, 1) == x8);
    // 7-fold reversed dds_concat peel.
    lemma_dds_concat(0, 2, x7, p8);   // dds(x8) =~= dds(p8) + dds(x7)
    lemma_dds_concat(0, 2, x6, p7);
    lemma_dds_concat(0, 2, x5, p6);
    lemma_dds_concat(0, 2, x4, p5);
    lemma_dds_concat(0, 2, x3, p4);
    lemma_dds_concat(0, 2, x2, p3);
    lemma_dds_concat(0, 2, x1, p2);
    // per-piece digit blocks.
    lemma_dds_symbol_power(0, 2, Symbol::Gen(0nat), i);   // dds(p8) =~= seq_pow([1],i)
    lemma_dds_binv_sub();                                 // dds(p7) =~= [4,3,2]
    lemma_dds_symbol_power(0, 2, Symbol::Inv(0nat), i);   // dds(p6) =~= seq_pow([3],i)
    lemma_dds_singleton(0, 2, Symbol::Inv(1nat));         // dds(p5) =~= [4]
    lemma_dds_word_power(0, 2, b_sub(0, 1), i);           // dds(p4) =~= seq_pow(dds(b_sub),i)
    lemma_dds_b_sub();                                    // dds(b_sub) =~= [4,1,2]
    lemma_dds_singleton(0, 2, Symbol::Gen(0nat));         // dds(p3) =~= [1]
    lemma_dds_word_power(0, 2, binv_sub(0, 1), i);        // dds(p2) =~= seq_pow(dds(binv_sub),i)
    // (dds(binv_sub) =~= [4,3,2] from lemma_dds_binv_sub above)
    lemma_dds_singleton(0, 2, Symbol::Gen(1nat));         // dds(p1) =~= [2]
}

/// **`dds(inverse_word(u_b)) == uinv_digits(b)`.** Rewrite `inverse_word(u_b)` into its explicit 8
/// primitive pieces ([`lemma_inverse_collapse_word`]) then the 8-fold reversed `dds_concat` peel + the
/// per-piece digit evaluations.
pub proof fn lemma_dds_inverse_collapse_word(b: nat)
    ensures
        decode_digit_seq(0, 2, inverse_word(miller_collapse_word(b, 0, 1))) =~= uinv_digits(b),
{
    let i = (b + 1) as nat;
    // the explicit inverse pieces (gap2_fam_split):
    //   inverse_word(u_b) = a⁻ⁱ · b · aⁱ · t · binv^i · a⁻¹ · b^i · t⁻¹
    let q1 = symbol_power(Symbol::Inv(0nat), i);
    let q2 = b_sub(0, 1);
    let q3 = symbol_power(Symbol::Gen(0nat), i);
    let q4 = seq![Symbol::Gen(1nat)];
    let q5 = word_power(binv_sub(0, 1), i);
    let q6 = seq![Symbol::Inv(0nat)];
    let q7 = word_power(b_sub(0, 1), i);
    let q8 = seq![Symbol::Inv(1nat)];
    let y1 = q1;
    let y2 = y1 + q2;
    let y3 = y2 + q3;
    let y4 = y3 + q4;
    let y5 = y4 + q5;
    let y6 = y5 + q6;
    let y7 = y6 + q7;
    let y8 = y7 + q8;
    lemma_inverse_collapse_word(b);   // inverse_word(u_b) =~= y8
    assert(inverse_word(miller_collapse_word(b, 0, 1)) =~= y8);
    // 7-fold reversed dds_concat peel.
    lemma_dds_concat(0, 2, y7, q8);   // dds(y8) =~= dds(q8) + dds(y7)
    lemma_dds_concat(0, 2, y6, q7);
    lemma_dds_concat(0, 2, y5, q6);
    lemma_dds_concat(0, 2, y4, q5);
    lemma_dds_concat(0, 2, y3, q4);
    lemma_dds_concat(0, 2, y2, q3);
    lemma_dds_concat(0, 2, y1, q2);
    // per-piece digit blocks.
    lemma_dds_singleton(0, 2, Symbol::Inv(1nat));         // dds(q8) =~= [4]
    lemma_dds_word_power(0, 2, b_sub(0, 1), i);           // dds(q7) =~= seq_pow(dds(b_sub),i)
    lemma_dds_b_sub();                                    // dds(b_sub) =~= [4,1,2]
    lemma_dds_singleton(0, 2, Symbol::Inv(0nat));         // dds(q6) =~= [3]
    lemma_dds_word_power(0, 2, binv_sub(0, 1), i);        // dds(q5) =~= seq_pow(dds(binv_sub),i)
    lemma_dds_binv_sub();                                 // dds(binv_sub) =~= [4,3,2]
    lemma_dds_singleton(0, 2, Symbol::Gen(1nat));         // dds(q4) =~= [2]
    lemma_dds_symbol_power(0, 2, Symbol::Gen(0nat), i);   // dds(q3) =~= seq_pow([1],i)
    lemma_dds_symbol_power(0, 2, Symbol::Inv(0nat), i);   // dds(q1) =~= seq_pow([3],i)
    // dds(q2) = dds(b_sub) =~= [4,1,2] from lemma_dds_b_sub above.
}

// ============================================================================
// The headline: dds(fam_relator) == fam_digits
// ============================================================================

/// **The explicit `relnum` digit pattern.** `decode_digit_seq(0,2, fam_relator(a,b)) == fam_digits(a,b)`
/// = `uinv_digits(b) ++ u_digits(a)`. Composes [`lemma_fam_relator_split`] (`fam_relator = u_a ++
/// inverse_word(u_b)`) + [`lemma_dds_concat`] (reversal) + the two block expansions. The single fact the
/// R-relnum-gen two-counter emitter and the R-cmp compare are proved against.
pub proof fn lemma_dds_fam_relator(a: nat, b: nat)
    ensures
        decode_digit_seq(0, 2, fam_relator(a, b)) =~= fam_digits(a, b),
{
    let ua = miller_collapse_word(a, 0, 1);
    let ub = miller_collapse_word(b, 0, 1);
    lemma_fam_relator_split(a, b);                 // fam_relator =~= ua + inverse_word(ub)
    assert(fam_relator(a, b) =~= ua + inverse_word(ub));
    lemma_dds_concat(0, 2, ua, inverse_word(ub));  // dds(ua + inv(ub)) =~= dds(inv(ub)) + dds(ua)
    lemma_dds_collapse_word(a);                    // dds(ua) =~= u_digits(a)
    lemma_dds_inverse_collapse_word(b);            // dds(inv(ub)) =~= uinv_digits(b)
}

/// **The Evaluation-side spec target (`relnum` as the `fam_digits` block value).** `relnum(e,mm,m,a,b) ==
/// dpack(fam_digits(a,b), m)` — composes the capstone [`lemma_relnum_is_decode_digit_seq`]
/// (`relnum == dpack(decode_digit_seq(0,2,fam_relator),m)`) with the headline [`lemma_dds_fam_relator`].
/// This is the single fact the R-relnum-gen emitter's Evaluation proof closes against: once the emitter is
/// shown to produce the digit block `fam_digits(a,b)` on tape, its `dpack` value is exactly `relnum`.
pub proof fn lemma_relnum_is_fam_digits(e: CEER, mm: ModMachine, m: nat, a: nat, b: nat)
    ensures
        relnum(e, mm, m, a, b) == dpack(fam_digits(a, b), m),
{
    lemma_relnum_is_decode_digit_seq(e, mm, m, a, b);   // relnum == dpack(dds(0,2,fam_relator), m)
    lemma_dds_fam_relator(a, b);                        // dds(0,2,fam_relator) == fam_digits
}

} // verus!
