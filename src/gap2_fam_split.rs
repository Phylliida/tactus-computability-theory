//! # GAP-2 R-relnum-gen — the `fam_relator` decomposition (apply_embedding bridge + inverse_word(u_b)).
//!
//! Assembles the explicit shape of `fam_relator(a,b)` for the digit-pattern characterization:
//!
//!   1. [`lemma_fam_relator_split`]: `fam_relator(a,b) == u_a ++ inverse_word(u_b)` where
//!      `u_j = miller_collapse_word(j,0,1)` — peeling `apply_embedding` over the 2-symbol relator word
//!      `[Gen(a), Inv(b)]` (via [`lemma_apply_embedding_concat`] + singleton unfolds).
//!   2. [`lemma_inverse_b_sub`]/[`lemma_inverse_binv_sub`]: the 3-letter `b`/`b⁻¹` word inverses
//!      (`(t a t⁻¹)⁻¹ = t a⁻¹ t⁻¹` and vice versa).
//!   3. [`lemma_inverse_collapse_word`]: `inverse_word(u_b)` rewritten into its explicit 8 primitive
//!      pieces (the same shapes as `u_a`), via [`crate::gap2_inverse`] + the 3-letter inverses.
//!
//! `docs/gap2-input-loader-plan.md` §5 (R-relnum-gen). Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::word::{Word, empty_word, inverse_word, concat, lemma_inverse_concat,
    lemma_inverse_singleton};
use verus_group_theory::symbol::{Symbol, inverse_symbol};
use verus_group_theory::machine_group::{word_power, symbol_power};
use verus_group_theory::miller_collapse::{miller_collapse_word, miller_collapse_emb, b_sub, binv_sub};
use verus_group_theory::benign::{apply_embedding, apply_embedding_symbol, lemma_apply_embedding_concat};
use crate::ceer_group::ceer_relator;
use crate::ceer_layer05::ceer_to_word;
use crate::gap2_relnum::{fam_relator, rel_slice, lemma_ceer_relator_word_valid};
use crate::gap2_inverse::{lemma_inverse_symbol_power, lemma_inverse_word_power};

verus! {

/// `Seq::new(1, |_| s)` — the singleton spelling [`lemma_inverse_singleton`] uses.
pub open spec fn sing(s: Symbol) -> Word {
    Seq::new(1, |_i: int| s)
}

/// `inverse_word([s]) == [s⁻¹]` (the `seq!` spelling, bridging [`lemma_inverse_singleton`]).
pub proof fn lemma_inverse_sing(s: Symbol)
    ensures
        inverse_word(seq![s]) =~= seq![inverse_symbol(s)],
{
    assert(seq![s] =~= sing(s));
    lemma_inverse_singleton(s);
    assert(seq![inverse_symbol(s)] =~= sing(inverse_symbol(s)));
}

/// **Inverse of a 3-letter word `[s0,s1,s2]` = `[s2⁻¹, s1⁻¹, s0⁻¹]`.** Robust three-singleton
/// composition via [`lemma_inverse_concat`] + [`lemma_inverse_singleton`] (no fuel-dependent unfolding).
pub proof fn lemma_inverse_triple(s0: Symbol, s1: Symbol, s2: Symbol)
    ensures
        inverse_word(seq![s0, s1, s2])
            =~= seq![inverse_symbol(s2), inverse_symbol(s1), inverse_symbol(s0)],
{
    // [s0,s1,s2] == (sing(s0) + sing(s1)) + sing(s2)
    assert(seq![s0, s1, s2] =~= concat(concat(sing(s0), sing(s1)), sing(s2)));
    lemma_inverse_concat(concat(sing(s0), sing(s1)), sing(s2));
    // inverse(((s0)(s1))(s2)) =~= inverse(s2) + inverse((s0)(s1))
    lemma_inverse_concat(sing(s0), sing(s1));
    // inverse((s0)(s1)) =~= inverse(s1) + inverse(s0)
    lemma_inverse_singleton(s0);   // inverse(sing(s0)) =~= sing(inverse_symbol(s0))
    lemma_inverse_singleton(s1);
    lemma_inverse_singleton(s2);
    assert(inverse_word(seq![s0, s1, s2])
        =~= sing(inverse_symbol(s2)) + (sing(inverse_symbol(s1)) + sing(inverse_symbol(s0))));
}

// ============================================================================
// Stage 1 — the 3-letter b / b⁻¹ word inverses
// ============================================================================

/// `inverse_word(b_sub(0,1)) == binv_sub(0,1)`: `(t a t⁻¹)⁻¹ = t a⁻¹ t⁻¹`.
pub proof fn lemma_inverse_b_sub()
    ensures
        inverse_word(b_sub(0, 1)) =~= binv_sub(0, 1),
{
    assert(b_sub(0, 1) =~= seq![Symbol::Gen(1nat), Symbol::Gen(0nat), Symbol::Inv(1nat)]);
    lemma_inverse_triple(Symbol::Gen(1nat), Symbol::Gen(0nat), Symbol::Inv(1nat));
    assert(binv_sub(0, 1) =~= seq![Symbol::Gen(1nat), Symbol::Inv(0nat), Symbol::Inv(1nat)]);
}

/// `inverse_word(binv_sub(0,1)) == b_sub(0,1)`: `(t a⁻¹ t⁻¹)⁻¹ = t a t⁻¹`. Mirror of
/// [`lemma_inverse_b_sub`].
pub proof fn lemma_inverse_binv_sub()
    ensures
        inverse_word(binv_sub(0, 1)) =~= b_sub(0, 1),
{
    assert(binv_sub(0, 1) =~= seq![Symbol::Gen(1nat), Symbol::Inv(0nat), Symbol::Inv(1nat)]);
    lemma_inverse_triple(Symbol::Gen(1nat), Symbol::Inv(0nat), Symbol::Inv(1nat));
    assert(b_sub(0, 1) =~= seq![Symbol::Gen(1nat), Symbol::Gen(0nat), Symbol::Inv(1nat)]);
}

// ============================================================================
// Stage 2 — fam_relator(a,b) = u_a ++ inverse_word(u_b)
// ============================================================================

/// **The `fam_relator` split.** `fam_relator(a,b) == miller_collapse_word(a,0,1) ++
/// inverse_word(miller_collapse_word(b,0,1))` — `apply_embedding` over the 2-symbol relator word
/// `[Gen(a), Inv(b)]` maps `Gen(a) ↦ u_a` and `Inv(b) ↦ inverse_word(u_b)`. Via
/// [`lemma_apply_embedding_concat`] (split the word) + singleton unfolds + the `images[j] = u_j` index
/// (`a,b < rel_slice(a,b)`, so the indices land in the `miller_collapse_word` prefix of the embedding).
pub proof fn lemma_fam_relator_split(a: nat, b: nat)
    ensures
        fam_relator(a, b)
            =~= miller_collapse_word(a, 0, 1) + inverse_word(miller_collapse_word(b, 0, 1)),
{
    let big = rel_slice(a, b);
    let images = miller_collapse_emb(big, 0, 1);
    let w = ceer_to_word(ceer_relator(a, b));
    // w = [Gen(a), Inv(b)]  (ceer_to_word of the 2-symbol ceer relator).
    assert(w.len() == 2);
    assert(w[0] == Symbol::Gen(a));
    assert(w[1] == Symbol::Inv(b));
    let wga = seq![Symbol::Gen(a)];
    let wib = seq![Symbol::Inv(b)];
    assert(w =~= concat(wga, wib));
    // apply_embedding(images, w) =~= apply_embedding(images, wga) + apply_embedding(images, wib)
    lemma_apply_embedding_concat(images, wga, wib);
    // singleton applies: apply_embedding(images, [s]) =~= apply_embedding_symbol(images, s).
    assert(wga.first() == Symbol::Gen(a));
    assert(wga.drop_first() =~= empty_word());
    assert(apply_embedding(images, empty_word()) =~= empty_word());
    assert(apply_embedding(images, wga) =~= apply_embedding_symbol(images, Symbol::Gen(a)));
    assert(wib.first() == Symbol::Inv(b));
    assert(wib.drop_first() =~= empty_word());
    assert(apply_embedding(images, wib) =~= apply_embedding_symbol(images, Symbol::Inv(b)));
    // apply_embedding_symbol: Gen(a) ↦ images[a], Inv(b) ↦ inverse_word(images[b]).
    assert(apply_embedding_symbol(images, Symbol::Gen(a)) == images[a as int]);
    assert(apply_embedding_symbol(images, Symbol::Inv(b)) == inverse_word(images[b as int]));
    // images[j] = miller_collapse_word(j,0,1) for j < big (the embedding's mcw prefix).
    assert(a < big && b < big);
    let pref = Seq::new(big, |j: int| miller_collapse_word(j as nat, 0, 1));
    assert(images[a as int] == miller_collapse_word(a, 0, 1)) by {
        assert(images[a as int] == pref[a as int]);
    }
    assert(images[b as int] == miller_collapse_word(b, 0, 1)) by {
        assert(images[b as int] == pref[b as int]);
    }
    // fam_relator = apply_embedding(images, w) =~= images[a] + inverse_word(images[b]).
    assert(fam_relator(a, b) == apply_embedding(images, w));
}

// ============================================================================
// Stage 3 — inverse_word(u_b) as 8 explicit primitive pieces
// ============================================================================

/// **The explicit `inverse_word(u_b)` rewrite.** `u_b = miller_collapse_word(b,0,1) =
/// t·binv^i·a·b^i·t⁻¹·a⁻ⁱ·binv·aⁱ` (i = b+1) inverts (reverse + invert each factor) to the same 8
/// primitive shapes as `u_a`:
/// ```text
///   inverse_word(u_b) = aⁱ·binv ... no: = a⁻ⁱ · b · aⁱ · t · binv^i · a⁻¹ · b^i · t⁻¹
/// ```
/// i.e. `symbol_power(Inv0,i)·b_sub·symbol_power(Gen0,i)·[Gen1]·word_power(binv_sub,i)·[Inv0]·
/// word_power(b_sub,i)·[Inv1]`. The 7-fold [`lemma_inverse_concat`] peel + the per-piece inverses
/// ([`lemma_inverse_symbol_power`], [`lemma_inverse_word_power`], the 3-letter/singleton inverses).
pub proof fn lemma_inverse_collapse_word(b: nat)
    ensures
        inverse_word(miller_collapse_word(b, 0, 1))
            =~= symbol_power(Symbol::Inv(0nat), (b + 1) as nat)
              + b_sub(0, 1)
              + symbol_power(Symbol::Gen(0nat), (b + 1) as nat)
              + seq![Symbol::Gen(1nat)]
              + word_power(binv_sub(0, 1), (b + 1) as nat)
              + seq![Symbol::Inv(0nat)]
              + word_power(b_sub(0, 1), (b + 1) as nat)
              + seq![Symbol::Inv(1nat)],
{
    let i = (b + 1) as nat;
    let p1 = seq![Symbol::Gen(1nat)];
    let p2 = word_power(binv_sub(0, 1), i);
    let p3 = seq![Symbol::Gen(0nat)];
    let p4 = word_power(b_sub(0, 1), i);
    let p5 = seq![Symbol::Inv(1nat)];
    let p6 = symbol_power(Symbol::Inv(0nat), i);
    let p7 = binv_sub(0, 1);
    let p8 = symbol_power(Symbol::Gen(0nat), i);
    // u_b is the left-associated 8-fold concatenation of the pieces.
    let x1 = p1;
    let x2 = x1 + p2;
    let x3 = x2 + p3;
    let x4 = x3 + p4;
    let x5 = x4 + p5;
    let x6 = x5 + p6;
    let x7 = x6 + p7;
    let x8 = x7 + p8;
    assert(miller_collapse_word(b, 0, 1) == x8);
    // 7-fold inverse_concat peel (reverse the factor order).
    lemma_inverse_concat(x7, p8);   // inverse(x8) =~= inverse(p8) + inverse(x7)
    lemma_inverse_concat(x6, p7);
    lemma_inverse_concat(x5, p6);
    lemma_inverse_concat(x4, p5);
    lemma_inverse_concat(x3, p4);
    lemma_inverse_concat(x2, p3);
    lemma_inverse_concat(x1, p2);   // inverse(x2) =~= inverse(p2) + inverse(x1)
    // per-piece inverses.
    lemma_inverse_symbol_power(Symbol::Gen(0nat), i);   // inverse(p8) =~= sp(Inv0,i)
    lemma_inverse_binv_sub();                           // inverse(p7) =~= b_sub(0,1)
    lemma_inverse_symbol_power(Symbol::Inv(0nat), i);   // inverse(p6) =~= sp(Gen0,i)
    lemma_inverse_sing(Symbol::Inv(1nat));              // inverse(p5) =~= [Gen1]
    lemma_inverse_word_power(b_sub(0, 1), i);           // inverse(p4) =~= wp(inverse(b_sub),i)
    lemma_inverse_b_sub();                              // inverse(b_sub) =~= binv_sub → inverse(p4) =~= wp(binv_sub,i)
    lemma_inverse_sing(Symbol::Gen(0nat));              // inverse(p3) =~= [Inv0]
    lemma_inverse_word_power(binv_sub(0, 1), i);        // inverse(p2) =~= wp(inverse(binv_sub),i)
    lemma_inverse_binv_sub();                           // inverse(binv_sub) =~= b_sub → inverse(p2) =~= wp(b_sub,i)
    lemma_inverse_sing(Symbol::Gen(1nat));              // inverse(p1) =~= [Inv1]
}

} // verus!
