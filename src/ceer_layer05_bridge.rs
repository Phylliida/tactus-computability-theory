//! Layer 0.5 wiring — step (ii): the NATIVE bridge connecting the CEER group's own word problem
//! (`ceer_group_equiv`) to the group-theory direct-limit presentation (`equiv_in_c0_limit`).
//!
//! `ceer_layer05.rs` instantiated `decls_fam` and consumed the abstract Miller iff over the
//! group-theory `Word`/presentation alphabet. This module proves that that presentation-side
//! triviality is *the same* as the CEER group's native derivation triviality, by translating
//! `ceer_group.rs`'s derivation system (`CeerGroupStep`) into `presentation.rs`'s (`DerivationStep`)
//! at a large enough finite slice level `M`. The two systems are step-for-step parallel
//! (`apply_step`'s relator insertion is PLAIN insertion, matching `apply_ceer_step` exactly), so the
//! translation is mechanical — the only bookkeeping is choosing `M` past every generator index and
//! stage used in the (finite) derivation, and matching a declared relator to its slice index.
//!
//! This file builds bottom-up. PART 1 here: the translation `ceer_to_word` commutes with the Seq
//! operations the derivation systems use (len/index/concat/subrange) and with symbol inversion.

use vstd::prelude::*;
use crate::ceer::*;
use crate::ceer_group::*;
use crate::ceer_layer05::*;
use verus_group_theory::symbol::*;
use verus_group_theory::word::*;
use verus_group_theory::presentation::{Presentation, DerivationStep, get_relator, apply_step,
    derivation_produces, Derivation, derivation_valid, equiv_in_presentation};
use verus_group_theory::reduction::has_cancellation_at;
use verus_group_theory::cohen_layer05_probe::c0_slice;
use verus_group_theory::cohen_layer05::equiv_in_c0_limit;

verus! {

/// The finite C₀ slice at level `big_m` for the CEER family — exactly what
/// `equiv_in_c0_limit(ceer_decls_fam(e), …)` quantifies over.
pub open spec fn c0_slice_of(e: CEER, big_m: nat) -> Presentation {
    c0_slice(big_m, ceer_decls_fam_at(e, big_m))
}

// ===========================================================================
// PART 1. The translation `ceer_to_word` commutes with Seq ops + inversion.
// ===========================================================================

/// `ceer_to_word` preserves length.
pub proof fn lemma_ceer_to_word_len(w: CeerWord)
    ensures
        ceer_to_word(w).len() == w.len(),
{
}

/// `ceer_to_word` acts pointwise.
pub proof fn lemma_ceer_to_word_index(w: CeerWord, i: int)
    requires
        0 <= i < w.len(),
    ensures
        ceer_to_word(w)[i] == ceer_sym_to_sym(w[i]),
{
}

/// Translation commutes with concatenation.
pub proof fn lemma_ceer_to_word_concat(a: CeerWord, b: CeerWord)
    ensures
        ceer_to_word(a + b) =~= ceer_to_word(a) + ceer_to_word(b),
{
    assert(ceer_to_word(a + b).len() == (ceer_to_word(a) + ceer_to_word(b)).len());
    assert forall|i: int| 0 <= i < ceer_to_word(a + b).len() implies
        ceer_to_word(a + b)[i] == (ceer_to_word(a) + ceer_to_word(b))[i] by {
        if i < a.len() {
            assert((a + b)[i] == a[i]);
        } else {
            assert((a + b)[i] == b[i - a.len()]);
        }
    }
}

/// Translation commutes with subrange.
pub proof fn lemma_ceer_to_word_subrange(w: CeerWord, i: int, j: int)
    requires
        0 <= i <= j <= w.len(),
    ensures
        ceer_to_word(w.subrange(i, j)) =~= ceer_to_word(w).subrange(i, j),
{
    assert(ceer_to_word(w.subrange(i, j)).len() == ceer_to_word(w).subrange(i, j).len());
    assert forall|k: int| 0 <= k < (j - i) implies
        ceer_to_word(w.subrange(i, j))[k] == ceer_to_word(w).subrange(i, j)[k] by {
        assert(w.subrange(i, j)[k] == w[i + k]);
    }
}

/// Translation commutes with symbol inversion.
pub proof fn lemma_ceer_sym_inverse(s: CeerSymbol)
    ensures
        ceer_sym_to_sym(inverse_ceer_symbol(s)) == inverse_symbol(ceer_sym_to_sym(s)),
{
}

/// `ceer_sym_to_sym` is injective.
pub proof fn lemma_ceer_sym_injective(s1: CeerSymbol, s2: CeerSymbol)
    requires
        ceer_sym_to_sym(s1) == ceer_sym_to_sym(s2),
    ensures
        s1 == s2,
{
}

/// The two inverse-pair notions agree under translation.
pub proof fn lemma_is_inverse_pair_translate(s1: CeerSymbol, s2: CeerSymbol)
    ensures
        is_inverse_pair(ceer_sym_to_sym(s1), ceer_sym_to_sym(s2)) == is_ceer_inverse_pair(s1, s2),
{
    lemma_ceer_sym_inverse(s1);
    // is_inverse_pair(t(s1), t(s2)) = (t(s2) == inverse_symbol(t(s1))) = (t(s2) == t(inverse_ceer(s1)))
    // <=> s2 == inverse_ceer(s1)  [injectivity]  <=> is_ceer_inverse_pair(s1, s2).
    if is_ceer_inverse_pair(s1, s2) {
        assert(s2 == inverse_ceer_symbol(s1));
    }
    if ceer_sym_to_sym(s2) == inverse_symbol(ceer_sym_to_sym(s1)) {
        assert(ceer_sym_to_sym(s2) == ceer_sym_to_sym(inverse_ceer_symbol(s1)));
        lemma_ceer_sym_injective(s2, inverse_ceer_symbol(s1));
    }
}

// ===========================================================================
// PART 2. Translating a CeerGroupStep to a DerivationStep, and matching a declared
//         relator to its slice index.
// ===========================================================================

/// The generator index carried by a CEER symbol.
pub open spec fn ceer_sym_idx(s: CeerSymbol) -> nat {
    match s {
        CeerSymbol::Gen { index } => index,
        CeerSymbol::Inv { index } => index,
    }
}

/// Translation preserves the generator index.
pub proof fn lemma_ceer_sym_idx(s: CeerSymbol)
    ensures
        generator_index(ceer_sym_to_sym(s)) == ceer_sym_idx(s),
{
}

/// At stage `stage`, is the declared pair stored in swapped order `(b, a)` (so the slice relator
/// `[Gen(b),Inv(a)]` must be inverted to recover the inserted `[Gen(a),Inv(b)]`)?
pub open spec fn declared_swapped(e: CEER, stage: nat, a: nat, b: nat) -> bool {
    declared_pair(e, stage) == Some((b, a))
}

/// Translate a CEER derivation step to a presentation derivation step at slice level `big_m`.
pub open spec fn translate_step(e: CEER, step: CeerGroupStep, big_m: nat) -> DerivationStep {
    match step {
        CeerGroupStep::FreeReduce { position } =>
            DerivationStep::FreeReduce { position: position as int },
        CeerGroupStep::FreeExpand { position, sym } =>
            DerivationStep::FreeExpand { position: position as int, symbol: ceer_sym_to_sym(sym) },
        CeerGroupStep::RelatorInsert { position, a, b, stage } =>
            DerivationStep::RelatorInsert {
                position: position as int,
                relator_index: stage,
                inverted: declared_swapped(e, stage, a, b),
            },
        CeerGroupStep::RelatorDelete { position, a, b, stage } =>
            DerivationStep::RelatorDelete {
                position: position as int,
                relator_index: stage,
                inverted: declared_swapped(e, stage, a, b),
            },
    }
}

/// The translated CEER relator is the explicit 2-symbol word `[Gen(a), Inv(b)]`.
pub proof fn lemma_ceer_relator_translate(a: nat, b: nat)
    ensures
        ceer_to_word(ceer_relator(a, b)) =~= seq![Symbol::Gen(a), Symbol::Inv(b)],
{
    let r = ceer_relator(a, b);
    assert(r.len() == 2);
    assert(r[0] == CeerSymbol::Gen { index: a });
    assert(r[1] == CeerSymbol::Inv { index: b });
    let w = ceer_to_word(r);
    assert(w.len() == 2);
    assert(w[0] == Symbol::Gen(a));
    assert(w[1] == Symbol::Inv(b));
}

/// `inverse_word` of a 2-symbol word reverses and inverts.
pub proof fn lemma_inverse_word_two(s0: Symbol, s1: Symbol)
    ensures
        inverse_word(seq![s0, s1]) =~= seq![inverse_symbol(s1), inverse_symbol(s0)],
{
    let w = seq![s0, s1];
    assert(w.len() == 2);
    assert(w.first() == s0);
    assert(w.drop_first() =~= seq![s1]);
    let w1 = seq![s1];
    assert(w1.len() == 1);
    assert(w1.first() == s1);
    assert(w1.drop_first() =~= Seq::<Symbol>::empty());
    // inverse_word(w1) = inverse_word(empty) + [inverse_symbol(s1)] = [inverse_symbol(s1)]
    assert(inverse_word(w1.drop_first()) =~= empty_word());
    assert(inverse_word(w1) =~= seq![inverse_symbol(s1)]);
    // inverse_word(w) = inverse_word(w1) + [inverse_symbol(s0)]
    assert(inverse_word(w) =~= seq![inverse_symbol(s1)] + seq![inverse_symbol(s0)]);
}

/// **The relator-match lemma.** At a slice level `big_m` past the stage and pair, the slice's
/// relator at index `stage`, possibly inverted per `declared_swapped`, is exactly the translated
/// inserted relator `ceer_to_word([Gen(a),Inv(b)])`.
pub proof fn lemma_slice_relator_match(e: CEER, stage: nat, a: nat, b: nat, big_m: nat)
    requires
        stage < big_m,
        a < big_m,
        b < big_m,
        stage_declares(e, stage, a, b),
    ensures
        get_relator(c0_slice_of(e, big_m), stage, declared_swapped(e, stage, a, b))
            =~= ceer_to_word(ceer_relator(a, b)),
{
    // declared_pair(e,stage) = Some((p0,p1)) with {p0,p1} = {a,b}, both < big_m.
    let p = declared_pair(e, stage).unwrap();
    assert(declared_pair(e, stage) is Some);
    let p0 = p.0;
    let p1 = p.1;
    assert((p0 == a && p1 == b) || (p0 == b && p1 == a));
    // slice.relators[stage] = ceer_relator_at(e, stage, big_m) = ceer_to_word(ceer_relator(p0,p1)).
    assert(c0_slice_of(e, big_m).relators[stage as int] == ceer_relator_at(e, stage, big_m));
    assert(p0 < big_m && p1 < big_m);
    assert(ceer_relator_at(e, stage, big_m) == ceer_to_word(ceer_relator(p0, p1)));
    lemma_ceer_relator_translate(p0, p1);
    lemma_ceer_relator_translate(a, b);
    if declared_swapped(e, stage, a, b) {
        // declared_pair = Some((b,a)): slice relator = [Gen(b),Inv(a)]; invert -> [Gen(a),Inv(b)].
        assert(p0 == b && p1 == a);
        lemma_inverse_word_two(Symbol::Gen(b), Symbol::Inv(a));
    } else {
        // not swapped: declared_pair = Some((a,b)); slice relator = [Gen(a),Inv(b)] directly.
        assert(p0 == a && p1 == b);
    }
}

// ===========================================================================
// PART 3. Per-step apply correspondence.
// ===========================================================================

/// `step` only mentions generator indices / stages below `big_m` (so its translation lands in the
/// level-`big_m` slice).
pub open spec fn step_fits(e: CEER, step: CeerGroupStep, big_m: nat) -> bool {
    match step {
        CeerGroupStep::FreeReduce { .. } => true,
        CeerGroupStep::FreeExpand { position, sym } => ceer_sym_idx(sym) < big_m,
        CeerGroupStep::RelatorInsert { position, a, b, stage } =>
            a < big_m && b < big_m && stage < big_m,
        CeerGroupStep::RelatorDelete { position, a, b, stage } =>
            a < big_m && b < big_m && stage < big_m,
    }
}

/// `ceer_to_word(w)` is valid over `big_m` iff every CEER symbol index is below `big_m`.
pub open spec fn ceer_word_fits(w: CeerWord, big_m: nat) -> bool {
    forall|i: int| 0 <= i < w.len() ==> ceer_sym_idx(#[trigger] w[i]) < big_m
}

/// `ceer_word_fits` is exactly `word_valid` of the translation.
pub proof fn lemma_ceer_word_fits_iff(w: CeerWord, big_m: nat)
    ensures
        ceer_word_fits(w, big_m) == word_valid(ceer_to_word(w), big_m),
{
    let ww = ceer_to_word(w);
    if ceer_word_fits(w, big_m) {
        assert forall|i: int| 0 <= i < ww.len() implies symbol_valid(#[trigger] ww[i], big_m) by {
            lemma_ceer_to_word_index(w, i);
            lemma_ceer_sym_idx(w[i]);
        }
    }
    if word_valid(ww, big_m) {
        assert forall|i: int| 0 <= i < w.len() implies ceer_sym_idx(#[trigger] w[i]) < big_m by {
            lemma_ceer_to_word_index(w, i);
            lemma_ceer_sym_idx(w[i]);
        }
    }
}

/// **The per-step correspondence.** Translating a valid, in-range CEER step and applying it in the
/// slice yields the translation of the CEER step's result.
pub proof fn lemma_translate_step_correct(e: CEER, big_m: nat, cw: CeerWord, step: CeerGroupStep)
    requires
        ceer_step_valid(e, cw, step),
        ceer_word_fits(cw, big_m),
        step_fits(e, step, big_m),
    ensures
        apply_step(c0_slice_of(e, big_m), ceer_to_word(cw), translate_step(e, step, big_m))
            == Some(ceer_to_word(apply_ceer_step(cw, step))),
{
    let slice = c0_slice_of(e, big_m);
    let w = ceer_to_word(cw);
    lemma_ceer_word_fits_iff(cw, big_m);
    assert(slice.num_generators == big_m);
    assert(slice.relators.len() == big_m);
    match step {
        CeerGroupStep::FreeReduce { position } => {
            // validity: is_ceer_inverse_pair(cw[pos], cw[pos+1]); pos+1 < cw.len().
            lemma_is_inverse_pair_translate(cw[position as int], cw[(position + 1) as int]);
            lemma_ceer_to_word_index(cw, position as int);
            lemma_ceer_to_word_index(cw, (position + 1) as int);
            assert(has_cancellation_at(w, position as int));
            lemma_ceer_to_word_subrange(cw, 0, position as int);
            lemma_ceer_to_word_subrange(cw, (position + 2) as int, cw.len() as int);
            lemma_ceer_to_word_concat(cw.subrange(0, position as int),
                cw.subrange((position + 2) as int, cw.len() as int));
            assert(apply_step(slice, w, translate_step(e, step, big_m))
                =~~= Some(ceer_to_word(apply_ceer_step(cw, step))));
        },
        CeerGroupStep::FreeExpand { position, sym } => {
            lemma_ceer_sym_idx(sym);
            assert(symbol_valid(ceer_sym_to_sym(sym), big_m));
            let pair_c = seq![sym, inverse_ceer_symbol(sym)];
            lemma_ceer_sym_inverse(sym);
            // crate inserts Seq::new(1,|_|s) + Seq::new(1,|_|inverse_symbol(s)).
            lemma_ceer_to_word_subrange(cw, 0, position as int);
            lemma_ceer_to_word_subrange(cw, position as int, cw.len() as int);
            lemma_ceer_to_word_concat(cw.subrange(0, position as int), pair_c);
            lemma_ceer_to_word_concat(cw.subrange(0, position as int) + pair_c,
                cw.subrange(position as int, cw.len() as int));
            assert(ceer_to_word(pair_c) =~= seq![ceer_sym_to_sym(sym), inverse_symbol(ceer_sym_to_sym(sym))]);
            assert(apply_step(slice, w, translate_step(e, step, big_m))
                =~~= Some(ceer_to_word(apply_ceer_step(cw, step))));
        },
        CeerGroupStep::RelatorInsert { position, a, b, stage } => {
            lemma_slice_relator_match(e, stage, a, b, big_m);
            lemma_ceer_to_word_subrange(cw, 0, position as int);
            lemma_ceer_to_word_subrange(cw, position as int, cw.len() as int);
            lemma_ceer_to_word_concat(cw.subrange(0, position as int), ceer_relator(a, b));
            lemma_ceer_to_word_concat(cw.subrange(0, position as int) + ceer_relator(a, b),
                cw.subrange(position as int, cw.len() as int));
            assert(apply_step(slice, w, translate_step(e, step, big_m))
                =~~= Some(ceer_to_word(apply_ceer_step(cw, step))));
        },
        CeerGroupStep::RelatorDelete { position, a, b, stage } => {
            lemma_slice_relator_match(e, stage, a, b, big_m);
            lemma_ceer_relator_translate(a, b);
            let r = get_relator(slice, stage, declared_swapped(e, stage, a, b));
            // r = [Gen(a), Inv(b)], rlen = 2; W[pos..pos+2] == r.
            lemma_ceer_to_word_index(cw, position as int);
            lemma_ceer_to_word_index(cw, (position + 1) as int);
            assert(w.subrange(position as int, position as int + 2) =~= r);
            lemma_ceer_to_word_subrange(cw, 0, position as int);
            lemma_ceer_to_word_subrange(cw, (position + 2) as int, cw.len() as int);
            lemma_ceer_to_word_concat(cw.subrange(0, position as int),
                cw.subrange((position + 2) as int, cw.len() as int));
            assert(apply_step(slice, w, translate_step(e, step, big_m))
                =~~= Some(ceer_to_word(apply_ceer_step(cw, step))));
        },
    }
}

// ===========================================================================
// PART 4. Derivation induction + the level bound + the forward bridge.
// ===========================================================================

/// Inversion preserves the CEER symbol index.
pub proof fn lemma_ceer_sym_idx_inverse(s: CeerSymbol)
    ensures
        ceer_sym_idx(inverse_ceer_symbol(s)) == ceer_sym_idx(s),
{
}

/// `ceer_word_fits` splits over concatenation.
pub proof fn lemma_ceer_word_fits_concat(a: CeerWord, b: CeerWord, big_m: nat)
    requires
        ceer_word_fits(a, big_m),
        ceer_word_fits(b, big_m),
    ensures
        ceer_word_fits(a + b, big_m),
{
    assert forall|i: int| 0 <= i < (a + b).len() implies ceer_sym_idx(#[trigger] (a + b)[i]) < big_m by {
        if i < a.len() {
            assert((a + b)[i] == a[i]);
        } else {
            assert((a + b)[i] == b[i - a.len()]);
        }
    }
}

/// `ceer_word_fits` is inherited by subranges.
pub proof fn lemma_ceer_word_fits_subrange(w: CeerWord, i: int, j: int, big_m: nat)
    requires
        ceer_word_fits(w, big_m),
        0 <= i <= j <= w.len(),
    ensures
        ceer_word_fits(w.subrange(i, j), big_m),
{
    assert forall|k: int| 0 <= k < (j - i) implies ceer_sym_idx(#[trigger] w.subrange(i, j)[k]) < big_m by {
        assert(w.subrange(i, j)[k] == w[i + k]);
    }
}

/// `apply_ceer_step` keeps the result within level `big_m`.
pub proof fn lemma_apply_ceer_step_fits(e: CEER, cw: CeerWord, step: CeerGroupStep, big_m: nat)
    requires
        ceer_step_valid(e, cw, step),
        ceer_word_fits(cw, big_m),
        step_fits(e, step, big_m),
    ensures
        ceer_word_fits(apply_ceer_step(cw, step), big_m),
{
    match step {
        CeerGroupStep::FreeReduce { position } => {
            lemma_ceer_word_fits_subrange(cw, 0, position as int, big_m);
            lemma_ceer_word_fits_subrange(cw, (position + 2) as int, cw.len() as int, big_m);
            lemma_ceer_word_fits_concat(cw.subrange(0, position as int),
                cw.subrange((position + 2) as int, cw.len() as int), big_m);
        },
        CeerGroupStep::FreeExpand { position, sym } => {
            lemma_ceer_sym_idx_inverse(sym);
            let pair_c = seq![sym, inverse_ceer_symbol(sym)];
            assert(ceer_word_fits(pair_c, big_m)) by {
                assert(pair_c[0] == sym);
                assert(pair_c[1] == inverse_ceer_symbol(sym));
            }
            lemma_ceer_word_fits_subrange(cw, 0, position as int, big_m);
            lemma_ceer_word_fits_subrange(cw, position as int, cw.len() as int, big_m);
            lemma_ceer_word_fits_concat(cw.subrange(0, position as int), pair_c, big_m);
            lemma_ceer_word_fits_concat(cw.subrange(0, position as int) + pair_c,
                cw.subrange(position as int, cw.len() as int), big_m);
        },
        CeerGroupStep::RelatorInsert { position, a, b, stage } => {
            let rel = ceer_relator(a, b);
            assert(ceer_word_fits(rel, big_m)) by {
                assert(rel[0] == CeerSymbol::Gen { index: a });
                assert(rel[1] == CeerSymbol::Inv { index: b });
            }
            lemma_ceer_word_fits_subrange(cw, 0, position as int, big_m);
            lemma_ceer_word_fits_subrange(cw, position as int, cw.len() as int, big_m);
            lemma_ceer_word_fits_concat(cw.subrange(0, position as int), rel, big_m);
            lemma_ceer_word_fits_concat(cw.subrange(0, position as int) + rel,
                cw.subrange(position as int, cw.len() as int), big_m);
        },
        CeerGroupStep::RelatorDelete { position, a, b, stage } => {
            lemma_ceer_word_fits_subrange(cw, 0, position as int, big_m);
            lemma_ceer_word_fits_subrange(cw, (position + 2) as int, cw.len() as int, big_m);
            lemma_ceer_word_fits_concat(cw.subrange(0, position as int),
                cw.subrange((position + 2) as int, cw.len() as int), big_m);
        },
    }
}

/// Map the step translation over a derivation.
pub open spec fn translate_steps(e: CEER, steps: Seq<CeerGroupStep>, big_m: nat) -> Seq<DerivationStep>
    decreases steps.len(),
{
    if steps.len() == 0 {
        Seq::empty()
    } else {
        seq![translate_step(e, steps.first(), big_m)] + translate_steps(e, steps.drop_first(), big_m)
    }
}

/// Every step in the derivation fits below level `big_m`.
pub open spec fn steps_fit(e: CEER, steps: Seq<CeerGroupStep>, big_m: nat) -> bool
    decreases steps.len(),
{
    if steps.len() == 0 {
        true
    } else {
        step_fits(e, steps.first(), big_m) && steps_fit(e, steps.drop_first(), big_m)
    }
}

/// **The derivation induction.** A valid CEER derivation, translated step-by-step, is a valid
/// presentation derivation in the level-`big_m` slice producing the translated endpoint.
pub proof fn lemma_translate_derivation(e: CEER, big_m: nat, cw: CeerWord, end: CeerWord,
    steps: Seq<CeerGroupStep>)
    requires
        ceer_derivation_valid(e, cw, end, steps),
        ceer_word_fits(cw, big_m),
        steps_fit(e, steps, big_m),
    ensures
        derivation_produces(c0_slice_of(e, big_m), translate_steps(e, steps, big_m), ceer_to_word(cw))
            == Some(ceer_to_word(end)),
    decreases steps.len(),
{
    let slice = c0_slice_of(e, big_m);
    if steps.len() == 0 {
        assert(cw =~= end);
        assert(ceer_to_word(cw) =~= ceer_to_word(end));
    } else {
        let first = steps.first();
        let rest = steps.drop_first();
        let cw2 = apply_ceer_step(cw, first);
        // step 1 lands on ceer_to_word(cw2)
        lemma_translate_step_correct(e, big_m, cw, first);
        lemma_apply_ceer_step_fits(e, cw, first, big_m);
        // the translated step list's head/tail
        let tsteps = translate_steps(e, steps, big_m);
        assert(tsteps.first() == translate_step(e, first, big_m));
        assert(tsteps.drop_first() =~= translate_steps(e, rest, big_m));
        assert(apply_step(slice, ceer_to_word(cw), tsteps.first()) == Some(ceer_to_word(cw2)));
        // recurse on the tail
        lemma_translate_derivation(e, big_m, cw2, end, rest);
    }
}

/// max of two nats.
pub open spec fn max_nat(a: nat, b: nat) -> nat { if a >= b { a } else { b } }

/// The smallest level that contains a single step's indices.
pub open spec fn step_level(step: CeerGroupStep) -> nat {
    match step {
        CeerGroupStep::FreeReduce { .. } => 0,
        CeerGroupStep::FreeExpand { position, sym } => ceer_sym_idx(sym) + 1,
        CeerGroupStep::RelatorInsert { position, a, b, stage } => max_nat(max_nat(a, b), stage) + 1,
        CeerGroupStep::RelatorDelete { position, a, b, stage } => max_nat(max_nat(a, b), stage) + 1,
    }
}

/// The smallest level that contains every step in a derivation.
pub open spec fn steps_level(steps: Seq<CeerGroupStep>) -> nat
    decreases steps.len(),
{
    if steps.len() == 0 {
        0
    } else {
        max_nat(step_level(steps.first()), steps_level(steps.drop_first()))
    }
}

/// At any level `>= steps_level`, every step fits.
pub proof fn lemma_steps_fit_at_level(e: CEER, steps: Seq<CeerGroupStep>, big_m: nat)
    requires
        steps_level(steps) <= big_m,
    ensures
        steps_fit(e, steps, big_m),
    decreases steps.len(),
{
    if steps.len() != 0 {
        let first = steps.first();
        assert(step_level(first) <= big_m);
        assert(steps_level(steps.drop_first()) <= big_m);
        lemma_steps_fit_at_level(e, steps.drop_first(), big_m);
    }
}

/// `ceer_word_fits` is monotone in the level.
pub proof fn lemma_ceer_word_fits_mono(w: CeerWord, n: nat, big_m: nat)
    requires
        ceer_word_fits(w, n),
        n <= big_m,
    ensures
        ceer_word_fits(w, big_m),
{
}

/// **THE FORWARD BRIDGE.** If a CEER word `w` (with generators below `n`) is trivial in the CEER
/// group, then its translation is trivial in the direct-limit C₀ over the concrete CEER family.
/// (Soundness of the embedding: CEER triviality ⟹ presentation-limit triviality.)
pub proof fn lemma_ceer_group_equiv_implies_c0_limit(e: CEER, n: nat, w: CeerWord)
    requires
        word_valid(ceer_to_word(w), n),
        ceer_group_equiv(e, w, Seq::<CeerSymbol>::empty()),
    ensures
        equiv_in_c0_limit(ceer_decls_fam(e), n, ceer_to_word(w), empty_word()),
{
    let eps = Seq::<CeerSymbol>::empty();
    let steps = choose|steps: Seq<CeerGroupStep>| ceer_derivation_valid(e, w, eps, steps);
    let big_m = max_nat(n, steps_level(steps));
    // bounds
    lemma_ceer_word_fits_iff(w, n);
    lemma_ceer_word_fits_mono(w, n, big_m);
    lemma_steps_fit_at_level(e, steps, big_m);
    // the translated derivation produces ε's translation = empty_word()
    lemma_translate_derivation(e, big_m, w, eps, steps);
    assert(ceer_to_word(eps) =~= empty_word());
    // package as a presentation derivation in the slice
    let slice = c0_slice_of(e, big_m);
    let d = Derivation { steps: translate_steps(e, steps, big_m) };
    assert(derivation_valid(slice, d, ceer_to_word(w), empty_word()));
    assert(equiv_in_presentation(slice, ceer_to_word(w), empty_word()));
    // slice == c0_slice(big_m, ceer_decls_fam(e)(big_m)); witness M = big_m >= n.
    assert(ceer_decls_fam(e)(big_m) == ceer_decls_fam_at(e, big_m));
    assert(slice == c0_slice(big_m, ceer_decls_fam(e)(big_m)));
    assert(equiv_in_c0_limit(ceer_decls_fam(e), n, ceer_to_word(w), empty_word()));
}

} // verus!
