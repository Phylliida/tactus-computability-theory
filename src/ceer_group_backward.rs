use vstd::prelude::*;
use crate::ceer::*;
use crate::ceer_group::*;

verus! {

//  ============================================================
//  Phase 1: Specs — word count invariant
//  ============================================================

///  Contribution of a single symbol to the count for CEER class [target].
///  Gen(i) with i ~ target contributes +1, Inv(i) with i ~ target contributes -1, else 0.
pub open spec fn symbol_contributes(e: CEER, sym: CeerSymbol, target: nat) -> int {
    match sym {
        CeerSymbol::Gen { index } => if ceer_equiv(e, index, target) { 1int } else { 0int },
        CeerSymbol::Inv { index } => if ceer_equiv(e, index, target) { -1int } else { 0int },
    }
}

///  Net count of symbols in w contributing to CEER class [target].
pub open spec fn word_count(e: CEER, w: CeerWord, target: nat) -> int
    decreases w.len(),
{
    if w.len() == 0 {
        0int
    } else {
        symbol_contributes(e, w.first(), target) + word_count(e, w.drop_first(), target)
    }
}

//  ============================================================
//  Phase 2: Additivity
//  ============================================================

///  word_count(w1 ++ w2) == word_count(w1) + word_count(w2).
pub proof fn lemma_word_count_additive(e: CEER, w1: CeerWord, w2: CeerWord, target: nat)
    ensures
        word_count(e, w1 + w2, target) == word_count(e, w1, target) + word_count(e, w2, target),
    decreases w1.len(),
{
    if w1.len() == 0 {
        assert((w1 + w2) =~= w2);
    } else {
        assert((w1 + w2).first() == w1.first());
        assert((w1 + w2).drop_first() =~= w1.drop_first() + w2);
        lemma_word_count_additive(e, w1.drop_first(), w2, target);
    }
}

//  ============================================================
//  Phase 3: Cancellation lemmas
//  ============================================================

///  declared_equiv implies ceer_equiv (via 2-element chain [a, b]).
proof fn lemma_declared_to_ceer_equiv(e: CEER, a: nat, b: nat)
    requires
        declared_equiv(e, a, b),
    ensures
        ceer_equiv(e, a, b),
{
    let chain = seq![a, b];
    assert(chain.drop_first() =~= seq![b]);
    assert(ceer_equiv_chain(e, b, b, chain.drop_first()));
    assert(ceer_equiv_chain(e, a, b, chain));
}

///  Equivalence class transfer: a ~ b implies (a ~ t ↔ b ~ t).
proof fn lemma_ceer_equiv_class_transfer(e: CEER, a: nat, b: nat, t: nat)
    requires
        ceer_equiv(e, a, b),
    ensures
        ceer_equiv(e, a, t) <==> ceer_equiv(e, b, t),
{
    if ceer_equiv(e, a, t) {
        lemma_ceer_equiv_symmetric(e, a, b);
        lemma_ceer_equiv_transitive(e, b, a, t);
    }
    if ceer_equiv(e, b, t) {
        lemma_ceer_equiv_transitive(e, a, b, t);
    }
}

///  A symbol and its formal inverse cancel: sc(s) + sc(inv(s)) == 0.
proof fn lemma_inverse_symbol_cancels(e: CEER, sym: CeerSymbol, target: nat)
    ensures
        symbol_contributes(e, sym, target)
            + symbol_contributes(e, inverse_ceer_symbol(sym), target) == 0,
{
}

///  An inverse pair (from is_ceer_inverse_pair) cancels: sc(s1) + sc(s2) == 0.
proof fn lemma_inverse_pair_cancels(e: CEER, s1: CeerSymbol, s2: CeerSymbol, target: nat)
    requires
        is_ceer_inverse_pair(s1, s2),
    ensures
        symbol_contributes(e, s1, target) + symbol_contributes(e, s2, target) == 0,
{
}

///  word_count of a singleton word equals symbol_contributes.
proof fn lemma_singleton_word_count(e: CEER, sym: CeerSymbol, target: nat)
    ensures
        word_count(e, seq![sym], target) == symbol_contributes(e, sym, target),
{
    reveal_with_fuel(word_count, 2);
    assert(seq![sym].drop_first() =~= Seq::<CeerSymbol>::empty());
}

///  The CEER relator [Gen(a), Inv(b)] has word_count 0 when a ~ b.
proof fn lemma_relator_cancels(e: CEER, a: nat, b: nat, stage: nat, target: nat)
    requires
        stage_declares(e, stage, a, b),
    ensures
        word_count(e, ceer_relator(a, b), target) == 0,
{
    let ga = CeerSymbol::Gen { index: a };
    let ib = CeerSymbol::Inv { index: b };
    assert(ceer_relator(a, b) =~= seq![ga] + seq![ib]);
    lemma_word_count_additive(e, seq![ga], seq![ib], target);
    lemma_singleton_word_count(e, ga, target);
    lemma_singleton_word_count(e, ib, target);

    //  stage_declares → declared_equiv → ceer_equiv → class transfer
    assert(declared_equiv(e, a, b));
    lemma_declared_to_ceer_equiv(e, a, b);
    lemma_ceer_equiv_class_transfer(e, a, b, target);
}

//  ============================================================
//  Phase 4: Step preservation
//  ============================================================

///  FreeReduce at position p preserves word_count.
proof fn lemma_free_reduce_preserves(e: CEER, w: CeerWord, position: nat, target: nat)
    requires
        position + 1 < w.len(),
        is_ceer_inverse_pair(w[position as int], w[(position + 1) as int]),
    ensures
        word_count(e, w, target) == word_count(e,
            w.subrange(0, position as int)
                + w.subrange((position + 2) as int, w.len() as int),
            target),
{
    reveal_with_fuel(word_count, 3);
    let prefix = w.subrange(0, position as int);
    let rest = w.subrange(position as int, w.len() as int);
    let suffix = w.subrange((position + 2) as int, w.len() as int);

    assert(w =~= prefix + rest);
    lemma_word_count_additive(e, prefix, rest, target);

    //  Unfold rest twice: sc(w[p]) + sc(w[p+1]) + word_count(suffix)
    assert(rest.first() == w[position as int]);
    let rest_tail = rest.drop_first();
    assert(rest_tail.first() == w[(position + 1) as int]);
    assert(rest_tail.drop_first() =~= suffix);

    lemma_inverse_pair_cancels(e, w[position as int], w[(position + 1) as int], target);
    lemma_word_count_additive(e, prefix, suffix, target);
}

///  FreeExpand preserves word_count.
proof fn lemma_free_expand_preserves(
    e: CEER, w: CeerWord, position: nat, sym: CeerSymbol, target: nat,
)
    requires
        position <= w.len(),
    ensures
        word_count(e, w, target) == word_count(e,
            (w.subrange(0, position as int) + seq![sym, inverse_ceer_symbol(sym)])
                + w.subrange(position as int, w.len() as int),
            target),
{
    let prefix = w.subrange(0, position as int);
    let suffix = w.subrange(position as int, w.len() as int);
    let pair = seq![sym, inverse_ceer_symbol(sym)];

    assert(w =~= prefix + suffix);
    lemma_word_count_additive(e, prefix, suffix, target);

    //  new_w = (prefix + pair) + suffix
    lemma_word_count_additive(e, prefix + pair, suffix, target);
    lemma_word_count_additive(e, prefix, pair, target);

    //  pair has count 0
    assert(pair =~= seq![sym] + seq![inverse_ceer_symbol(sym)]);
    lemma_word_count_additive(e, seq![sym], seq![inverse_ceer_symbol(sym)], target);
    lemma_singleton_word_count(e, sym, target);
    lemma_singleton_word_count(e, inverse_ceer_symbol(sym), target);
    lemma_inverse_symbol_cancels(e, sym, target);
}

///  RelatorInsert preserves word_count.
proof fn lemma_relator_insert_preserves(
    e: CEER, w: CeerWord, position: nat, a: nat, b: nat, stage: nat, target: nat,
)
    requires
        position <= w.len(),
        stage_declares(e, stage, a, b),
    ensures
        word_count(e, w, target) == word_count(e,
            (w.subrange(0, position as int) + ceer_relator(a, b))
                + w.subrange(position as int, w.len() as int),
            target),
{
    let prefix = w.subrange(0, position as int);
    let suffix = w.subrange(position as int, w.len() as int);
    let rel = ceer_relator(a, b);

    assert(w =~= prefix + suffix);
    lemma_word_count_additive(e, prefix, suffix, target);

    //  new_w = (prefix + rel) + suffix
    lemma_word_count_additive(e, prefix + rel, suffix, target);
    lemma_word_count_additive(e, prefix, rel, target);

    lemma_relator_cancels(e, a, b, stage, target);
}

///  RelatorDelete preserves word_count.
proof fn lemma_relator_delete_preserves(
    e: CEER, w: CeerWord, position: nat, a: nat, b: nat, stage: nat, target: nat,
)
    requires
        stage_declares(e, stage, a, b),
        position + 2 <= w.len(),
        w[position as int] == (CeerSymbol::Gen { index: a }),
        w[(position + 1) as int] == (CeerSymbol::Inv { index: b }),
    ensures
        word_count(e, w, target) == word_count(e,
            w.subrange(0, position as int)
                + w.subrange((position + 2) as int, w.len() as int),
            target),
{
    reveal_with_fuel(word_count, 3);
    let prefix = w.subrange(0, position as int);
    let rest = w.subrange(position as int, w.len() as int);
    let suffix = w.subrange((position + 2) as int, w.len() as int);

    assert(w =~= prefix + rest);
    lemma_word_count_additive(e, prefix, rest, target);

    //  Unfold rest: [Gen(a), Inv(b)] ++ suffix
    assert(rest.first() == (CeerSymbol::Gen { index: a }));
    let rest_tail = rest.drop_first();
    assert(rest_tail.first() == (CeerSymbol::Inv { index: b }));
    assert(rest_tail.drop_first() =~= suffix);

    //  sc(Gen(a)) + sc(Inv(b)) == 0 since a ~ b
    assert(declared_equiv(e, a, b));
    lemma_declared_to_ceer_equiv(e, a, b);
    lemma_ceer_equiv_class_transfer(e, a, b, target);

    lemma_word_count_additive(e, prefix, suffix, target);
}

///  Dispatcher: any valid step preserves word_count.
proof fn lemma_step_preserves_word_count(
    e: CEER, w: CeerWord, step: CeerGroupStep, target: nat,
)
    requires
        ceer_step_valid(e, w, step),
    ensures
        word_count(e, w, target) == word_count(e, apply_ceer_step(w, step), target),
{
    match step {
        CeerGroupStep::FreeReduce { position } => {
            lemma_free_reduce_preserves(e, w, position, target);
        },
        CeerGroupStep::FreeExpand { position, sym } => {
            lemma_free_expand_preserves(e, w, position, sym, target);
        },
        CeerGroupStep::RelatorInsert { position, a, b, stage } => {
            lemma_relator_insert_preserves(e, w, position, a, b, stage, target);
        },
        CeerGroupStep::RelatorDelete { position, a, b, stage } => {
            lemma_relator_delete_preserves(e, w, position, a, b, stage, target);
        },
    }
}

//  ============================================================
//  Phase 5: Final proofs
//  ============================================================

///  A valid derivation preserves word_count.
proof fn lemma_derivation_preserves_word_count(
    e: CEER, w1: CeerWord, w2: CeerWord,
    steps: Seq<CeerGroupStep>, target: nat,
)
    requires
        ceer_derivation_valid(e, w1, w2, steps),
    ensures
        word_count(e, w1, target) == word_count(e, w2, target),
    decreases steps.len(),
{
    if steps.len() == 0 {
        assert(w1 =~= w2);
    } else {
        let next = apply_ceer_step(w1, steps.first());
        lemma_step_preserves_word_count(e, w1, steps.first(), target);
        lemma_derivation_preserves_word_count(e, next, w2, steps.drop_first(), target);
    }
}

///  word_count(Gen(n), n) == 1.
proof fn lemma_generator_word_self_count(e: CEER, n: nat)
    ensures
        word_count(e, generator_word(n), n) == 1,
{
    reveal_with_fuel(word_count, 2);
    assert(generator_word(n).drop_first() =~= Seq::<CeerSymbol>::empty());
    lemma_ceer_equiv_reflexive(e, n);
}

///  word_count(Gen(m), n) depends on ceer_equiv(e, m, n).
proof fn lemma_generator_word_count(e: CEER, m: nat, n: nat)
    ensures
        word_count(e, generator_word(m), n) == if ceer_equiv(e, m, n) { 1int } else { 0int },
{
    reveal_with_fuel(word_count, 2);
    assert(generator_word(m).drop_first() =~= Seq::<CeerSymbol>::empty());
}

///  Backward direction: ceer_group_equiv(Gen(n), Gen(m)) → ceer_equiv(n, m).
pub proof fn lemma_ceer_group_equiv_implies_ceer_equiv(e: CEER, n: nat, m: nat)
    requires
        ceer_group_equiv(e, generator_word(n), generator_word(m)),
    ensures
        ceer_equiv(e, n, m),
{
    let steps = choose|s: Seq<CeerGroupStep>|
        ceer_derivation_valid(e, generator_word(n), generator_word(m), s);
    lemma_derivation_preserves_word_count(
        e, generator_word(n), generator_word(m), steps, n,
    );
    lemma_generator_word_self_count(e, n);
    lemma_generator_word_count(e, m, n);
    //  1 == if ceer_equiv(e,m,n) {1} else {0}, so ceer_equiv(e,m,n) holds
    lemma_ceer_equiv_symmetric(e, m, n);
}

///  Biconditional: ceer_equiv(n, m) ↔ ceer_group_equiv(Gen(n), Gen(m)).
pub proof fn lemma_ceer_equiv_iff_group_equiv(e: CEER, n: nat, m: nat)
    ensures
        ceer_equiv(e, n, m) <==>
            ceer_group_equiv(e, generator_word(n), generator_word(m)),
{
    if ceer_equiv(e, n, m) {
        lemma_ceer_equiv_implies_group_equiv(e, n, m);
    }
    if ceer_group_equiv(e, generator_word(n), generator_word(m)) {
        lemma_ceer_group_equiv_implies_ceer_equiv(e, n, m);
    }
}

} //  verus!
