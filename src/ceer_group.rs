use vstd::prelude::*;
use crate::ceer::*;

verus! {

//  ============================================================
//  Symbol and word types for the CEER group
//  ============================================================

///  Symbol in an infinite generator alphabet (one generator per natural number).
pub enum CeerSymbol {
    Gen { index: nat },
    Inv { index: nat },
}

///  A word in the CEER group's free group.
pub type CeerWord = Seq<CeerSymbol>;

///  Single-generator word: [Gen(n)].
pub open spec fn generator_word(n: nat) -> CeerWord {
    seq![CeerSymbol::Gen { index: n }]
}

///  Formal inverse of a symbol.
pub open spec fn inverse_ceer_symbol(s: CeerSymbol) -> CeerSymbol {
    match s {
        CeerSymbol::Gen { index } => CeerSymbol::Inv { index },
        CeerSymbol::Inv { index } => CeerSymbol::Gen { index },
    }
}

///  Two symbols form an inverse pair (Gen(n) next to Inv(n)).
pub open spec fn is_ceer_inverse_pair(s1: CeerSymbol, s2: CeerSymbol) -> bool {
    match (s1, s2) {
        (CeerSymbol::Gen { index: a }, CeerSymbol::Inv { index: b }) => a == b,
        (CeerSymbol::Inv { index: a }, CeerSymbol::Gen { index: b }) => a == b,
        _ => false,
    }
}

///  The relator for declaring a ≡ b: Gen(a) · Inv(b).
///  In the group, this being a relator means Gen(a) = Gen(b).
pub open spec fn ceer_relator(a: nat, b: nat) -> CeerWord {
    seq![CeerSymbol::Gen { index: a }, CeerSymbol::Inv { index: b }]
}

//  ============================================================
//  Derivation system
//  ============================================================

///  A single derivation step in the CEER group.
pub enum CeerGroupStep {
    ///  Remove an inverse pair at position (cancels w[pos] and w[pos+1]).
    FreeReduce { position: nat },
    ///  Insert sym · sym⁻¹ at position.
    FreeExpand { position: nat, sym: CeerSymbol },
    ///  Insert relator Gen(a)·Inv(b) at position, witnessed by CEER stage.
    RelatorInsert { position: nat, a: nat, b: nat, stage: nat },
    ///  Delete relator Gen(a)·Inv(b) at position, witnessed by CEER stage.
    RelatorDelete { position: nat, a: nat, b: nat, stage: nat },
}

///  Check that a step is valid for word w under CEER e.
pub open spec fn ceer_step_valid(e: CEER, w: CeerWord, step: CeerGroupStep) -> bool {
    match step {
        CeerGroupStep::FreeReduce { position } => {
            position + 1 < w.len() &&
            is_ceer_inverse_pair(w[position as int], w[(position + 1) as int])
        },
        CeerGroupStep::FreeExpand { position, sym } => {
            position <= w.len()
        },
        CeerGroupStep::RelatorInsert { position, a, b, stage } => {
            position <= w.len() &&
            stage_declares(e, stage, a, b)
        },
        CeerGroupStep::RelatorDelete { position, a, b, stage } => {
            stage_declares(e, stage, a, b) &&
            position + 2 <= w.len() &&
            w[position as int] == CeerSymbol::Gen { index: a } &&
            w[(position + 1) as int] == CeerSymbol::Inv { index: b }
        },
    }
}

///  Apply a valid step to produce a new word.
pub open spec fn apply_ceer_step(w: CeerWord, step: CeerGroupStep) -> CeerWord {
    match step {
        CeerGroupStep::FreeReduce { position } => {
            w.subrange(0, position as int) + w.subrange((position + 2) as int, w.len() as int)
        },
        CeerGroupStep::FreeExpand { position, sym } => {
            let pair = seq![sym, inverse_ceer_symbol(sym)];
            w.subrange(0, position as int) + pair + w.subrange(position as int, w.len() as int)
        },
        CeerGroupStep::RelatorInsert { position, a, b, stage } => {
            let rel = ceer_relator(a, b);
            w.subrange(0, position as int) + rel + w.subrange(position as int, w.len() as int)
        },
        CeerGroupStep::RelatorDelete { position, a, b, stage } => {
            w.subrange(0, position as int) + w.subrange((position + 2) as int, w.len() as int)
        },
    }
}

///  A derivation is a sequence of steps transforming w1 into w2.
pub open spec fn ceer_derivation_valid(
    e: CEER, w1: CeerWord, w2: CeerWord, steps: Seq<CeerGroupStep>,
) -> bool
    decreases steps.len(),
{
    if steps.len() == 0 {
        w1 =~= w2
    } else {
        ceer_step_valid(e, w1, steps.first()) &&
        ceer_derivation_valid(
            e,
            apply_ceer_step(w1, steps.first()),
            w2,
            steps.drop_first(),
        )
    }
}

///  Two words are equivalent in the CEER group if there exists a valid derivation.
pub open spec fn ceer_group_equiv(e: CEER, w1: CeerWord, w2: CeerWord) -> bool {
    exists|steps: Seq<CeerGroupStep>| ceer_derivation_valid(e, w1, w2, steps)
}

//  ============================================================
//  Proofs: forward direction (ceer_equiv → group_equiv)
//  ============================================================

///  Empty derivation witnesses reflexivity.
pub proof fn lemma_ceer_group_equiv_reflexive(e: CEER, w: CeerWord)
    ensures
        ceer_group_equiv(e, w, w),
{
    let steps = Seq::<CeerGroupStep>::empty();
    assert(ceer_derivation_valid(e, w, w, steps));
}

///  Concatenating two valid derivations yields a valid derivation.
pub proof fn lemma_derivation_concat(
    e: CEER,
    w1: CeerWord, w2: CeerWord, w3: CeerWord,
    steps1: Seq<CeerGroupStep>, steps2: Seq<CeerGroupStep>,
)
    requires
        ceer_derivation_valid(e, w1, w2, steps1),
        ceer_derivation_valid(e, w2, w3, steps2),
    ensures
        ceer_derivation_valid(e, w1, w3, steps1 + steps2),
    decreases steps1.len(),
{
    if steps1.len() == 0 {
        assert((steps1 + steps2) =~= steps2);
    } else {
        let next = apply_ceer_step(w1, steps1.first());
        let tail1 = steps1.drop_first();
        lemma_derivation_concat(e, next, w2, w3, tail1, steps2);
        assert((steps1 + steps2).first() == steps1.first());
        assert((steps1 + steps2).drop_first() =~= tail1 + steps2);
    }
}

///  Group equivalence is transitive.
pub proof fn lemma_ceer_group_equiv_transitive(
    e: CEER, w1: CeerWord, w2: CeerWord, w3: CeerWord,
)
    requires
        ceer_group_equiv(e, w1, w2),
        ceer_group_equiv(e, w2, w3),
    ensures
        ceer_group_equiv(e, w1, w3),
{
    let steps1 = choose|s: Seq<CeerGroupStep>| ceer_derivation_valid(e, w1, w2, s);
    let steps2 = choose|s: Seq<CeerGroupStep>| ceer_derivation_valid(e, w2, w3, s);
    lemma_derivation_concat(e, w1, w2, w3, steps1, steps2);
}

///  If stage declares (a, b), then Gen(a) ≡ Gen(b) in the CEER group.
///
///  Proof sketch for a ≠ b:
///    Gen(a) → Gen(a) · [Inv(b) · Gen(b)]  (FreeExpand at pos 1 with Inv(b))
///             = Gen(a) · Inv(b) · Gen(b)
///           → Gen(b)                        (RelatorDelete at pos 0, removing Gen(a)·Inv(b))
pub proof fn lemma_declared_equiv_to_group_equiv(e: CEER, n: nat, m: nat)
    requires
        declared_equiv(e, n, m),
    ensures
        ceer_group_equiv(e, generator_word(n), generator_word(m)),
{
    if n == m {
        lemma_ceer_group_equiv_reflexive(e, generator_word(n));
    } else {
        let s = choose|s: nat| stage_declares(e, s, n, m);

        //  Step 1: FreeExpand Inv(m) at position 1
        //  Gen(n) → Gen(n) · Inv(m) · Gen(m)
        let step1 = CeerGroupStep::FreeExpand {
            position: 1,
            sym: CeerSymbol::Inv { index: m },
        };
        let w0 = generator_word(n);
        assert(ceer_step_valid(e, w0, step1));
        let w1 = apply_ceer_step(w0, step1);

        //  w1 should be [Gen(n), Inv(m), Gen(m)]
        assert(w1 =~= seq![
            CeerSymbol::Gen { index: n },
            CeerSymbol::Inv { index: m },
            CeerSymbol::Gen { index: m },
        ]);

        //  Step 2: RelatorDelete Gen(n)·Inv(m) at position 0
        let step2 = CeerGroupStep::RelatorDelete {
            position: 0,
            a: n,
            b: m,
            stage: s,
        };
        assert(ceer_step_valid(e, w1, step2));
        let w2 = apply_ceer_step(w1, step2);

        //  w2 should be [Gen(m)]
        assert(w2 =~= generator_word(m));

        //  Build single-step derivation for step2: w1 → generator_word(m)
        let single = seq![step2];
        assert(single.len() == 1);
        assert(single.first() == step2);
        let after = apply_ceer_step(w1, step2);
        assert(after =~= generator_word(m));
        assert(single.drop_first().len() == 0);
        assert(single.drop_first() =~= Seq::<CeerGroupStep>::empty());
        assert(ceer_derivation_valid(e, generator_word(m), generator_word(m),
            Seq::<CeerGroupStep>::empty()));
        assert(ceer_derivation_valid(e, w1, generator_word(m), single));

        //  Build two-step derivation: w0 → w1 → generator_word(m)
        let steps = seq![step1, step2];
        assert(steps.first() == step1);
        assert(steps.drop_first() =~= single);
        assert(ceer_derivation_valid(e, w0, generator_word(m), steps));
    }
}

///  If ceer_equiv(e, n, m), then Gen(n) ≡ Gen(m) in the CEER group.
///
///  Proof: induction on the CEER chain. Each declared_equiv link gives
///  a group equivalence, and we combine them by transitivity.
pub proof fn lemma_ceer_equiv_implies_group_equiv(e: CEER, n: nat, m: nat)
    requires
        ceer_equiv(e, n, m),
    ensures
        ceer_group_equiv(e, generator_word(n), generator_word(m)),
{
    let chain = choose|chain: Seq<nat>| ceer_equiv_chain(e, n, m, chain);
    lemma_chain_to_group_equiv(e, n, m, chain);
}

///  Helper: induction on chain to get group equivalence.
proof fn lemma_chain_to_group_equiv(e: CEER, n: nat, m: nat, chain: Seq<nat>)
    requires
        ceer_equiv_chain(e, n, m, chain),
    ensures
        ceer_group_equiv(e, generator_word(n), generator_word(m)),
    decreases chain.len(),
{
    if chain.len() == 1 {
        //  n == m, reflexive
        lemma_ceer_group_equiv_reflexive(e, generator_word(n));
    } else {
        let mid = chain[1];
        //  declared_equiv(e, n, mid) → group equiv
        lemma_declared_equiv_to_group_equiv(e, n, mid);

        //  Recurse on tail for mid → m
        lemma_chain_to_group_equiv(e, mid, m, chain.drop_first());

        //  Combine by transitivity
        lemma_ceer_group_equiv_transitive(
            e,
            generator_word(n),
            generator_word(mid),
            generator_word(m),
        );
    }
}

} //  verus!
