use vstd::prelude::*;
use crate::machine::*;
use crate::computation::*;

verus! {

///  A Computably Enumerable Equivalence Relation (CEER).
///
///  At each stage s, the enumerator machine runs on input s.
///  If it halts, registers 1 and 2 contain a declared pair (a, b).
///  The CEER is the reflexive-symmetric-transitive closure of all declared pairs.
pub struct CEER {
    pub enumerator: RegisterMachine,
}

///  Well-formedness: machine is well-formed and has at least 3 registers
///  (reg[0]=stage input, reg[1]=left output, reg[2]=right output).
#[verifier::opaque]
pub open spec fn ceer_wf(e: CEER) -> bool {
    e.enumerator.num_regs >= 3 && machine_wf(e.enumerator)
}

///  If the enumerator halts on stage s, return the declared pair (reg[1], reg[2]).
pub open spec fn declared_pair(e: CEER, s: nat) -> Option<(nat, nat)> {
    if e.enumerator.num_regs < 3 {
        None
    } else if halts(e.enumerator, s) {
        let fuel = choose|fuel: nat| run_halts(e.enumerator, initial_config(e.enumerator, s), fuel);
        let final_config = run(e.enumerator, initial_config(e.enumerator, s), fuel);
        Some((final_config.registers[1], final_config.registers[2]))
    } else {
        None
    }
}

///  The declared pair is well-defined: it doesn't depend on which fuel is chosen.
pub proof fn lemma_declared_pair_well_defined(e: CEER, s: nat, f1: nat, f2: nat)
    requires
        e.enumerator.num_regs >= 3,
        run_halts(e.enumerator, initial_config(e.enumerator, s), f1),
        run_halts(e.enumerator, initial_config(e.enumerator, s), f2),
    ensures
        run(e.enumerator, initial_config(e.enumerator, s), f1)
         == run(e.enumerator, initial_config(e.enumerator, s), f2),
{
    lemma_run_deterministic(e.enumerator, initial_config(e.enumerator, s), f1, f2);
}

///  Stage s declares a ≡ b (directly, as a single pair).
pub open spec fn stage_declares(e: CEER, s: nat, a: nat, b: nat) -> bool {
    match declared_pair(e, s) {
        Some(pair) => (pair.0 == a && pair.1 == b) || (pair.0 == b && pair.1 == a),
        None => false,
    }
}

///  A ≡ b is declared at some stage (one-step relation).
pub open spec fn declared_equiv(e: CEER, a: nat, b: nat) -> bool {
    exists|s: nat| stage_declares(e, s, a, b)
}

///  An equivalence chain: a sequence of intermediate values where consecutive
///  pairs are declared equivalent. Witnesses a ≡ b via a = chain[0], ..., chain[n] = b.
///
///  The chain includes both endpoints. For a ≡ a, the chain is [a].
///  For a ≡ b via declared pair, the chain is [a, b].
pub open spec fn ceer_equiv_chain(e: CEER, a: nat, b: nat, chain: Seq<nat>) -> bool
    decreases chain.len(),
{
    if chain.len() == 0 {
        false //  empty chain is invalid
    } else if chain.len() == 1 {
        //  Reflexive: a == b and chain[0] == a
        a == b && chain[0] == a
    } else {
        //  chain[0] == a, last == b, and consecutive pairs are declared equivalent
        chain[0] == a &&
        chain[chain.len() - 1] == b &&
        declared_equiv(e, chain[0], chain[1]) &&
        ceer_equiv_chain(e, chain[1], b, chain.drop_first())
    }
}

///  Two naturals are CEER-equivalent if there exists a witnessing chain.
pub open spec fn ceer_equiv(e: CEER, a: nat, b: nat) -> bool {
    exists|chain: Seq<nat>| #[trigger] ceer_equiv_chain(e, a, b, chain)
}

///  CEER E computably reduces to CEER F: there exists a computable total function g
///  such that E.equiv(a,b) ↔ F.equiv(g(a), g(b)).
pub open spec fn ceer_reduces_to(e: CEER, f: CEER) -> bool {
    exists|g: spec_fn(nat) -> nat| is_computable_fn(g) &&
        forall|a: nat, b: nat| ceer_equiv(e, a, b) <==> ceer_equiv(f, g(a), g(b))
}

///  A CEER is Σ₀₁-universal if every CEER reduces to it.
pub open spec fn is_sigma01_universal(f: CEER) -> bool {
    forall|e: CEER| ceer_reduces_to(e, f)
}

//  ============================================================
//  Proof lemmas — equivalence relation properties
//  ============================================================

///  Reflexivity: a ≡ a via the singleton chain [a].
pub proof fn lemma_ceer_equiv_reflexive(e: CEER, a: nat)
    ensures
        ceer_equiv(e, a, a),
{
    let chain = seq![a];
    assert(chain.len() == 1);
    assert(chain[0] == a);
    assert(ceer_equiv_chain(e, a, a, chain));
}

///  Helper: reverse a chain witnessing a ≡ b to get a chain for b ≡ a.
pub proof fn lemma_chain_reverse(e: CEER, a: nat, b: nat, chain: Seq<nat>)
    requires
        ceer_equiv_chain(e, a, b, chain),
    ensures
        ceer_equiv_chain(e, b, a, chain.reverse()),
    decreases chain.len(),
{
    if chain.len() <= 1 {
        assert(chain.reverse() =~= chain);
    } else {
        let x = chain[1];
        let tail = chain.drop_first();
        lemma_chain_reverse(e, x, b, tail);
        let rev_tail = tail.reverse();

        lemma_reverse_is_push(chain);
        assert(chain.reverse() =~= tail.reverse().push(a));

        assert(declared_equiv(e, a, x));
        assert(declared_equiv(e, x, a)) by {
            let s = choose|s: nat| stage_declares(e, s, a, x);
            assert(stage_declares(e, s, x, a));
        };

        lemma_chain_extend(e, b, x, a, rev_tail);
    }
}

///  Helper: if chain witnesses a ≡ b and declared_equiv(b, c), then chain.push(c) witnesses a ≡ c.
proof fn lemma_chain_extend(e: CEER, a: nat, b: nat, c: nat, chain: Seq<nat>)
    requires
        ceer_equiv_chain(e, a, b, chain),
        declared_equiv(e, b, c),
    ensures
        ceer_equiv_chain(e, a, c, chain.push(c)),
    decreases chain.len(),
{
    let ext = chain.push(c);
    if chain.len() == 1 {
        assert(ext.len() == 2);
        assert(ext[0] == a);
        assert(ext[1] == c);
        assert(ext[ext.len() - 1] == c);
        assert(declared_equiv(e, a, c)) by {
            assert(a == b);
        };
        assert(ext.drop_first() =~= seq![c]);
        assert(ceer_equiv_chain(e, c, c, ext.drop_first()));
    } else {
        let x = chain[1];
        let tail = chain.drop_first();
        lemma_chain_extend(e, x, b, c, tail);
        assert(ext[0] == a);
        assert(ext[ext.len() - 1] == c);
        assert(declared_equiv(e, ext[0], ext[1]));
        assert(ext.drop_first() =~= tail.push(c));
        assert(ceer_equiv_chain(e, x, c, ext.drop_first()));
    }
}

///  Helper: reversing [head] ++ tail == tail.reverse().push(head).
proof fn lemma_reverse_is_push(s: Seq<nat>)
    requires s.len() > 0,
    ensures s.reverse() =~= s.drop_first().reverse().push(s[0]),
{
    let n = s.len();
    let rev = s.reverse();
    let expected = s.drop_first().reverse().push(s[0]);
    assert(rev.len() == expected.len());
    assert forall|i: int| 0 <= i < rev.len() implies rev[i] == expected[i] by {
        if i < n - 1 {
            assert(rev[i] == s[n - 1 - i]);
            assert(expected[i] == s.drop_first().reverse()[i]);
            assert(s.drop_first().reverse()[i] == s.drop_first()[(n - 1) - 1 - i]);
            assert(s.drop_first()[(n - 1) - 1 - i] == s[(n - 1) - 1 - i + 1]);
        } else {
            assert(rev[i] == s[0]);
        }
    };
}

///  Symmetry: if a ≡ b then b ≡ a.
pub proof fn lemma_ceer_equiv_symmetric(e: CEER, a: nat, b: nat)
    requires
        ceer_equiv(e, a, b),
    ensures
        ceer_equiv(e, b, a),
{
    let chain = choose|chain: Seq<nat>| ceer_equiv_chain(e, a, b, chain);
    lemma_chain_reverse(e, a, b, chain);
    assert(ceer_equiv_chain(e, b, a, chain.reverse()));
}

///  Helper: concatenate two chains. If chain1 witnesses a ≡ b and chain2 witnesses b ≡ c,
///  then chain1 + chain2.drop_first() witnesses a ≡ c.
pub proof fn lemma_chain_concat(e: CEER, a: nat, b: nat, c: nat, chain1: Seq<nat>, chain2: Seq<nat>)
    requires
        ceer_equiv_chain(e, a, b, chain1),
        ceer_equiv_chain(e, b, c, chain2),
    ensures
        ceer_equiv_chain(e, a, c, chain1 + chain2.drop_first()),
    decreases chain1.len(),
{
    let combined = chain1 + chain2.drop_first();
    if chain1.len() == 1 {
        assert(combined =~= chain2) by {
            if chain2.len() == 1 {
                assert(chain2.drop_first() =~= Seq::<nat>::empty());
                assert(combined =~= seq![a]);
                assert(a == b && b == c);
                assert(chain2 =~= seq![b]);
            } else {
                assert(chain2[0] == b);
                assert(a == b);
            }
        };
    } else {
        let x = chain1[1];
        let tail1 = chain1.drop_first();
        lemma_chain_concat(e, x, b, c, tail1, chain2);
        let inner = tail1 + chain2.drop_first();

        assert(combined[0] == a);
        assert(combined.drop_first() =~= inner);
        assert(combined[combined.len() - 1] == c) by {
            if chain2.drop_first().len() > 0 {
                assert(combined[combined.len() - 1] == chain2.drop_first()[chain2.drop_first().len() - 1]);
                assert(chain2.drop_first()[chain2.drop_first().len() - 1] == chain2[chain2.len() - 1]);
            } else {
                assert(chain2.len() == 1);
                assert(b == c);
                assert(combined =~= chain1);
                assert(chain1[chain1.len() - 1] == b);
            }
        };
        assert(declared_equiv(e, combined[0], combined[1]));
        assert(ceer_equiv_chain(e, x, c, combined.drop_first()));
    }
}

///  Transitivity: if a ≡ b and b ≡ c then a ≡ c.
pub proof fn lemma_ceer_equiv_transitive(e: CEER, a: nat, b: nat, c: nat)
    requires
        ceer_equiv(e, a, b),
        ceer_equiv(e, b, c),
    ensures
        ceer_equiv(e, a, c),
{
    let chain1 = choose|chain: Seq<nat>| ceer_equiv_chain(e, a, b, chain);
    let chain2 = choose|chain: Seq<nat>| ceer_equiv_chain(e, b, c, chain);
    lemma_chain_concat(e, a, b, c, chain1, chain2);
    let combined = chain1 + chain2.drop_first();
    assert(ceer_equiv_chain(e, a, c, combined));
}

///  The CEER equivalence is an equivalence relation (refl/sym/trans).
pub proof fn lemma_ceer_equiv_is_equivalence_relation(e: CEER)
    requires
        ceer_wf(e),
    ensures
        forall|a: nat| ceer_equiv(e, a, a),
        forall|a: nat, b: nat| ceer_equiv(e, a, b) ==> ceer_equiv(e, b, a),
        forall|a: nat, b: nat, c: nat|
            ceer_equiv(e, a, b) && ceer_equiv(e, b, c) ==> ceer_equiv(e, a, c),
{
    assert forall|a: nat| ceer_equiv(e, a, a) by {
        lemma_ceer_equiv_reflexive(e, a);
    };
    assert forall|a: nat, b: nat| ceer_equiv(e, a, b) implies ceer_equiv(e, b, a) by {
        lemma_ceer_equiv_symmetric(e, a, b);
    };
    assert forall|a: nat, b: nat, c: nat|
        ceer_equiv(e, a, b) && ceer_equiv(e, b, c) implies ceer_equiv(e, a, c)
    by {
        lemma_ceer_equiv_transitive(e, a, b, c);
    };
}

} //  verus!
