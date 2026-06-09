use vstd::prelude::*;
use crate::machine::*;

verus! {

///  A machine `m` computes the total function `f`:
///  it halts on every input and register 0 contains f(input).
pub open spec fn computes(m: RegisterMachine, f: spec_fn(nat) -> nat) -> bool {
    m.num_regs > 0 &&
    forall|input: nat| #[trigger] halts(m, input) && output(m, input) == f(input)
}

///  A function f: nat -> nat is computable if some register machine computes it.
pub open spec fn is_computable_fn(f: spec_fn(nat) -> nat) -> bool {
    exists|m: RegisterMachine| computes(m, f)
}

///  Machine m accepts exactly set s.
pub open spec fn machine_accepts(m: RegisterMachine, s: spec_fn(nat) -> bool) -> bool {
    m.num_regs > 0 &&
    forall|n: nat| s(n) <==> #[trigger] halts(m, n)
}

///  A set S ⊆ ℕ is computably enumerable (c.e.) if there exists a machine
///  that halts on exactly the elements of S.
pub open spec fn is_ce(s: spec_fn(nat) -> bool) -> bool {
    exists|m: RegisterMachine| #[trigger] machine_accepts(m, s)
}

///  A set S is computable if both S and its complement are c.e.
pub open spec fn is_computable_set(s: spec_fn(nat) -> bool) -> bool {
    is_ce(s) && is_ce(|n: nat| !s(n))
}

///  A computable set is c.e. (trivially from the definition).
pub proof fn lemma_computable_set_is_ce(s: spec_fn(nat) -> bool)
    requires
        is_computable_set(s),
    ensures
        is_ce(s),
{
}

///  A computable total function has c.e. domain (domain is all of ℕ).
pub proof fn lemma_computable_fn_total(m: RegisterMachine, f: spec_fn(nat) -> nat)
    requires
        computes(m, f),
    ensures
        forall|input: nat| halts(m, input),
{
}

} //  verus!
