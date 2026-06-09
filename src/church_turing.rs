use vstd::prelude::*;
use crate::machine::*;
use crate::zfc_enumerator::*;
use crate::enumerator_computable::*;

verus! {

///  A register machine exists that implements the proof-checking enumerator.
///
///  Previously an axiom (external_body). Now derived from:
///    1. axiom_computable_partial_fn (generic CTT: CompSpec → register machine)
///    2. Verified proof that enumerator_spec is CompSpec-definable
///       (Phase 1: matching proofs deferred as external_body in
///        enumerator_computable.rs; Phase 2 will verify them fully)
///
///  The domain-specific logic (proof checking is decidable, output
///  extraction is primitive recursive) is separated from the generic
///  Church-Turing claim (primitive recursive → register machine).
pub proof fn axiom_enumerator_machine_exists()
    ensures
        exists|rm: RegisterMachine|
            machine_wf(rm) && rm.num_regs >= 3 &&
            //  Halts iff enumerator_spec produces output
            (forall|s: nat| halts(rm, s) <==> enumerator_spec(s).is_some()) &&
            //  When it halts, registers match the spec output
            (forall|s: nat, fuel: nat|
                run_halts(rm, initial_config(rm, s), fuel) ==>
                enumerator_spec(s) == Some((
                    run(rm, initial_config(rm, s), fuel).registers[1],
                    run(rm, initial_config(rm, s), fuel).registers[2]
                ))),
{
    lemma_derive_enumerator_machine();
}

} //  verus!
