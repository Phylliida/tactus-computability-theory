use vstd::prelude::*;
use crate::machine::*;
use crate::computable::*;
use crate::zfc_enumerator::*;
use crate::compspec_decode::*;

verus! {

//  ============================================================
//  Deriving axiom_enumerator_machine_exists from CompSpec
//  ============================================================
//
//  We show that enumerator_spec is CompSpec-definable, then
//  apply axiom_computable_partial_fn to get a register machine.
//
//  Strategy: We define the three CompSpec terms via `choose`,
//  selecting any CompSpec that computes the right function.
//  The EXISTENCE of such terms is the mathematical claim
//  "these functions are primitive recursive," which we assert
//  as external_body axioms (axiom_halts_is_prim_rec, etc.).
//  The proofs then follow trivially from the choose definitions.

//  ============================================================
//  Primitive recursiveness axioms
//  ============================================================
//
//  These axioms assert that specific functions are primitive
//  recursive (i.e., CompSpec-representable). This is a standard
//  mathematical fact: is_valid_iff_proof_code is decidable by
//  bounded checks on Cantor-encoded proof structures, and the
//  output extraction is a composition of primitive recursive
//  decoding functions.

///  Helper: c computes the halting predicate for is_valid_iff_proof_code.
pub open spec fn is_halts_comp(c: CompSpec) -> bool {
    forall|s: nat| (#[trigger] eval_comp(c, s) != 0) <==> is_valid_iff_proof_code(s)
}

///  Helper: c computes the first output of enumerator_spec.
pub open spec fn is_output1_comp(c: CompSpec) -> bool {
    forall|s: nat| is_valid_iff_proof_code(s) ==>
        (#[trigger] eval_comp(c, s)) == enumerator_spec(s).unwrap().0
}

///  Helper: c computes the second output of enumerator_spec.
pub open spec fn is_output2_comp(c: CompSpec) -> bool {
    forall|s: nat| is_valid_iff_proof_code(s) ==>
        (#[trigger] eval_comp(c, s)) == enumerator_spec(s).unwrap().1
}

///  Axiom: is_valid_iff_proof_code is a primitive recursive predicate.
///  There exists a CompSpec c such that eval_comp(c, s) != 0 iff
///  is_valid_iff_proof_code(s).
#[verifier::external_body]
pub proof fn axiom_halts_is_prim_rec()
    ensures
        exists|c: CompSpec| #[trigger] is_halts_comp(c),
{
}

///  The first output component of enumerator_spec is primitive recursive.
///  There exists a CompSpec c such that for all valid proof codes s,
///  eval_comp(c, s) equals the first output of enumerator_spec(s).
pub proof fn axiom_output1_is_prim_rec()
    ensures
        exists|c: CompSpec| #[trigger] is_output1_comp(c),
{
    lemma_output1_comp_correct();
}

///  The second output component of enumerator_spec is primitive recursive.
///  There exists a CompSpec c such that for all valid proof codes s,
///  eval_comp(c, s) equals the second output of enumerator_spec(s).
pub proof fn axiom_output2_is_prim_rec()
    ensures
        exists|c: CompSpec| #[trigger] is_output2_comp(c),
{
    lemma_output2_comp_correct();
}

//  ============================================================
//  CompSpec terms via choose
//  ============================================================

///  The halting predicate as a CompSpec: chosen to satisfy
///  eval_comp(c, s) != 0 <==> is_valid_iff_proof_code(s).
pub open spec fn enumerator_halts_comp() -> CompSpec {
    choose|c: CompSpec| is_halts_comp(c)
}

///  First output component as a CompSpec: chosen to satisfy
///  eval_comp(c, s) == enumerator_spec(s).unwrap().0 for valid codes.
pub open spec fn enumerator_output1_comp() -> CompSpec {
    choose|c: CompSpec| is_output1_comp(c)
}

///  Second output component as a CompSpec: chosen to satisfy
///  eval_comp(c, s) == enumerator_spec(s).unwrap().1 for valid codes.
pub open spec fn enumerator_output2_comp() -> CompSpec {
    choose|c: CompSpec| is_output2_comp(c)
}

///  Proof: halts_comp matches is_valid_iff_proof_code.
///  Derives from axiom_halts_is_prim_rec + choose definition.
proof fn lemma_halts_comp_matches()
    ensures
        forall|s: nat| eval_comp(enumerator_halts_comp(), s) != 0
            <==> is_valid_iff_proof_code(s),
{
    //  axiom_halts_is_prim_rec ensures exists|c| is_halts_comp(c)
    //  enumerator_halts_comp() = choose|c| is_halts_comp(c)
    //  So is_halts_comp(enumerator_halts_comp()) holds, which unfolds
    //  to the forall|s| we need.
    axiom_halts_is_prim_rec();
}

///  Proof: output comps match enumerator_spec outputs.
///  Derives from axiom_output1_is_prim_rec, axiom_output2_is_prim_rec + choose definitions.
proof fn lemma_output_comp_matches()
    ensures
        forall|s: nat| is_valid_iff_proof_code(s) ==> {
            let spec_out = enumerator_spec(s).unwrap();
            &&& eval_comp(enumerator_output1_comp(), s) == spec_out.0
            &&& eval_comp(enumerator_output2_comp(), s) == spec_out.1
        },
{
    //  axiom_output1_is_prim_rec ensures exists|c| is_output1_comp(c)
    //  axiom_output2_is_prim_rec ensures exists|c| is_output2_comp(c)
    //  The choose definitions give us is_output1_comp(enumerator_output1_comp())
    //  and is_output2_comp(enumerator_output2_comp()), which unfold to our ensures.
    axiom_output1_is_prim_rec();
    axiom_output2_is_prim_rec();
}

///  Derive axiom_enumerator_machine_exists from the reduced CTT axiom.
pub proof fn lemma_derive_enumerator_machine()
    ensures
        exists|rm: RegisterMachine|
            machine_wf(rm) && rm.num_regs >= 3 &&
            (forall|s: nat| halts(rm, s) <==> enumerator_spec(s).is_some()) &&
            (forall|s: nat, fuel: nat|
                run_halts(rm, initial_config(rm, s), fuel) ==>
                enumerator_spec(s) == Some((
                    run(rm, initial_config(rm, s), fuel).registers[1],
                    run(rm, initial_config(rm, s), fuel).registers[2]
                ))),
{
    //  Step 1: Get the register machine from the reduced axiom
    axiom_computable_partial_fn(
        enumerator_halts_comp(),
        enumerator_output1_comp(),
        enumerator_output2_comp(),
    );

    let rm = choose|rm: RegisterMachine|
        machine_wf(rm) && rm.num_regs >= 3 &&
        (forall|s: nat| halts(rm, s) <==> eval_comp(enumerator_halts_comp(), s) != 0) &&
        (forall|s: nat, fuel: nat|
            run_halts(rm, initial_config(rm, s), fuel) ==> (
                run(rm, initial_config(rm, s), fuel).registers[1] == eval_comp(enumerator_output1_comp(), s) &&
                run(rm, initial_config(rm, s), fuel).registers[2] == eval_comp(enumerator_output2_comp(), s)
            ));

    //  Step 2: Bridge to enumerator_spec
    lemma_halts_comp_matches();
    lemma_output_comp_matches();

    //  Step 3: Show the machine satisfies the enumerator_spec ensures
    assert forall|s: nat| halts(rm, s) <==> enumerator_spec(s).is_some() by {
        //  halts(rm, s) <==> eval_comp(halts_comp, s) != 0 <==> is_valid_iff_proof_code(s)
        //  enumerator_spec(s).is_some() <==> is_valid_iff_proof_code(s)
    };

    assert forall|s: nat, fuel: nat|
        run_halts(rm, initial_config(rm, s), fuel) ==>
        enumerator_spec(s) == Some((
            run(rm, initial_config(rm, s), fuel).registers[1],
            run(rm, initial_config(rm, s), fuel).registers[2]
        ))
    by {
        if run_halts(rm, initial_config(rm, s), fuel) {
            //  rm halts → halts(rm, s) → enumerator_spec(s).is_some()
            assert(halts(rm, s));
            assert(enumerator_spec(s).is_some());
            let spec_out = enumerator_spec(s).unwrap();
            //  registers match eval_comp, which matches spec_out
            assert(run(rm, initial_config(rm, s), fuel).registers[1] == eval_comp(enumerator_output1_comp(), s));
            assert(run(rm, initial_config(rm, s), fuel).registers[2] == eval_comp(enumerator_output2_comp(), s));
            assert(eval_comp(enumerator_output1_comp(), s) == spec_out.0);
            assert(eval_comp(enumerator_output2_comp(), s) == spec_out.1);
        }
    };
}

} //  verus!
