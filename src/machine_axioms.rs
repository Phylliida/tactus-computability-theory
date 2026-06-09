use vstd::prelude::*;
use crate::machine::*;
use crate::ceer::*;
use crate::zfc_ceer::*;
use crate::zfc_enumerator::*;
use crate::church_turing::*;

verus! {

///  ZFC proof enumeration generates a CEER.
///
///  Previously an axiom (external_body). Now fully derived from
///  `axiom_enumerator_machine_exists` (Church-Turing thesis) plus
///  verified soundness/completeness of the proof enumerator.
pub proof fn axiom_zfc_ceer()
    ensures
        exists|e: CEER| ceer_wf(e) &&
            (forall|n: nat, m: nat| n != m && zfc_equiv_nat(n, m) ==> declared_equiv(e, n, m)) &&
            (forall|n: nat, m: nat| declared_equiv(e, n, m) ==> zfc_equiv_nat(n, m)),
{
    //  Step 1: Get the register machine from the reduced axiom
    axiom_enumerator_machine_exists();
    let rm = choose|rm: RegisterMachine|
        machine_wf(rm) && rm.num_regs >= 3 &&
        (forall|s: nat| halts(rm, s) <==> enumerator_spec(s).is_some()) &&
        (forall|s: nat, fuel: nat|
            run_halts(rm, initial_config(rm, s), fuel) ==>
            enumerator_spec(s) == Some((
                run(rm, initial_config(rm, s), fuel).registers[1],
                run(rm, initial_config(rm, s), fuel).registers[2]
            )));

    //  Step 2: Construct the CEER
    let e = CEER { enumerator: rm };

    //  Step 3: ceer_wf(e)
    assert(ceer_wf(e)) by { reveal(ceer_wf); };

    //  Step 4: Bridge — declared_pair(e, s) == enumerator_spec(s) for all s
    assert forall|s: nat| declared_pair(e, s) == enumerator_spec(s) by {
        if halts(rm, s) {
            //  declared_pair chooses a fuel, forall|fuel| gives enumerator_spec match
        } else {
            //  Both None
        }
    };

    //  Step 5: Soundness — declared_equiv(e, n, m) ==> zfc_equiv_nat(n, m)
    assert forall|n: nat, m: nat| declared_equiv(e, n, m) implies zfc_equiv_nat(n, m) by {
        let s = choose|s: nat| stage_declares(e, s, n, m);
        //  stage_declares means declared_pair(e, s) has n,m (in some order)
        //  Since declared_pair(e, s) == enumerator_spec(s):
        assert(enumerator_spec(s).is_some());
        let pair = enumerator_spec(s).unwrap();
        if pair.0 == n && pair.1 == m {
            lemma_enumerator_soundness(s, n, m);
        } else {
            //  pair == (m, n)
            lemma_enumerator_soundness(s, pair.0, pair.1);
            lemma_zfc_equiv_nat_symmetric(pair.0, pair.1);
        }
    };

    //  Step 6: Completeness — n != m && zfc_equiv_nat(n, m) ==> declared_equiv(e, n, m)
    assert forall|n: nat, m: nat| n != m && zfc_equiv_nat(n, m) implies declared_equiv(e, n, m) by {
        lemma_enumerator_completeness(n, m);
        let s = choose|s: nat| enumerator_spec(s) == Some((n, m));
        //  Since declared_pair(e, s) == enumerator_spec(s) == Some((n, m)):
        assert(declared_pair(e, s) == Some((n, m)));
        assert(stage_declares(e, s, n, m));
    };
}

} //  verus!
