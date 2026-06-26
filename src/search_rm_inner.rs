//  GAP-2 / L0 brick B-L0.2c — the dovetail inner body (one (T,s) iteration), built as small phase
//  lemmas (each ~4 gadgets, isolated budget) chained via `lemma_run_add`. See search_rm.rs for the
//  machine layout and docs/gap2-l0-search-rm-plan.md (B-L0.2c).

use vstd::prelude::*;
use crate::machine::*;
use crate::ceer::{CEER, ceer_wf};
use crate::multi_output_primitives::{mk_inc, mk_dj};
use crate::search_rm_clearbank::{clear_bank_instrs, lemma_clear_bank};
use crate::search_rm_compare::lemma_clear_loop;
use crate::search_rm_arith::lemma_run_add;
use crate::search_rm::*;

verus! {

//  ============================================================
//  Register invariants
//  ============================================================

///  Every working temporary EXCEPT ii1(13)/ii2(20) is zero. These are the registers the CMP gadgets
///  require zeroed; ii1/ii2 are cleared per iteration in the reset phase.
pub open spec fn srm_temps_zero(c: Configuration) -> bool {
    &&& c.registers[7] == 0   && c.registers[8] == 0   && c.registers[9] == 0   && c.registers[10] == 0
    &&& c.registers[11] == 0  && c.registers[12] == 0  && c.registers[14] == 0  && c.registers[15] == 0
    &&& c.registers[16] == 0  && c.registers[17] == 0
    &&& c.registers[18] == 0  && c.registers[19] == 0  && c.registers[21] == 0  && c.registers[22] == 0
    &&& c.registers[23] == 0  && c.registers[24] == 0
    &&& c.registers[25] == 0  && c.registers[26] == 0  && c.registers[27] == 0  && c.registers[28] == 0
}

///  The configuration is at INNER_TOP with the per-iteration register state: control registers set,
///  all CMP temporaries zero, E-bank/fuel/ii1/ii2 unconstrained (cleared in the reset phase).
pub open spec fn srm_at_top(e: CEER, c: Configuration, inp_v: nat, t_v: nat, s_v: nat, cnt_v: nat, r_v: nat) -> bool {
    &&& c.pc == 8
    &&& c.registers.len() == srm_numregs(e)
    &&& c.registers[1] == 0
    &&& c.registers[0] == inp_v
    &&& c.registers[3] == t_v
    &&& c.registers[4] == s_v
    &&& c.registers[5] == cnt_v
    &&& c.registers[6] == r_v
    &&& srm_temps_zero(c)
}

//  ============================================================
//  Phase R1 — guard (cnt>0) + clear E-bank + clear ii1 + clear ii2.  INNER_TOP -> B2.
//  ============================================================

#[verifier::rlimit(8000)]
pub proof fn lemma_srm_phase_r1(
    e: CEER, c: Configuration, inp_v: nat, t_v: nat, s_v: nat, cnt_v: nat, r_v: nat,
)
    requires
        ceer_wf(e),
        srm_at_top(e, c, inp_v, t_v, s_v, cnt_v, r_v),
        cnt_v > 0,
    ensures
        exists|g: nat|
            #[trigger] run(search_rm(e), c, g).pc == srm_b2(e)
            && run(search_rm(e), c, g).registers.len() == srm_numregs(e)
            && run(search_rm(e), c, g).registers[1] == 0
            && run(search_rm(e), c, g).registers[0] == inp_v
            && run(search_rm(e), c, g).registers[3] == t_v
            && run(search_rm(e), c, g).registers[4] == s_v
            && run(search_rm(e), c, g).registers[5] == cnt_v - 1
            && run(search_rm(e), c, g).registers[6] == r_v
            && srm_temps_zero(run(search_rm(e), c, g))
            && (forall|r: int| 29 <= r < 29 + srm_ne(e) ==> #[trigger] run(search_rm(e), c, g).registers[r] == 0),
{
    reveal(ceer_wf);
    let m = search_rm(e);
    let ne = srm_ne(e);
    let nr = srm_numregs(e);

    //  --- guard at pc 8: DecJump{cnt=5, ie}; cnt>0 ⇒ decrement, pc 8->9 ---
    lemma_srm_index(e, 8);
    assert(m.instructions[8] == mk_dj(5, srm_ie(e)));
    assert(!is_halted(m, c));
    let c0 = step(m, c).unwrap();
    assert(c0.pc == 9);
    assert(c0.registers == c.registers.update(5, (cnt_v - 1) as nat));
    assert(run(m, c, 1) == c0) by { lemma_run_unfold(m, c, 1); }

    //  --- clear E-bank: clear_bank(29, ne, 1, 9) ---
    assert forall|j: int| 0 <= j < 2 * ne implies
        m.instructions[(9 + j) as int] == #[trigger] clear_bank_instrs(29, ne, 1, 9)[j]
    by {
        lemma_srm_index(e, 9 + j);
        assert(srm_instr(e, 9 + j) == clear_bank_instrs(29, ne, 1, 9)[j]);
    }
    assert(c0.registers[1] == 0) by { assert(5 != 1); }
    lemma_clear_bank(m, c0, 29, ne, 1, 9);
    let g1 = choose|g: nat|
        run(m, c0, g).pc == 9 + 2 * ne
        && run(m, c0, g).registers.len() == m.num_regs
        && (forall|r: int| 0 <= r < m.num_regs as int ==>
                run(m, c0, g).registers[r] == (if 29 <= r && r < 29 + ne { 0nat } else { c0.registers[r] }));
    let c1 = run(m, c0, g1);
    assert(m.num_regs == nr);
    assert(c1.pc == 9 + 2 * ne);
    assert(c1.pc == srm_clrii1(e));

    //  --- clear ii1 at clrii1: clear_instrs(13, 1, clrii1) ---
    lemma_srm_index(e, srm_clrii1(e) as int);
    lemma_srm_index(e, srm_clrii1(e) as int + 1);
    assert(m.instructions[srm_clrii1(e) as int] == mk_dj(13, srm_clrii1(e) + 2));
    assert(m.instructions[(srm_clrii1(e) + 1) as int] == mk_dj(1, srm_clrii1(e)));
    assert(c1.pc == srm_clrii1(e));
    assert(c1.registers[1] == 0) by { assert(!(29 <= 1 < 29 + ne)); }
    lemma_clear_loop(m, c1, 13, 1, srm_clrii1(e), c1.registers[13]);
    let s2: nat = (2 * c1.registers[13] + 1) as nat;
    let c2 = run(m, c1, s2);
    assert(c2.pc == srm_clrii2(e));
    assert(c2.registers[13] == 0);

    //  --- clear ii2 at clrii2: clear_instrs(20, 1, clrii2) ---
    lemma_srm_index(e, srm_clrii2(e) as int);
    lemma_srm_index(e, srm_clrii2(e) as int + 1);
    assert(m.instructions[srm_clrii2(e) as int] == mk_dj(20, srm_clrii2(e) + 2));
    assert(m.instructions[(srm_clrii2(e) + 1) as int] == mk_dj(1, srm_clrii2(e)));
    assert(c2.registers[1] == 0) by { assert(20 != 13); }
    lemma_clear_loop(m, c2, 20, 1, srm_clrii2(e), c2.registers[20]);
    let s3: nat = (2 * c2.registers[20] + 1) as nat;
    let c3 = run(m, c2, s3);
    assert(c3.pc == srm_clrii2(e) + 2);
    assert(c3.pc == srm_b2(e));
    assert(c3.registers[20] == 0);

    //  --- compose: run(m, c, g) == c3 ---
    lemma_run_add(m, c1, s2, s3);
    lemma_run_add(m, c0, g1, (s2 + s3) as nat);
    lemma_run_add(m, c, 1, (g1 + s2 + s3) as nat);
    let g: nat = (1 + g1 + s2 + s3) as nat;
    assert(run(m, c, g) == c3);

    //  --- register postconditions ---
    //  control + temps preserved through the three clears (none touches 0,1,3,4,5(after guard),6 or non-ii temps)
    assert(c3.registers.len() == nr);
    assert(c3.registers[1] == 0);
    assert(c3.registers[0] == inp_v);
    assert(c3.registers[3] == t_v);
    assert(c3.registers[4] == s_v);
    assert(c3.registers[5] == (cnt_v - 1) as nat);
    assert(c3.registers[6] == r_v);
    assert(srm_temps_zero(c3));
    assert(forall|r: int| 29 <= r < 29 + ne ==> #[trigger] c3.registers[r] == 0) by {
        //  E-bank zeroed by clear_bank; ii-clears (regs 13,20) don't touch r>=29
        assert forall|r: int| 29 <= r < 29 + ne implies c3.registers[r] == 0 by {
            assert(c1.registers[r] == 0);
        }
    }
}

///  Local `run` unfold helper (private copy).
proof fn lemma_run_unfold(m: RegisterMachine, c: Configuration, fuel: nat)
    requires !is_halted(m, c), fuel > 0,
    ensures run(m, c, fuel) == run(m, step(m, c).unwrap(), (fuel - 1) as nat),
{
}

} //  verus!
