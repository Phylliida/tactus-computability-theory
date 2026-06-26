//  GAP-2 / L0 brick B-L0.2c (pre) — combined instrument outcome.
//
//  `lemma_instrument_outcome` merges the two directional instrument lemmas (`lemma_instrument_halts`
//  ⟸ and `lemma_instrument_reaches_sink` ⟹) into ONE existential step-count `g`, so the SAME `g`
//  witnesses both the soundness implication (reaching HALTED ⟹ E genuinely halted, bank == run(E,phi))
//  and the completeness implication (E halts within phi-1 ⟹ HALTED is reached). The dovetail's inner
//  body (lemma_inner_body) consumes this single outcome to characterise one (s,T) iteration without an
//  existential-witness mismatch between the halt/timeout case-split.
//
//  See docs/gap2-l0-search-rm-plan.md (B-L0.2c).

use vstd::prelude::*;
use crate::machine::*;
use crate::search_rm_sim::{
    instr_configs_agree, instrument_frame, lemma_instrument_halts, lemma_instrument_reaches_sink,
};

verus! {

///  One instrument run from the matching config reaches a unique sink within `2*phi+1` steps, with:
///   - soundness: `pc == halted_pc ==> run_halts(E, c_sub, phi) ∧ bank == run(E, c_sub, phi)`;
///   - completeness: `run_halts(E, c_sub, phi-1) ==> pc == halted_pc`;
///   - frame: out-of-bank registers preserved.
pub proof fn lemma_instrument_outcome(
    rm_sub: RegisterMachine, m: RegisterMachine,
    reg_offset: nat, pc_offset: nat, halted_pc: nat, timeout_pc: nat,
    fuel_reg: nat, scratch: nat,
    c_sub: Configuration, c: Configuration, phi: nat,
)
    requires
        machine_wf(rm_sub),
        config_wf(rm_sub, c_sub),
        instr_configs_agree(rm_sub, reg_offset, pc_offset, fuel_reg, scratch, phi, c_sub, c),
        phi >= 1,
        c.registers.len() == m.num_regs,
        instrument_frame(rm_sub, m, reg_offset, pc_offset, halted_pc, timeout_pc, fuel_reg, scratch),
    ensures
        exists|g: nat| g <= 2 * phi + 1
            && (#[trigger] run(m, c, g).pc == halted_pc || run(m, c, g).pc == timeout_pc)
            && run(m, c, g).registers.len() == m.num_regs
            && (run(m, c, g).pc == halted_pc ==>
                    run_halts(rm_sub, c_sub, phi)
                    && (forall|r: int| 0 <= r < rm_sub.num_regs as int ==>
                            #[trigger] run(m, c, g).registers[(r + reg_offset) as int]
                                == run(rm_sub, c_sub, phi).registers[r]))
            && (run_halts(rm_sub, c_sub, (phi - 1) as nat) ==> run(m, c, g).pc == halted_pc)
            && (forall|jj: int| 0 <= jj < m.num_regs as int
                    && (jj < reg_offset || jj >= reg_offset + rm_sub.num_regs)
                    && jj != fuel_reg as int && jj != scratch as int
                    ==> #[trigger] run(m, c, g).registers[jj] == c.registers[jj]),
{
    if run_halts(rm_sub, c_sub, (phi - 1) as nat) {
        lemma_instrument_halts(rm_sub, m, reg_offset, pc_offset, halted_pc, timeout_pc,
            fuel_reg, scratch, c_sub, c, phi);
        let g_h = choose|g: nat| g <= 2 * phi
            && run(m, c, g).pc == halted_pc
            && (forall|r: int| 0 <= r < rm_sub.num_regs as int ==>
                    #[trigger] run(m, c, g).registers[(r + reg_offset) as int]
                        == run(rm_sub, c_sub, (phi - 1) as nat).registers[r])
            && run(m, c, g).registers[scratch as int] == 0
            && run(m, c, g).registers.len() == m.num_regs
            && (forall|jj: int| 0 <= jj < m.num_regs as int
                    && (jj < reg_offset || jj >= reg_offset + rm_sub.num_regs)
                    && jj != fuel_reg as int && jj != scratch as int
                    ==> #[trigger] run(m, c, g).registers[jj] == c.registers[jj]);
        //  run(E, phi-1) == run(E, phi) and run_halts(E, phi), from monotonicity.
        lemma_run_monotone(rm_sub, c_sub, (phi - 1) as nat, phi);
        assert(run_halts(rm_sub, c_sub, phi));
        assert(run(rm_sub, c_sub, (phi - 1) as nat) == run(rm_sub, c_sub, phi));
        //  Assemble the augmented predicate for the witness g_h.
        assert(g_h <= 2 * phi + 1);
        assert(run(m, c, g_h).pc == halted_pc);
        assert(run(m, c, g_h).registers.len() == m.num_regs);
        assert(run(m, c, g_h).pc == halted_pc ==>
            run_halts(rm_sub, c_sub, phi)
            && (forall|r: int| 0 <= r < rm_sub.num_regs as int ==>
                    #[trigger] run(m, c, g_h).registers[(r + reg_offset) as int]
                        == run(rm_sub, c_sub, phi).registers[r]));
        assert(run_halts(rm_sub, c_sub, (phi - 1) as nat) ==> run(m, c, g_h).pc == halted_pc);
        assert(forall|jj: int| 0 <= jj < m.num_regs as int
            && (jj < reg_offset || jj >= reg_offset + rm_sub.num_regs)
            && jj != fuel_reg as int && jj != scratch as int
            ==> #[trigger] run(m, c, g_h).registers[jj] == c.registers[jj]);
    } else {
        lemma_instrument_reaches_sink(rm_sub, m, reg_offset, pc_offset, halted_pc, timeout_pc,
            fuel_reg, scratch, c_sub, c, phi);
        let g_i = choose|g: nat| g <= 2 * phi + 1
            && (run(m, c, g).pc == halted_pc || run(m, c, g).pc == timeout_pc)
            && run(m, c, g).registers.len() == m.num_regs
            && (run(m, c, g).pc == halted_pc ==>
                    run_halts(rm_sub, c_sub, phi)
                    && (forall|r: int| 0 <= r < rm_sub.num_regs as int ==>
                            #[trigger] run(m, c, g).registers[(r + reg_offset) as int]
                                == run(rm_sub, c_sub, phi).registers[r]))
            && (forall|jj: int| 0 <= jj < m.num_regs as int
                    && (jj < reg_offset || jj >= reg_offset + rm_sub.num_regs)
                    && jj != fuel_reg as int && jj != scratch as int
                    ==> #[trigger] run(m, c, g).registers[jj] == c.registers[jj]);
        //  completeness arm vacuous: ¬run_halts(E, phi-1).
        assert(run_halts(rm_sub, c_sub, (phi - 1) as nat) ==> run(m, c, g_i).pc == halted_pc);
    }
}

} //  verus!
