//! # GAP-2 L1 — M5-dispatch: the one-step k→2 simulation.
//!
//! Wraps the M5 per-instruction sims (`godel_sim.rs`) with the M4 layout extraction
//! (`godel_assemble.rs`) into a single one-step lemma: ONE non-halting RM(k) step is simulated by a
//! run of the assembled RM(2) machine, under the encoding
//!
//! ```text
//!   rm2_config_enc(instrs, c_k) = Configuration { pc: block_start(instrs, c_k.pc),
//!                                                  registers: [godel_encode(c_k.registers), 0] }.
//! ```
//!
//! `lemma_sim_step` dispatches on the RM(k) instruction at `c_k.pc` (Inc / DecJump / Jump), picks the
//! matching sim, and shows the resulting RM(2) config is exactly the encoding of the stepped RM(k)
//! config. The `Halt` (and run-off-the-end) cases are the M6 halting connection, handled there. No
//! verifier escape hatches.

use vstd::prelude::*;
use crate::machine::*;
use crate::multi_output_primitives::{mk_inc, mk_dj, mk_jump};
use crate::godel::godel_encode;
use crate::godel_assemble::{
    rm_k_to_rm2, rm2_instrs, block_start, block_size,
    lemma_inc_block_layout, lemma_decjump_block_layout, lemma_jump_block_layout, lemma_rm2_len,
};
use crate::godel_sim::{lemma_inc_sim, lemma_decjump_sim, lemma_jump_sim};

verus! {

/// The RM(2) configuration encoding an RM(k) configuration: pc through the block-address map, registers
/// `[C1 = godel_encode(regs), C2 = 0]`.
pub open spec fn rm2_config_enc(instrs: Seq<Instruction>, c_k: Configuration) -> Configuration {
    Configuration {
        pc: block_start(instrs, c_k.pc),
        registers: seq![godel_encode(c_k.registers), 0nat],
    }
}

/// **The one-step k→2 simulation.** From a well-formed RM(k) config `c_k` whose instruction is a
/// non-halt (Inc/DecJump/Jump), the assembled RM(2) machine runs from `rm2_config_enc(c_k)` to
/// `rm2_config_enc(step(c_k))` in some number of steps.
pub proof fn lemma_sim_step(rm_k: RegisterMachine, c_k: Configuration)
    requires
        machine_wf(rm_k),
        config_wf(rm_k, c_k),
        c_k.pc < rm_k.instructions.len(),
        rm_k.instructions[c_k.pc as int] !== Instruction::Halt,
    ensures
        exists|g: nat|
            run(rm_k_to_rm2(rm_k), rm2_config_enc(rm_k.instructions, c_k), g)
                == rm2_config_enc(rm_k.instructions, step(rm_k, c_k).unwrap()),
{
    let instrs = rm_k.instructions;
    let m2 = rm_k_to_rm2(rm_k);
    let pc = c_k.pc;
    let regs = c_k.registers;
    let enc = rm2_config_enc(instrs, c_k);
    let start = block_start(instrs, pc);
    reveal(machine_wf);
    assert(m2.instructions == rm2_instrs(instrs));
    assert(m2.num_regs == 2);
    assert(enc.pc == start);
    assert(enc.registers.len() == 2);
    assert(enc.registers[0] == godel_encode(regs));
    assert(enc.registers[1] == 0);

    match instrs[pc as int] {
        Instruction::Inc { register } => {
            let i = register;
            assert(i < rm_k.num_regs);          //  from machine_wf
            assert(regs.len() == rm_k.num_regs); //  config_wf
            lemma_inc_block_layout(instrs, pc, i);
            lemma_inc_sim(m2, enc, regs, i, start);
            let g = choose|g: nat|
                run(m2, enc, g).pc == start + crate::godel::base(i) + 5
                && run(m2, enc, g).registers[0] == godel_encode(regs.update(i as int, (regs[i as int] + 1) as nat))
                && run(m2, enc, g).registers[1] == 0
                && run(m2, enc, g).registers.len() == 2;
            let result = run(m2, enc, g);
            let stepped = step(rm_k, c_k).unwrap();
            let enc_step = rm2_config_enc(instrs, stepped);
            //  stepped.pc == pc + 1, stepped.registers == regs.update(i, regs[i]+1).
            assert(stepped.pc == pc + 1);
            assert(stepped.registers == regs.update(i as int, (regs[i as int] + 1) as nat));
            //  enc_step.pc == block_start(pc+1) == start + base(i) + 5 (block_size of Inc).
            crate::godel_assemble::lemma_block_start_step(instrs, pc);
            assert(block_size(instrs[pc as int]) == crate::godel::base(i) + 5);
            assert(enc_step.pc == start + crate::godel::base(i) + 5);
            assert(result.pc == enc_step.pc);
            assert(result.registers =~= enc_step.registers);
            assert(result == enc_step);
        },
        Instruction::DecJump { register, target } => {
            let i = register;
            let t = target;
            assert(i < rm_k.num_regs);
            assert(regs.len() == rm_k.num_regs);
            let target_block = block_start(instrs, t);
            lemma_decjump_block_layout(instrs, pc, i, t);
            lemma_decjump_sim(m2, enc, regs, i, start, target_block);
            let g = choose|g: nat|
                run(m2, enc, g).registers.len() == 2
                && run(m2, enc, g).registers[1] == 0
                && (if regs[i as int] >= 1 {
                        run(m2, enc, g).pc == start + 3 * crate::godel::base(i) + 10
                        && run(m2, enc, g).registers[0] == godel_encode(regs.update(i as int, (regs[i as int] - 1) as nat))
                    } else {
                        run(m2, enc, g).pc == target_block
                        && run(m2, enc, g).registers[0] == godel_encode(regs)
                    });
            let result = run(m2, enc, g);
            let stepped = step(rm_k, c_k).unwrap();
            let enc_step = rm2_config_enc(instrs, stepped);
            crate::godel_assemble::lemma_block_start_step(instrs, pc);
            assert(block_size(instrs[pc as int]) == 3 * crate::godel::base(i) + 10);
            if regs[i as int] >= 1 {
                //  RM(k): decrement, pc -> pc+1.  enc_step.pc == block_start(pc+1) == start + 3k + 10.
                assert(regs[i as int] > 0);
                assert(stepped.pc == pc + 1);
                assert(stepped.registers == regs.update(i as int, (regs[i as int] - 1) as nat));
                assert(enc_step.pc == start + 3 * crate::godel::base(i) + 10);
                assert(result.pc == enc_step.pc);
                assert(result.registers =~= enc_step.registers);
                assert(result == enc_step);
            } else {
                //  RM(k): pc -> t, registers unchanged.  enc_step.pc == block_start(t) == target_block.
                assert(regs[i as int] == 0);
                assert(stepped.pc == t);
                assert(stepped.registers == regs);
                assert(enc_step.pc == target_block);
                assert(result.pc == enc_step.pc);
                assert(result.registers =~= enc_step.registers);
                assert(result == enc_step);
            }
        },
        Instruction::Jump { target } => {
            let t = target;
            let target_block = block_start(instrs, t);
            lemma_jump_block_layout(instrs, pc, t);
            lemma_jump_sim(m2, enc, start, target_block);
            let result = run(m2, enc, 1);
            let stepped = step(rm_k, c_k).unwrap();
            let enc_step = rm2_config_enc(instrs, stepped);
            assert(stepped.pc == t);
            assert(stepped.registers == regs);
            assert(enc_step.pc == target_block);
            assert(result.pc == enc_step.pc);
            assert(result.registers =~= enc_step.registers);
            assert(result == enc_step);
        },
        Instruction::Halt => {
            assert(false);
        },
    }
}

} //  verus!
