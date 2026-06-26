//! # GAP-2 L1 — M6: the k→2 run simulation and halting equivalence.
//!
//! Chains the M5-dispatch one-step sim (`godel_dispatch::lemma_sim_step`) along a whole run and proves
//! the headline halting equivalence:
//!
//! ```text
//!   (∃F. run_halts(rm_k, c, F))  ⟺  (∃G. run_halts(rm_k_to_rm2(rm_k), rm2_config_enc(instrs, c), G))
//! ```
//!
//! for any well-formed RM(k) `rm_k` and well-formed config `c`. Composing with the B6
//! `tm_run_sim::lemma_rm_tm_origin_iff` (RM(2) halts ⟺ `rm_to_tm` reaches origin) and
//! `tm_h0::lemma_tm_h0_iff` (reaches origin ⟺ `mm_in_H0`) gives RM(k) halts ⟺ `mm_in_H0` — the machine
//! content G2-F wires to discharge `ceer_realizes`.
//!
//! Structure mirrors `tm_run_sim.rs` (forward chains `sim_step`; backward inducts on RM(2) fuel, using
//! the `g ≥ 1` progress of each gadget to bound a `DecJump`-on-zero self-loop). No verifier escape hatches.

use vstd::prelude::*;
use crate::machine::*;
use crate::multi_output_primitives::{mk_inc, mk_dj, mk_jump};
use crate::godel::lemma_base_ge_2;
use crate::godel_assemble::{
    rm_k_to_rm2, rm2_instrs, block_start, block_size, block_instrs, inc_block, decjump_block,
    lemma_block_at_full, lemma_rm2_len, lemma_block_start_step, lemma_block_start_le,
};
use crate::godel_dispatch::{rm2_config_enc, lemma_sim_step};

verus! {

/// Run-composition: `run(m,c,a+b) == run(m, run(m,c,a), b)` (per-module local copy).
proof fn lemma_run_add(m: RegisterMachine, c: Configuration, a: nat, b: nat)
    ensures
        run(m, c, (a + b) as nat) == run(m, run(m, c, a), b),
    decreases a,
{
    if a == 0 {
    } else if is_halted(m, c) {
        lemma_halted_run_identity(m, c, a);
        lemma_halted_run_identity(m, c, (a + b) as nat);
        lemma_halted_run_identity(m, c, b);
    } else {
        let next = step(m, c).unwrap();
        lemma_run_add(m, next, (a - 1) as nat, b);
        assert((a - 1) + b == (a + b) - 1);
    }
}

//  ============================================================
//  Structural facts about the address map.
//  ============================================================

/// Every block has at least one instruction.
pub proof fn lemma_block_size_pos(instr: Instruction)
    ensures
        block_size(instr) >= 1,
{
    match instr {
        Instruction::Inc { register } => { lemma_base_ge_2(register); },
        Instruction::DecJump { register, target } => { lemma_base_ge_2(register); },
        Instruction::Jump { target } => {},
        Instruction::Halt => {},
    }
}

/// `block_start` is strictly monotone (each block has positive size).
pub proof fn lemma_block_start_strict(instrs: Seq<Instruction>, a: nat, b: nat)
    requires
        a < b,
        b <= instrs.len(),
    ensures
        block_start(instrs, a) < block_start(instrs, b),
    decreases b,
{
    lemma_block_start_step(instrs, (b - 1) as nat);          //  block_start(b) == block_start(b-1) + size
    lemma_block_size_pos(instrs[(b - 1) as int]);
    if a == (b - 1) as nat {
    } else {
        lemma_block_start_strict(instrs, a, (b - 1) as nat);
    }
}

//  ============================================================
//  Halted correspondence between an RM(k) config and its RM(2) encoding.
//  ============================================================

/// If the RM(k) config is halted, so is its RM(2) encoding (either the encoding's pc lands at the
/// machine end, or it lands on the compiled `Halt` block head).
pub proof fn lemma_enc_halted_fwd(rm_k: RegisterMachine, c_k: Configuration)
    requires
        machine_wf(rm_k),
        config_wf(rm_k, c_k),
        is_halted(rm_k, c_k),
    ensures
        is_halted(rm_k_to_rm2(rm_k), rm2_config_enc(rm_k.instructions, c_k)),
{
    let instrs = rm_k.instructions;
    let m2 = rm_k_to_rm2(rm_k);
    let enc = rm2_config_enc(instrs, c_k);
    let pc = c_k.pc;
    let start = block_start(instrs, pc);
    reveal(machine_wf);
    lemma_rm2_len(instrs);                                   //  m2.len() == block_start(len)
    crate::tm_run_sim::lemma_rm_terminal_cases(rm_k, c_k);   //  pc==len OR (pc<len && Halt)
    if pc == instrs.len() {
        assert(enc.pc >= m2.instructions.len());            //  start == block_start(len) == m2.len()
    } else {
        assert(pc < instrs.len() && instrs[pc as int] == Instruction::Halt);
        lemma_block_size_pos(instrs[pc as int]);
        lemma_block_at_full(instrs, pc, 0);                 //  m2.instr[start] == block_instrs[0]
        assert(block_instrs(instrs, pc) == seq![Instruction::Halt]);
        assert(m2.instructions[start as int] == Instruction::Halt);
        lemma_block_start_strict(instrs, pc, instrs.len());
    }
}

/// If the RM(k) config is NOT halted, neither is its RM(2) encoding: the encoded pc sits at a real
/// gadget head (`DecJump`/`Jump`), which always steps.
pub proof fn lemma_enc_not_halted(rm_k: RegisterMachine, c_k: Configuration)
    requires
        machine_wf(rm_k),
        config_wf(rm_k, c_k),
        !is_halted(rm_k, c_k),
    ensures
        !is_halted(rm_k_to_rm2(rm_k), rm2_config_enc(rm_k.instructions, c_k)),
{
    let instrs = rm_k.instructions;
    let m2 = rm_k_to_rm2(rm_k);
    let enc = rm2_config_enc(instrs, c_k);
    let pc = c_k.pc;
    let start = block_start(instrs, pc);
    reveal(machine_wf);
    //  !is_halted ⟹ step Some ⟹ pc < len ∧ instr ≠ Halt.
    assert(step(rm_k, c_k) is Some);
    assert(pc < instrs.len());
    assert(instrs[pc as int] !== Instruction::Halt);
    lemma_rm2_len(instrs);
    lemma_block_start_strict(instrs, pc, instrs.len());      //  start < m2.len()
    lemma_block_size_pos(instrs[pc as int]);
    lemma_block_at_full(instrs, pc, 0);                     //  m2.instr[start] == block_instrs[0]
    assert(enc.registers.len() == 2);
    match instrs[pc as int] {
        Instruction::Inc { register } => {
            assert(block_instrs(instrs, pc) == inc_block(register, start));
            assert(m2.instructions[start as int] == mk_dj(0, start + 3));
        },
        Instruction::DecJump { register, target } => {
            assert(block_instrs(instrs, pc) == decjump_block(register, start, block_start(instrs, target)));
            assert(m2.instructions[start as int] == mk_dj(0, start + 3));
        },
        Instruction::Jump { target } => {
            assert(block_instrs(instrs, pc) == seq![mk_jump(block_start(instrs, target))]);
            assert(m2.instructions[start as int] == mk_jump(block_start(instrs, target)));
        },
        Instruction::Halt => {
            assert(false);
        },
    }
    assert(step(m2, enc) is Some);
}

//  ============================================================
//  Forward: chain the simulation along the run.
//  ============================================================

/// **The run simulation.** If `rm_k` halts within `F` steps from `c`, the RM(2) machine runs from
/// `enc(c)` to `enc(run(rm_k, c, F))` (the halted config), by chaining `lemma_sim_step`.
pub proof fn lemma_sim_run(rm_k: RegisterMachine, c_k: Configuration, f: nat)
    requires
        machine_wf(rm_k),
        config_wf(rm_k, c_k),
        run_halts(rm_k, c_k, f),
    ensures
        exists|g: nat|
            run(rm_k_to_rm2(rm_k), rm2_config_enc(rm_k.instructions, c_k), g)
                == rm2_config_enc(rm_k.instructions, run(rm_k, c_k, f)),
    decreases f,
{
    let instrs = rm_k.instructions;
    let m2 = rm_k_to_rm2(rm_k);
    let enc = rm2_config_enc(instrs, c_k);
    if f == 0 {
        assert(run(rm_k, c_k, 0) == c_k);
        assert(run(m2, enc, 0) == enc);
    } else if is_halted(rm_k, c_k) {
        lemma_halted_run_identity(rm_k, c_k, f);            //  run(c,f) == c
        assert(run(m2, enc, 0) == enc);
    } else {
        let next = step(rm_k, c_k).unwrap();
        assert(step(rm_k, c_k) is Some);
        lemma_sim_step(rm_k, c_k);                          //  ∃g0. run(m2, enc, g0) == enc(next)
        let g0 = choose|g0: nat|
            1 <= g0 && run(m2, enc, g0) == rm2_config_enc(instrs, next);
        crate::machine::lemma_step_preserves_config_wf(rm_k, c_k);   //  config_wf(next)
        assert(run_halts(rm_k, next, (f - 1) as nat));      //  not halted ⟹ Some-branch
        lemma_sim_run(rm_k, next, (f - 1) as nat);          //  ∃g1. run(m2, enc(next), g1) == enc(run(next,f-1))
        let g1 = choose|g1: nat|
            run(m2, rm2_config_enc(instrs, next), g1) == rm2_config_enc(instrs, run(rm_k, next, (f - 1) as nat));
        assert(run(rm_k, c_k, f) == run(rm_k, next, (f - 1) as nat));
        lemma_run_add(m2, enc, g0, g1);                     //  run(m2, enc, g0+g1) == run(m2, run(m2,enc,g0), g1)
        assert(run(m2, enc, (g0 + g1) as nat)
            == rm2_config_enc(instrs, run(rm_k, c_k, f)));
    }
}

/// **Forward halting.** If `rm_k` halts from `c`, the RM(2) machine halts from `enc(c)`.
pub proof fn lemma_godel_fwd(rm_k: RegisterMachine, c_k: Configuration)
    requires
        machine_wf(rm_k),
        config_wf(rm_k, c_k),
        exists|f: nat| run_halts(rm_k, c_k, f),
    ensures
        exists|g: nat| run_halts(rm_k_to_rm2(rm_k), rm2_config_enc(rm_k.instructions, c_k), g),
{
    let instrs = rm_k.instructions;
    let m2 = rm_k_to_rm2(rm_k);
    let enc = rm2_config_enc(instrs, c_k);
    let f = choose|f: nat| run_halts(rm_k, c_k, f);
    let c_halt = run(rm_k, c_k, f);
    crate::tm_run_sim::lemma_run_halts_is_halted(rm_k, c_k, f);         //  is_halted(rm_k, c_halt)
    crate::multi_output_primitives::lemma_run_preserves_config_wf(rm_k, c_k, f);   //  config_wf(c_halt)
    lemma_sim_run(rm_k, c_k, f);                            //  ∃g0. run(m2, enc, g0) == enc(c_halt)
    let g0 = choose|g0: nat|
        run(m2, enc, g0) == rm2_config_enc(instrs, c_halt);
    lemma_enc_halted_fwd(rm_k, c_halt);                     //  is_halted(m2, enc(c_halt))
    assert(is_halted(m2, run(m2, enc, g0)));
    crate::multi_output_primitives::lemma_halted_at_end_run_halts(m2, enc, g0);    //  run_halts(m2, enc, g0)
}

//  ============================================================
//  Backward: RM(2) halts ⟹ RM(k) halts (induct on RM(2) fuel, using g ≥ 1 progress).
//  ============================================================

/// **Backward halting.** If the RM(2) machine is halted at `run(m2, enc(c), G)`, then `rm_k` halts from
/// `c`. Induction on `G`: bottom out when `rm_k` is already halted; otherwise peel `g ≥ 1` RM(2) steps
/// of the gadget simulating the next RM(k) step and recurse (the `g ≥ 1` is what bounds the recursion).
pub proof fn lemma_godel_bwd(rm_k: RegisterMachine, c_k: Configuration, g: nat)
    requires
        machine_wf(rm_k),
        config_wf(rm_k, c_k),
        is_halted(rm_k_to_rm2(rm_k), run(rm_k_to_rm2(rm_k), rm2_config_enc(rm_k.instructions, c_k), g)),
    ensures
        exists|f: nat| run_halts(rm_k, c_k, f),
    decreases g,
{
    let instrs = rm_k.instructions;
    let m2 = rm_k_to_rm2(rm_k);
    let enc = rm2_config_enc(instrs, c_k);
    if is_halted(rm_k, c_k) {
        assert(run_halts(rm_k, c_k, 0));
    } else {
        let next = step(rm_k, c_k).unwrap();
        assert(step(rm_k, c_k) is Some);
        let enc_next = rm2_config_enc(instrs, next);
        crate::machine::lemma_step_preserves_config_wf(rm_k, c_k);   //  config_wf(next)
        lemma_sim_step(rm_k, c_k);                          //  ∃g0. 1<=g0 && run(m2,enc,g0) == enc_next
        let g0 = choose|g0: nat| 1 <= g0 && run(m2, enc, g0) == enc_next;
        assert(1 <= g0 && run(m2, enc, g0) == enc_next);
        if g0 <= g {
            //  peel g0: run(m2, enc_next, g-g0) == run(m2, enc, g), which is halted.
            lemma_run_add(m2, enc, g0, (g - g0) as nat);
            assert((g0 + (g - g0)) as nat == g);
            assert(run(m2, enc_next, (g - g0) as nat) == run(m2, enc, g));
            lemma_godel_bwd(rm_k, next, (g - g0) as nat);   //  ∃f1. run_halts(next, f1)  [g-g0 < g]
            let f1 = choose|f1: nat| run_halts(rm_k, next, f1);
            assert(run_halts(rm_k, next, f1));
            assert(((f1 + 1) - 1) as nat == f1);
            assert(run_halts(rm_k, c_k, (f1 + 1) as nat));
        } else {
            //  g < g0: run(m2, enc, g0) idles after the (halted) step g, so enc_next is halted.
            lemma_run_add(m2, enc, g, (g0 - g) as nat);
            assert((g + (g0 - g)) as nat == g0);
            lemma_halted_run_identity(m2, run(m2, enc, g), (g0 - g) as nat);
            assert(run(m2, enc, g0) == run(m2, enc, g));
            assert(is_halted(m2, enc_next));
            //  enc_next halted ⟹ next halted (contrapositive of lemma_enc_not_halted).
            if !is_halted(rm_k, next) {
                lemma_enc_not_halted(rm_k, next);
                assert(false);
            }
            assert(is_halted(rm_k, next));
            assert(run_halts(rm_k, next, 0));
            assert(run_halts(rm_k, c_k, 1));
        }
    }
}

//  ============================================================
//  The M6 headline iff.
//  ============================================================

/// **M6 — RM(k) halting ⟺ the assembled RM(2) machine halts.** For a well-formed `rm_k` and config `c`,
/// `rm_k` halts from `c` iff `rm_k_to_rm2(rm_k)` halts from `rm2_config_enc(c)`. Composing with
/// `tm_run_sim::lemma_rm_tm_origin_iff` and `tm_h0::lemma_tm_h0_iff` realizes `rm_k`'s halting set as
/// `H₀` — the machine content of `ceer_realizes` (G2-F).
pub proof fn lemma_godel_halts_iff(rm_k: RegisterMachine, c_k: Configuration)
    requires
        machine_wf(rm_k),
        config_wf(rm_k, c_k),
    ensures
        (exists|f: nat| run_halts(rm_k, c_k, f))
            <==> (exists|g: nat| run_halts(rm_k_to_rm2(rm_k), rm2_config_enc(rm_k.instructions, c_k), g)),
{
    let instrs = rm_k.instructions;
    let m2 = rm_k_to_rm2(rm_k);
    let enc = rm2_config_enc(instrs, c_k);
    if exists|f: nat| run_halts(rm_k, c_k, f) {
        lemma_godel_fwd(rm_k, c_k);
    }
    if exists|g: nat| run_halts(m2, enc, g) {
        let g = choose|g: nat| run_halts(m2, enc, g);
        crate::tm_run_sim::lemma_run_halts_is_halted(m2, enc, g);   //  is_halted(m2, run(m2, enc, g))
        lemma_godel_bwd(rm_k, c_k, g);
    }
}

} //  verus!
