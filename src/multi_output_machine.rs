use vstd::prelude::*;
use crate::machine::*;
use crate::conditional_halt::{lemma_run_split, lemma_run_halts_split};
use crate::multi_output_primitives::*;

verus! {

//  ============================================================
//  Combined machine construction
//  ============================================================

///  Register layout:
///    reg 0: output 0 (also initial input)
///    reg 1: output 1
///    reg 2: output 2
///    reg 3: scratch (always 0)
///    reg 4 .. 4+N_h-1: bank for rm_halts
///    reg 4+N_h .. 4+N_h+N_1-1: bank for rm_out1
///    reg 4+N_h+N_1 .. 4+N_h+N_1+N_2-1: bank for rm_out2

pub open spec fn build_multi_output(
    rm_h: RegisterMachine,
    rm_1: RegisterMachine,
    rm_2: RegisterMachine,
) -> RegisterMachine {
    let n_h = rm_h.instructions.len();
    let n_1 = rm_1.instructions.len();
    let n_2 = rm_2.instructions.len();
    let bh: nat = 4;
    let b1: nat = 4 + rm_h.num_regs;
    let b2: nat = 4 + rm_h.num_regs + rm_1.num_regs;
    let scratch: nat = 3;
    let nr = 4 + rm_h.num_regs + rm_1.num_regs + rm_2.num_regs;

    //  PC layout: [dist(5)] [embed_h(n_h)] [copy_h(3)] [embed_1(n_1)]
    //             [copy_1(3)] [embed_2(n_2)] [copy_2(3)] [Halt(1)]
    let p0: nat = 0;                            //  triple distribute
    let p1: nat = 5;                            //  embedded rm_h
    let p2: nat = 5 + n_h;                      //  copy bank_h[0] → reg 0
    let p3: nat = 8 + n_h;                      //  embedded rm_1
    let p4: nat = 8 + n_h + n_1;                //  copy bank_1[0] → reg 1
    let p5: nat = 11 + n_h + n_1;               //  embedded rm_2
    let p6: nat = 11 + n_h + n_1 + n_2;         //  copy bank_2[0] → reg 2
    let p7: nat = 14 + n_h + n_1 + n_2;         //  Halt

    RegisterMachine {
        instructions:
            triple_dist_instrs(0, bh, b1, b2, scratch, p0)
            + embed_instructions(rm_h.instructions, bh, p1, p2, scratch)
            + copy_instrs(bh, 0, scratch, p2)
            + embed_instructions(rm_1.instructions, b1, p3, p4, scratch)
            + copy_instrs(b1, 1, scratch, p4)
            + embed_instructions(rm_2.instructions, b2, p5, p6, scratch)
            + copy_instrs(b2, 2, scratch, p6)
            + seq![Instruction::Halt],
        num_regs: nr,
    }
}

//  ============================================================
//  Well-formedness of the combined machine
//  ============================================================

proof fn lemma_build_multi_output_wf(
    rm_h: RegisterMachine,
    rm_1: RegisterMachine,
    rm_2: RegisterMachine,
)
    requires
        machine_wf(rm_h),
        machine_wf(rm_1),
        machine_wf(rm_2),
    ensures
        machine_wf(build_multi_output(rm_h, rm_1, rm_2)),
        build_multi_output(rm_h, rm_1, rm_2).num_regs >= 3,
{
    reveal(machine_wf);
    let m = build_multi_output(rm_h, rm_1, rm_2);
    let n_h = rm_h.instructions.len();
    let n_1 = rm_1.instructions.len();
    let n_2 = rm_2.instructions.len();
    let bh: nat = 4;
    let b1: nat = 4 + rm_h.num_regs;
    let b2: nat = 4 + rm_h.num_regs + rm_1.num_regs;
    let scratch: nat = 3;
    let nr = m.num_regs;
    let tl = m.instructions.len();
    let p1: nat = 5;
    let p2: nat = 5 + n_h;
    let p3: nat = 8 + n_h;
    let p4: nat = 8 + n_h + n_1;
    let p5: nat = 11 + n_h + n_1;
    let p6: nat = 11 + n_h + n_1 + n_2;
    let p7: nat = 14 + n_h + n_1 + n_2;
    assert(tl == p7 + 1);

    assert forall|i: int| #![trigger m.instructions[i]]
        0 <= i < tl as int
    implies match m.instructions[i] {
        Instruction::Inc { register } => register < nr,
        Instruction::DecJump { register, target } =>
            register < nr && target <= tl,
        Instruction::Halt => true,
    } by {
        //  Each region: identify the instruction and check bounds
        if i < p1 as int {
        } else if i < p2 as int {
        } else if i < p3 as int {
        } else if i < p4 as int {
        } else if i < p5 as int {
        } else if i < p6 as int {
        } else if i < p7 as int {
        } else {
        }
    };
}

//  ============================================================
//  Per-input proof: chain all phases
//  ============================================================

#[verifier::rlimit(40)]
proof fn lemma_multi_output_for_input(
    rm_h: RegisterMachine,
    rm_1: RegisterMachine,
    rm_2: RegisterMachine,
    f_h: spec_fn(nat) -> nat,
    f_1: spec_fn(nat) -> nat,
    f_2: spec_fn(nat) -> nat,
    s: nat,
)
    requires
        machine_wf(rm_h) &&
        (forall|s: nat| halts(rm_h, s)) &&
        (forall|s: nat| output(rm_h, s) == f_h(s)),
        machine_wf(rm_1) &&
        (forall|s: nat| halts(rm_1, s)) &&
        (forall|s: nat| output(rm_1, s) == f_1(s)),
        machine_wf(rm_2) &&
        (forall|s: nat| halts(rm_2, s)) &&
        (forall|s: nat| output(rm_2, s) == f_2(s)),
    ensures ({
        let m = build_multi_output(rm_h, rm_1, rm_2);
        let init = initial_config(m, s);
        exists|total_fuel: nat|
            run_halts(m, init, total_fuel) &&
            run(m, init, total_fuel).registers[0] == f_h(s) &&
            run(m, init, total_fuel).registers[1] == f_1(s) &&
            run(m, init, total_fuel).registers[2] == f_2(s)
    }),
{
    reveal(machine_wf);
    let m = build_multi_output(rm_h, rm_1, rm_2);
    let init = initial_config(m, s);
    let bh: nat = 4;
    let b1: nat = 4 + rm_h.num_regs;
    let b2: nat = 4 + rm_h.num_regs + rm_1.num_regs;
    let scratch: nat = 3;
    let n_h = rm_h.instructions.len();
    let n_1 = rm_1.instructions.len();
    let n_2 = rm_2.instructions.len();
    let p1: nat = 5;
    let p2: nat = 5 + n_h;
    let p3: nat = 8 + n_h;
    let p4: nat = 8 + n_h + n_1;
    let p5: nat = 11 + n_h + n_1;
    let p6: nat = 11 + n_h + n_1 + n_2;
    let p7: nat = 14 + n_h + n_1 + n_2;

    //  ========================================
    //  Phase 0: triple distribute (fuel: 5*s + 1)
    //  ========================================
    assert(m.instructions[0] == mk_dj(0, 5));
    assert(m.instructions[1] == mk_inc(bh));
    assert(m.instructions[2] == mk_inc(b1));
    assert(m.instructions[3] == mk_inc(b2));
    assert(m.instructions[4] == mk_dj(scratch, 0));
    lemma_triple_dist_inner(m, init, 0, bh, b1, b2, scratch, 0, s, 0, s);
    let f0: nat = 5 * s + 1;
    let c0 = run(m, init, f0);
    assert(c0.pc == p1);
    assert(c0.registers[bh as int] == s);
    assert(c0.registers[scratch as int] == 0);

    //  ========================================
    //  Phase 1: embedded rm_halts (fuel: g1 from embed_reaches_target)
    //  ========================================
    let init_h = initial_config(rm_h, s);
    assert(init_h.registers.len() == rm_h.num_regs);
    assert forall|r: int| 0 <= r < rm_h.num_regs as int implies
        c0.registers[(r + bh) as int] == init_h.registers[r]
    by {
        if r == 0 {
            assert(c0.registers[bh as int] == s);
            assert(init_h.registers[0] == s);
        } else {
            let idx = (r + bh) as int;
            assert(idx != 0 as int);
            assert(idx != bh as int);
            assert(idx < b1 as int);
            assert(idx != b1 as int);
            assert(idx != b2 as int);
            //  triple_dist guarantees unchanged for this idx
            assert(c0.registers[idx] == init.registers[idx]);
            //  init has 0 at all positions > 0
            assert(init.registers[idx] == 0);
            //  init_h has 0 at all positions > 0
            assert(init_h.registers[r] == 0);
        }
    };
    assert(c0.registers[scratch as int] == 0);
    assert(embed_configs_agree(rm_h, bh, p1, scratch, init_h, c0));

    //  Instruction matching for embedded rm_h
    assert forall|i: int| 0 <= i < n_h as int implies
        m.instructions[(i + p1) as int] ==
            embed_instructions(rm_h.instructions, bh, p1, p2, scratch)[i]
    by {};

    //  rm_h halts on s
    let fuel_h: nat = choose|f: nat| run_halts(rm_h, init_h, f);
    lemma_embed_reaches_target(rm_h, m, bh, p1, p2, scratch, init_h, c0, fuel_h);

    let halt_h = run(rm_h, init_h, fuel_h);
    let g1: nat = choose|g: nat| g <= fuel_h + 1 &&
        run(m, c0, g).pc == p2 &&
        (forall|r: int| 0 <= r < rm_h.num_regs as int ==>
            run(m, c0, g).registers[(r + bh) as int] == halt_h.registers[r]) &&
        run(m, c0, g).registers[scratch as int] == 0 &&
        run(m, c0, g).registers.len() == m.num_regs;
    let c1 = run(m, c0, g1);
    assert(c1.pc == p2);
    //  c1.registers[bh] == halt_h.registers[0] == output(rm_h, s) == f_h(s)
    assert(c1.registers[bh as int] == f_h(s));

    //  ========================================
    //  Phase 2: copy bank_h[0] → reg 0 (fuel: 3*f_h(s) + 1)
    //  ========================================
    assert(m.instructions[p2 as int] == mk_dj(bh, p2 + 3));
    assert(m.instructions[(p2 + 1) as int] == mk_inc(0));
    assert(m.instructions[(p2 + 2) as int] == mk_dj(scratch, p2));
    assert(c1.registers[0] == 0) by {
        //  reg 0 was zeroed by Phase 0, not touched by Phase 1 (Phase 1 only touches bh..bh+N_h)
        //  Phase 0 zeroed reg 0, Phase 1 operates at reg_offset = bh = 4, so reg 0 untouched
    };
    lemma_copy_loop_inner(m, c1, bh, 0, scratch, p2, f_h(s), 0, f_h(s));
    let f2: nat = 3 * f_h(s) + 1;
    let c2 = run(m, c1, f2);
    assert(c2.pc == p3);
    assert(c2.registers[0] == f_h(s));

    //  ========================================
    //  Phase 3: embedded rm_out1
    //  ========================================
    let init_1 = initial_config(rm_1, s);
    assert forall|r: int| 0 <= r < rm_1.num_regs as int implies
        c2.registers[(r + b1) as int] == init_1.registers[r]
    by {};
    assert(embed_configs_agree(rm_1, b1, p3, scratch, init_1, c2));
    assert forall|i: int| 0 <= i < n_1 as int implies
        m.instructions[(i + p3) as int] ==
            embed_instructions(rm_1.instructions, b1, p3, p4, scratch)[i]
    by {};
    let fuel_1: nat = choose|f: nat| run_halts(rm_1, init_1, f);
    lemma_embed_reaches_target(rm_1, m, b1, p3, p4, scratch, init_1, c2, fuel_1);
    let halt_1 = run(rm_1, init_1, fuel_1);
    let g3: nat = choose|g: nat| g <= fuel_1 + 1 &&
        run(m, c2, g).pc == p4 &&
        (forall|r: int| 0 <= r < rm_1.num_regs as int ==>
            run(m, c2, g).registers[(r + b1) as int] == halt_1.registers[r]) &&
        run(m, c2, g).registers[scratch as int] == 0 &&
        run(m, c2, g).registers.len() == m.num_regs;
    let c3 = run(m, c2, g3);
    assert(c3.registers[b1 as int] == f_1(s));
    assert(c3.registers[0] == f_h(s)); //  preserved from Phase 2

    //  ========================================
    //  Phase 4: copy bank_1[0] → reg 1
    //  ========================================
    assert(m.instructions[p4 as int] == mk_dj(b1, p4 + 3));
    assert(m.instructions[(p4 + 1) as int] == mk_inc(1));
    assert(m.instructions[(p4 + 2) as int] == mk_dj(scratch, p4));
    lemma_copy_loop_inner(m, c3, b1, 1, scratch, p4, f_1(s), 0, f_1(s));
    let f4: nat = 3 * f_1(s) + 1;
    let c4 = run(m, c3, f4);
    assert(c4.registers[1] == f_1(s));
    assert(c4.registers[0] == f_h(s)); //  preserved

    //  ========================================
    //  Phase 5: embedded rm_out2
    //  ========================================
    let init_2 = initial_config(rm_2, s);
    assert forall|r: int| 0 <= r < rm_2.num_regs as int implies
        c4.registers[(r + b2) as int] == init_2.registers[r]
    by {};
    assert(embed_configs_agree(rm_2, b2, p5, scratch, init_2, c4));
    assert forall|i: int| 0 <= i < n_2 as int implies
        m.instructions[(i + p5) as int] ==
            embed_instructions(rm_2.instructions, b2, p5, p6, scratch)[i]
    by {};
    let fuel_2: nat = choose|f: nat| run_halts(rm_2, init_2, f);
    lemma_embed_reaches_target(rm_2, m, b2, p5, p6, scratch, init_2, c4, fuel_2);
    let halt_2 = run(rm_2, init_2, fuel_2);
    let g5: nat = choose|g: nat| g <= fuel_2 + 1 &&
        run(m, c4, g).pc == p6 &&
        (forall|r: int| 0 <= r < rm_2.num_regs as int ==>
            run(m, c4, g).registers[(r + b2) as int] == halt_2.registers[r]) &&
        run(m, c4, g).registers[scratch as int] == 0 &&
        run(m, c4, g).registers.len() == m.num_regs;
    let c5 = run(m, c4, g5);
    assert(c5.registers[b2 as int] == f_2(s));
    assert(c5.registers[0] == f_h(s)); //  preserved
    assert(c5.registers[1] == f_1(s)); //  preserved

    //  ========================================
    //  Phase 6: copy bank_2[0] → reg 2
    //  ========================================
    assert(m.instructions[p6 as int] == mk_dj(b2, p6 + 3));
    assert(m.instructions[(p6 + 1) as int] == mk_inc(2));
    assert(m.instructions[(p6 + 2) as int] == mk_dj(scratch, p6));
    lemma_copy_loop_inner(m, c5, b2, 2, scratch, p6, f_2(s), 0, f_2(s));
    let f6: nat = 3 * f_2(s) + 1;
    let c6 = run(m, c5, f6);
    assert(c6.registers[2] == f_2(s));
    assert(c6.registers[0] == f_h(s)); //  preserved
    assert(c6.registers[1] == f_1(s)); //  preserved

    //  ========================================
    //  Phase 7: Halt — one more step
    //  ========================================
    assert(c6.pc == p7);
    assert(m.instructions[p7 as int] is Halt);
    assert(is_halted(m, c6));
    //  run_halts(m, c6, 0)
    assert(run_halts(m, c6, 0));
    assert(run(m, c6, 0) == c6);

    //  ========================================
    //  Fuel composition: chain all phases from init to c6
    //  ========================================
    assert(!is_halted(m, c0));
    lemma_not_halted_means_not_run_halts(m, init, f0);
    assert(!is_halted(m, c1)); //  c1.pc == p2, instruction is copy (DecJump)
    assert(!is_halted(m, c2)); //  c2.pc == p3, instruction is embedded
    assert(!is_halted(m, c3)); //  c3.pc == p4, instruction is copy
    assert(!is_halted(m, c4)); //  c4.pc == p5, instruction is embedded
    assert(!is_halted(m, c5)); //  c5.pc == p6, instruction is copy

    assert(run_halts(m, c5, f6));

    //  Phase 5→6: run_halts(m, c5, f6) — established above.
    //  Phase 4→5→6:
    if g5 > 0 {
        lemma_not_halted_means_not_run_halts(m, c4, (g5 - 1) as nat);
        lemma_run_halts_split(m, c4, (g5 - 1) as nat, f6);
    }
    let f56: nat = g5 + f6;
    assert(run_halts(m, c4, f56));

    //  Phase 3→4→5→6:
    if f4 > 0 {
        lemma_not_halted_means_not_run_halts(m, c3, (f4 - 1) as nat);
        lemma_run_halts_split(m, c3, (f4 - 1) as nat, f56);
    }
    let f46: nat = f4 + f56;
    assert(run_halts(m, c3, f46));

    //  Phase 2→3→4→5→6:
    if g3 > 0 {
        lemma_not_halted_means_not_run_halts(m, c2, (g3 - 1) as nat);
        lemma_run_halts_split(m, c2, (g3 - 1) as nat, f46);
    }
    let f36: nat = g3 + f46;
    assert(run_halts(m, c2, f36));

    //  Phase 1→2→...→6:
    if f2 > 0 {
        lemma_not_halted_means_not_run_halts(m, c1, (f2 - 1) as nat);
        lemma_run_halts_split(m, c1, (f2 - 1) as nat, f36);
    }
    let f26: nat = f2 + f36;
    assert(run_halts(m, c1, f26));

    //  Phase 0→1→...→6:
    if g1 > 0 {
        lemma_not_halted_means_not_run_halts(m, c0, (g1 - 1) as nat);
        lemma_run_halts_split(m, c0, (g1 - 1) as nat, f26);
    }
    let f16: nat = g1 + f26;
    assert(run_halts(m, c0, f16));

    //  init→0→1→...→6:
    lemma_not_halted_means_not_run_halts(m, init, (f0 - 1) as nat);
    lemma_run_halts_split(m, init, (f0 - 1) as nat, f16);
    let total: nat = f0 + f16;
    assert(run_halts(m, init, total));

    //  Register correctness: run(m, init, total) == c6 (by determinism + all the runs)
    //  Use lemma_run_split to compose: run(m, init, total) goes through the phases
    lemma_run_split(m, init, (f0 - 1) as nat, f16);
    //  run(m, init, f0 + f16) == run(m, run(m, init, f0), f16) == run(m, c0, f16)
    if g1 > 0 {
        lemma_run_split(m, c0, (g1 - 1) as nat, f26);
    }
    if f2 > 0 {
        lemma_run_split(m, c1, (f2 - 1) as nat, f36);
    }
    if g3 > 0 {
        lemma_run_split(m, c2, (g3 - 1) as nat, f46);
    }
    if f4 > 0 {
        lemma_run_split(m, c3, (f4 - 1) as nat, f56);
    }
    if g5 > 0 {
        lemma_run_split(m, c4, (g5 - 1) as nat, f6);
    }
    //  Now: run(m, init, total) should equal c6
    lemma_halted_run_identity(m, c6, 0);
    assert(run(m, init, total).registers[0] == f_h(s));
    assert(run(m, init, total).registers[1] == f_1(s));
    assert(run(m, init, total).registers[2] == f_2(s));
}

//  ============================================================
//  Main proof
//  ============================================================

pub proof fn lemma_total_multi_output_machine(
    rm_halts: RegisterMachine,
    rm_out1: RegisterMachine,
    rm_out2: RegisterMachine,
    f_h: spec_fn(nat) -> nat,
    f_1: spec_fn(nat) -> nat,
    f_2: spec_fn(nat) -> nat,
)
    requires
        machine_wf(rm_halts) &&
        (forall|s: nat| halts(rm_halts, s)) &&
        (forall|s: nat| output(rm_halts, s) == f_h(s)),
        machine_wf(rm_out1) &&
        (forall|s: nat| halts(rm_out1, s)) &&
        (forall|s: nat| output(rm_out1, s) == f_1(s)),
        machine_wf(rm_out2) &&
        (forall|s: nat| halts(rm_out2, s)) &&
        (forall|s: nat| output(rm_out2, s) == f_2(s)),
    ensures
        exists|rm: RegisterMachine|
            machine_wf(rm) && rm.num_regs >= 3 &&
            (forall|s: nat| halts(rm, s)) &&
            (forall|s: nat, fuel: nat|
                run_halts(rm, initial_config(rm, s), fuel) ==> (
                    run(rm, initial_config(rm, s), fuel).registers[0] == f_h(s) &&
                    run(rm, initial_config(rm, s), fuel).registers[1] == f_1(s) &&
                    run(rm, initial_config(rm, s), fuel).registers[2] == f_2(s)
                )),
{
    let m = build_multi_output(rm_halts, rm_out1, rm_out2);
    lemma_build_multi_output_wf(rm_halts, rm_out1, rm_out2);
    let n_h = rm_halts.instructions.len();
    let n_1 = rm_out1.instructions.len();
    let n_2 = rm_out2.instructions.len();
    let bh: nat = 4;
    let b1: nat = 4 + rm_halts.num_regs;
    let b2: nat = 4 + rm_halts.num_regs + rm_out1.num_regs;
    let scratch: nat = 3;
    let nr = m.num_regs;
    let p1: nat = 5;
    let p2: nat = 5 + n_h;
    let p3: nat = 8 + n_h;
    let p4: nat = 8 + n_h + n_1;
    let p5: nat = 11 + n_h + n_1;
    let p6: nat = 11 + n_h + n_1 + n_2;
    let p7: nat = 14 + n_h + n_1 + n_2;

    //  Prove halts and register correctness for each input
    assert forall|s: nat| halts(m, s) by {
        lemma_multi_output_for_input(
            rm_halts, rm_out1, rm_out2, f_h, f_1, f_2, s);
    };

    assert forall|s: nat, fuel: nat|
        run_halts(m, initial_config(m, s), fuel)
    implies (
        run(m, initial_config(m, s), fuel).registers[0] == f_h(s) &&
        run(m, initial_config(m, s), fuel).registers[1] == f_1(s) &&
        run(m, initial_config(m, s), fuel).registers[2] == f_2(s)
    ) by {
        lemma_multi_output_for_input(
            rm_halts, rm_out1, rm_out2, f_h, f_1, f_2, s);
        //  halts gives a specific fuel with the right registers
        //  by determinism, any halting fuel gives the same result
        let specific_fuel: nat = choose|f: nat| run_halts(m, initial_config(m, s), f) &&
            run(m, initial_config(m, s), f).registers[0] == f_h(s) &&
            run(m, initial_config(m, s), f).registers[1] == f_1(s) &&
            run(m, initial_config(m, s), f).registers[2] == f_2(s);
        lemma_run_deterministic(m, initial_config(m, s), fuel, specific_fuel);
    };
}

} //  verus!
