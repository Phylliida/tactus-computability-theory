use vstd::prelude::*;
use crate::machine::*;

verus! {

//  ============================================================
//  Construction spec functions
//  ============================================================

///  Replace all Halt instructions with DecJump{scratch_reg, target_pc}.
pub open spec fn replace_halts(
    instrs: Seq<Instruction>,
    scratch_reg: nat,
    target_pc: nat,
) -> Seq<Instruction> {
    Seq::new(instrs.len(), |i: int|
        match instrs[i] {
            Instruction::Halt => Instruction::DecJump { register: scratch_reg, target: target_pc },
            instr => instr,
        }
    )
}

///  Build a machine that runs `rm` to completion, then halts iff reg[0] > 0.
///
///  Construction:
///    - scratch = rm.num_regs (new register, always 0)
///    - Replace all Halt with DecJump{scratch, N} (unconditional jump to N)
///    - Append DecJump{0, N} at position N (loop if reg[0]==0, else fall through)
///    - Append Halt at position N+1
pub open spec fn build_cond_halt(rm: RegisterMachine) -> RegisterMachine {
    let n = rm.instructions.len();
    let scratch = rm.num_regs;
    RegisterMachine {
        instructions: replace_halts(rm.instructions, scratch, n)
            .push(Instruction::DecJump { register: 0, target: n })
            .push(Instruction::Halt),
        num_regs: rm.num_regs + 1,
    }
}

///  Configurations agree: same pc, registers match on [0, num_regs), scratch = 0.
pub open spec fn cond_configs_agree(
    num_regs: nat,
    c1: Configuration,
    c2: Configuration,
) -> bool {
    c1.pc == c2.pc &&
    c1.registers.len() == num_regs &&
    c2.registers.len() == num_regs + 1 &&
    (forall|i: int| 0 <= i < num_regs as int ==>
        c2.registers[i] == c1.registers[i]) &&
    c2.registers[num_regs as int] == 0
}

//  ============================================================
//  Well-formedness
//  ============================================================

pub proof fn lemma_build_cond_halt_wf(rm: RegisterMachine)
    requires machine_wf(rm),
    ensures machine_wf(build_cond_halt(rm)),
{
    reveal(machine_wf);
    let rm2 = build_cond_halt(rm);
    let n = rm.instructions.len();
    let scratch = rm.num_regs;
    assert forall|i: int| #![trigger rm2.instructions[i]]
        0 <= i < rm2.instructions.len()
    implies match rm2.instructions[i] {
        Instruction::Inc { register } => register < rm2.num_regs,
        Instruction::DecJump { register, target } =>
            register < rm2.num_regs && target <= rm2.instructions.len(),
        Instruction::Halt => true,
    } by {
        if i < n {
            //  Original or replaced instruction
            assert(rm2.instructions[i] == replace_halts(rm.instructions, scratch, n)[i as int]);
            match rm.instructions[i] {
                Instruction::Halt => {
                    assert(rm2.instructions[i] == Instruction::DecJump {
                        register: scratch, target: n,
                    });
                },
                _ => {
                    assert(rm2.instructions[i] == rm.instructions[i]);
                },
            }
        } else if i == n as int {
            //  DecJump{0, n}
        } else {
            //  Halt at n+1
        }
    };
}

//  ============================================================
//  Initial config agreement
//  ============================================================

pub proof fn lemma_init_configs_agree(rm: RegisterMachine, s: nat)
    requires machine_wf(rm),
    ensures
        cond_configs_agree(rm.num_regs, initial_config(rm, s), initial_config(build_cond_halt(rm), s)),
        config_wf(rm, initial_config(rm, s)),
{
    reveal(machine_wf);
    let c1 = initial_config(rm, s);
    let c2 = initial_config(build_cond_halt(rm), s);
    assert forall|i: int| 0 <= i < rm.num_regs as int
    implies c2.registers[i] == c1.registers[i] by {};
}

//  ============================================================
//  Single-step simulation
//  ============================================================

///  If rm is not halted at c1, then build_cond_halt(rm) steps identically from c2.
pub proof fn lemma_step_sim(
    rm: RegisterMachine,
    c1: Configuration,
    c2: Configuration,
)
    requires
        machine_wf(rm),
        config_wf(rm, c1),
        cond_configs_agree(rm.num_regs, c1, c2),
        !is_halted(rm, c1),
    ensures
        !is_halted(build_cond_halt(rm), c2),
        step(rm, c1) is Some,
        step(build_cond_halt(rm), c2) is Some,
        cond_configs_agree(
            rm.num_regs,
            step(rm, c1).unwrap(),
            step(build_cond_halt(rm), c2).unwrap(),
        ),
        config_wf(rm, step(rm, c1).unwrap()),
{
    reveal(machine_wf);
    let rm2 = build_cond_halt(rm);
    let n = rm.instructions.len();
    let scratch = rm.num_regs;
    let pc = c1.pc;

    //  Not halted means pc < n and instruction is not Halt
    assert(pc < n);
    let instr = rm.instructions[pc as int];
    assert(!(instr is Halt));

    //  In rm2, instruction at pc is the same (replace_halts preserves non-Halt)
    assert(rm2.instructions[pc as int] == instr);

    let s1 = step(rm, c1).unwrap();
    let s2 = step(rm2, c2).unwrap();

    match instr {
        Instruction::Inc { register: r } => {
            assert(c2.registers[r as int] == c1.registers[r as int]);
            assert forall|i: int| 0 <= i < rm.num_regs as int
            implies s2.registers[i] == s1.registers[i] by {
                if i == r as int {
                    assert(c2.registers[i] == c1.registers[i]);
                } else {
                    assert(s2.registers[i] == c2.registers[i]);
                    assert(s1.registers[i] == c1.registers[i]);
                }
            };
            assert(s2.registers[scratch as int] == 0) by {
                assert(r < rm.num_regs);
                assert(s2.registers[scratch as int] == c2.registers[scratch as int]);
            };
        },
        Instruction::DecJump { register: r, target: t } => {
            assert(c2.registers[r as int] == c1.registers[r as int]);
            if c1.registers[r as int] > 0 {
                //  Decrement branch
                assert forall|i: int| 0 <= i < rm.num_regs as int
                implies s2.registers[i] == s1.registers[i] by {
                    if i == r as int {
                        assert(c2.registers[i] == c1.registers[i]);
                    } else {
                        assert(s2.registers[i] == c2.registers[i]);
                        assert(s1.registers[i] == c1.registers[i]);
                    }
                };
                assert(s2.registers[scratch as int] == 0) by {
                    assert(r < rm.num_regs);
                    assert(s2.registers[scratch as int] == c2.registers[scratch as int]);
                };
            } else {
                //  Jump branch
                assert forall|i: int| 0 <= i < rm.num_regs as int
                implies s2.registers[i] == s1.registers[i] by {
                    assert(s2.registers[i] == c2.registers[i]);
                    assert(s1.registers[i] == c1.registers[i]);
                };
                assert(s2.registers[scratch as int] == c2.registers[scratch as int]);
            }
        },
        Instruction::Halt => {
            assert(false);
        },
    }
}

//  ============================================================
//  Multi-step simulation (while rm hasn't halted)
//  ============================================================

pub proof fn lemma_sim(
    rm: RegisterMachine,
    c1: Configuration,
    c2: Configuration,
    f: nat,
)
    requires
        machine_wf(rm),
        config_wf(rm, c1),
        cond_configs_agree(rm.num_regs, c1, c2),
        !run_halts(rm, c1, f),
    ensures
        !run_halts(build_cond_halt(rm), c2, f),
        cond_configs_agree(
            rm.num_regs,
            run(rm, c1, f),
            run(build_cond_halt(rm), c2, f),
        ),
        config_wf(rm, run(rm, c1, f)),
    decreases f,
{
    let rm2 = build_cond_halt(rm);
    if f == 0 {
        //  !run_halts at 0 means !is_halted
        lemma_step_sim(rm, c1, c2);
    } else {
        //  !is_halted, step is Some
        lemma_step_sim(rm, c1, c2);
        let n1 = step(rm, c1).unwrap();
        let n2 = step(rm2, c2).unwrap();
        lemma_sim(rm, n1, n2, (f - 1) as nat);
    }
}

//  ============================================================
//  Reaching pc = n
//  ============================================================

///  When rm halts at fuel f, build_cond_halt(rm) reaches pc = n
///  within f+1 steps, with matching registers.
pub proof fn lemma_reaches_n(
    rm: RegisterMachine,
    c1: Configuration,
    c2: Configuration,
    f: nat,
)
    requires
        machine_wf(rm),
        config_wf(rm, c1),
        cond_configs_agree(rm.num_regs, c1, c2),
        run_halts(rm, c1, f),
    ensures ({
        let rm2 = build_cond_halt(rm);
        let n = rm.instructions.len();
        let c_halt = run(rm, c1, f);
        exists|g: nat|
            g <= f + 1 &&
            run(rm2, c2, g).pc == n &&
            run(rm2, c2, g).registers.len() == rm.num_regs + 1 &&
            (forall|i: int| 0 <= i < rm.num_regs as int ==>
                run(rm2, c2, g).registers[i] == c_halt.registers[i]) &&
            run(rm2, c2, g).registers[rm.num_regs as int] == 0 &&
            (g > 0 ==> !run_halts(rm2, c2, (g - 1) as nat))
    }),
    decreases f,
{
    reveal(machine_wf);
    let rm2 = build_cond_halt(rm);
    let n = rm.instructions.len();
    let scratch = rm.num_regs;

    if is_halted(rm, c1) {
        lemma_halted_run_identity(rm, c1, f);
        //  run(rm, c1, f) == c1

        if c1.pc >= n {
            //  c1.pc == n (from config_wf: pc <= instructions.len())
            assert(c1.pc == n);
            //  c2.pc == n, already at n. g = 0.
            assert(run(rm2, c2, 0) == c2);
            assert(c2.pc == n);
        } else {
            //  instruction is Halt, replaced with DecJump{scratch, n}
            assert(rm.instructions[c1.pc as int] is Halt);
            assert(rm2.instructions[c2.pc as int] ==
                Instruction::DecJump { register: scratch, target: n });
            //  scratch is 0, so jump to n
            assert(!is_halted(rm2, c2));
            let next = step(rm2, c2).unwrap();
            assert(next.pc == n);
            assert(next.registers == c2.registers);
            //  Explicitly unfold: run(rm2, c2, 1) == next
            assert(step(rm2, c2) == Some(next));
            assert(run(rm2, next, 0) == next);
            assert(run(rm2, c2, 1) == next);
            //  registers of run(rm2, c2, 1) match c1's
            assert forall|i: int| 0 <= i < rm.num_regs as int implies
                run(rm2, c2, 1).registers[i] == run(rm, c1, f).registers[i]
            by {};
            assert(run(rm2, c2, 1).registers[rm.num_regs as int] == 0);
            //  !run_halts(rm2, c2, 0): DecJump is not Halt
        }
    } else {
        //  rm takes a step
        assert(f > 0);
        let n1 = step(rm, c1).unwrap();
        lemma_step_sim(rm, c1, c2);
        lemma_step_preserves_config_wf(rm, c1);
        let n2 = step(rm2, c2).unwrap();

        //  Inductive call
        lemma_reaches_n(rm, n1, n2, (f - 1) as nat);

        let c_halt_inner = run(rm, n1, (f - 1) as nat);
        let g_inner: nat = choose|g: nat|
            g <= f &&
            run(rm2, n2, g).pc == n &&
            run(rm2, n2, g).registers.len() == rm.num_regs + 1 &&
            (forall|i: int| 0 <= i < rm.num_regs as int ==>
                run(rm2, n2, g).registers[i] == c_halt_inner.registers[i]) &&
            run(rm2, n2, g).registers[rm.num_regs as int] == 0 &&
            (g > 0 ==> !run_halts(rm2, n2, (g - 1) as nat));

        //  g = g_inner + 1
        let g = g_inner + 1;

        //  run(rm2, c2, g) = run(rm2, n2, g_inner)
        assert(run(rm2, c2, g) == run(rm2, n2, g_inner));
        //  run(rm, c1, f) = run(rm, n1, f-1)
        assert(run(rm, c1, f) == c_halt_inner);

        //  !run_halts(rm2, c2, g - 1) = !run_halts(rm2, c2, g_inner)
        if g_inner == 0 {
            //  !run_halts(rm2, c2, 0) = !is_halted(rm2, c2)
            //  True from step_sim: step is Some, so not halted
        } else {
            //  !run_halts(rm2, c2, g_inner):
            //  = !is_halted(rm2, c2) && !(step is Some && run_halts(n2, g_inner - 1))
            //  = true && !run_halts(n2, g_inner - 1) [from induction]
        }
    }
}

//  ============================================================
//  Behavior at pc = n
//  ============================================================

///  At pc = n with reg[0] > 0: halts in 2 steps, regs 1 and 2 preserved.
pub proof fn lemma_at_n_halts(
    rm: RegisterMachine,
    c: Configuration,
)
    requires
        machine_wf(rm),
        rm.num_regs >= 3,
        c.pc == rm.instructions.len(),
        c.registers.len() == rm.num_regs + 1,
        c.registers[0] > 0,
    ensures ({
        let rm2 = build_cond_halt(rm);
        run_halts(rm2, c, 2) &&
        run(rm2, c, 2).registers[1] == c.registers[1] &&
        run(rm2, c, 2).registers[2] == c.registers[2]
    }),
{
    reveal(machine_wf);
    let rm2 = build_cond_halt(rm);
    let n = rm.instructions.len();
    //  Instruction at n: DecJump{0, n}. reg[0] > 0: decrement, pc = n+1.
    assert(!is_halted(rm2, c));
    let c1 = step(rm2, c).unwrap();
    assert(c1.pc == n + 1);
    assert(c1.registers == c.registers.update(0, (c.registers[0] - 1) as nat));
    //  Instruction at n+1: Halt
    assert(is_halted(rm2, c1));
    //  Explicitly unfold run
    //  run(rm2, c, 1) = run(rm2, c1, 0) = c1
    assert(run(rm2, c1, 0) == c1);
    //  run(rm2, c, 2) = run(rm2, c1, 1)
    lemma_halted_run_identity(rm2, c1, 1);
    assert(run(rm2, c1, 1) == c1);
    //  run_halts(rm2, c, 2): !is_halted(c), step = Some(c1), run_halts(c1, 1)?
    //  run_halts(rm2, c1, 1) = is_halted(c1) || ... = true
    assert(run_halts(rm2, c1, 1));
    //  So run_halts(rm2, c, 2)
    assert(c1.registers[1] == c.registers[1]);
    assert(c1.registers[2] == c.registers[2]);
}

///  At pc = n with reg[0] == 0: infinite loop, never halts.
pub proof fn lemma_at_n_loops(
    rm: RegisterMachine,
    c: Configuration,
    fuel: nat,
)
    requires
        machine_wf(rm),
        c.pc == rm.instructions.len(),
        c.registers.len() == rm.num_regs + 1,
        c.registers[0] == 0,
    ensures
        !run_halts(build_cond_halt(rm), c, fuel),
    decreases fuel,
{
    reveal(machine_wf);
    let rm2 = build_cond_halt(rm);
    let n = rm.instructions.len();
    //  Instruction at n: DecJump{0, n}. reg[0] == 0: jump to n. Same config.
    if fuel > 0 {
        let next = step(rm2, c).unwrap();
        assert(next.pc == n);
        assert(next.registers == c.registers);
        lemma_at_n_loops(rm, next, (fuel - 1) as nat);
    }
}

//  ============================================================
//  Fuel composition lemmas
//  ============================================================

///  If not halted after f1 steps, run_halts at f1+f2+1 iff run_halts
///  of the remaining f2 from the config at step f1+1.
pub proof fn lemma_run_halts_split(
    m: RegisterMachine,
    c: Configuration,
    f1: nat,
    f2: nat,
)
    requires
        !run_halts(m, c, f1),
    ensures
        run_halts(m, c, (f1 + f2 + 1) as nat) <==>
            run_halts(m, run(m, c, (f1 + 1) as nat), f2),
    decreases f1,
{
    if f1 == 0 {
        //  !run_halts at 0 means !is_halted
        assert(!is_halted(m, c));
        let next = step(m, c).unwrap();
        //  run(m, c, 1) = next
        assert(run(m, c, 1) == run(m, next, 0));
        //  run_halts(m, c, f2+1) = is_halted(c) || run_halts(next, f2) = run_halts(next, f2)
    } else {
        assert(!is_halted(m, c));
        let next = step(m, c).unwrap();
        lemma_run_halts_split(m, next, (f1 - 1) as nat, f2);
    }
}

///  If not halted after f1 steps, run at f1+f2+1 equals run from
///  config at step f1+1 for f2 more steps.
pub proof fn lemma_run_split(
    m: RegisterMachine,
    c: Configuration,
    f1: nat,
    f2: nat,
)
    requires
        !run_halts(m, c, f1),
    ensures
        run(m, c, (f1 + f2 + 1) as nat) == run(m, run(m, c, (f1 + 1) as nat), f2),
    decreases f1,
{
    if f1 == 0 {
        assert(!is_halted(m, c));
        let next = step(m, c).unwrap();
        assert(run(m, c, 1) == run(m, next, 0));
    } else {
        assert(!is_halted(m, c));
        let next = step(m, c).unwrap();
        lemma_run_split(m, next, (f1 - 1) as nat, f2);
    }
}

//  ============================================================
//  Main proof
//  ============================================================

pub proof fn lemma_conditional_halt_on_reg0(
    rm_total: RegisterMachine,
    f_h: spec_fn(nat) -> nat,
    f_1: spec_fn(nat) -> nat,
    f_2: spec_fn(nat) -> nat,
)
    requires
        machine_wf(rm_total) && rm_total.num_regs >= 3 &&
        (forall|s: nat| halts(rm_total, s)) &&
        (forall|s: nat, fuel: nat|
            run_halts(rm_total, initial_config(rm_total, s), fuel) ==> (
                run(rm_total, initial_config(rm_total, s), fuel).registers[0] == f_h(s) &&
                run(rm_total, initial_config(rm_total, s), fuel).registers[1] == f_1(s) &&
                run(rm_total, initial_config(rm_total, s), fuel).registers[2] == f_2(s)
            )),
    ensures
        exists|rm: RegisterMachine|
            machine_wf(rm) && rm.num_regs >= 3 &&
            (forall|s: nat| halts(rm, s) <==> f_h(s) != 0) &&
            (forall|s: nat, fuel: nat|
                run_halts(rm, initial_config(rm, s), fuel) ==> (
                    run(rm, initial_config(rm, s), fuel).registers[1] == f_1(s) &&
                    run(rm, initial_config(rm, s), fuel).registers[2] == f_2(s)
                )),
{
    let rm2 = build_cond_halt(rm_total);
    lemma_build_cond_halt_wf(rm_total);
    let n = rm_total.instructions.len();

    //  --- Part 1: halts(rm2, s) <==> f_h(s) != 0 ---
    assert forall|s: nat| halts(rm2, s) <==> f_h(s) != 0 by {
        let init1 = initial_config(rm_total, s);
        let init2 = initial_config(rm2, s);
        lemma_init_configs_agree(rm_total, s);

        //  rm_total halts on s
        assert(halts(rm_total, s));
        let ft: nat = choose|f: nat| run_halts(rm_total, init1, f);
        assert(run_halts(rm_total, init1, ft));

        //  Establish preconditions for lemma_reaches_n
        assert(config_wf(rm_total, init1));
        assert(cond_configs_agree(rm_total.num_regs, init1, init2));

        //  rm2 reaches pc = n with matching registers
        lemma_reaches_n(rm_total, init1, init2, ft);
        let c_halt = run(rm_total, init1, ft);
        let g: nat = choose|g: nat|
            g <= ft + 1 &&
            run(rm2, init2, g).pc == n &&
            run(rm2, init2, g).registers.len() == rm_total.num_regs + 1 &&
            (forall|i: int| 0 <= i < rm_total.num_regs as int ==>
                run(rm2, init2, g).registers[i] == c_halt.registers[i]) &&
            run(rm2, init2, g).registers[rm_total.num_regs as int] == 0 &&
            (g > 0 ==> !run_halts(rm2, init2, (g - 1) as nat));
        let c_at_n = run(rm2, init2, g);

        //  c_at_n.registers[0] == f_h(s)
        assert(c_at_n.registers[0] == f_h(s));

        if f_h(s) != 0 {
            //  Forward: f_h(s) != 0 ==> halts(rm2, s)
            assert(c_at_n.registers[0] > 0);
            lemma_at_n_halts(rm_total, c_at_n);
            //  run_halts(rm2, c_at_n, 2)
            if g == 0 {
                assert(run_halts(rm2, init2, 2));
            } else {
                lemma_run_halts_split(rm2, init2, (g - 1) as nat, 2);
            }
            //  halts(rm2, s)
        } else {
            //  Backward: f_h(s) == 0 ==> !halts(rm2, s)
            assert(c_at_n.registers[0] == 0);
            if halts(rm2, s) {
                let big_f: nat = choose|f: nat| run_halts(rm2, init2, f);
                if g == 0 {
                    //  c_at_n == init2
                    lemma_at_n_loops(rm_total, c_at_n, big_f);
                    assert(false);
                } else {
                    //  !run_halts(rm2, init2, g - 1)
                    if big_f < g {
                        lemma_run_monotone(rm2, init2, big_f, (g - 1) as nat);
                        assert(false);
                    } else {
                        //  big_f >= g, so (g-1) + (big_f - g) + 1 == big_f
                        lemma_run_halts_split(rm2, init2, (g - 1) as nat, (big_f - g) as nat);
                        //  run_halts(rm2, c_at_n, big_f - g)
                        lemma_at_n_loops(rm_total, c_at_n, (big_f - g) as nat);
                        assert(false);
                    }
                }
            }
        }
    };

    //  --- Part 2: register preservation ---
    assert forall|s: nat, fuel: nat|
        run_halts(rm2, initial_config(rm2, s), fuel)
    implies (
        run(rm2, initial_config(rm2, s), fuel).registers[1] == f_1(s) &&
        run(rm2, initial_config(rm2, s), fuel).registers[2] == f_2(s)
    ) by {
        let init1 = initial_config(rm_total, s);
        let init2 = initial_config(rm2, s);
        lemma_init_configs_agree(rm_total, s);

        //  run_halts implies halts implies f_h(s) != 0
        assert(halts(rm2, s));
        assert(f_h(s) != 0);

        //  Get halting fuel and reach n
        assert(halts(rm_total, s));
        let ft: nat = choose|f: nat| run_halts(rm_total, init1, f);
        assert(run_halts(rm_total, init1, ft));
        assert(config_wf(rm_total, init1));
        assert(cond_configs_agree(rm_total.num_regs, init1, init2));
        lemma_reaches_n(rm_total, init1, init2, ft);
        let c_halt = run(rm_total, init1, ft);
        let g: nat = choose|g: nat|
            g <= ft + 1 &&
            run(rm2, init2, g).pc == n &&
            run(rm2, init2, g).registers.len() == rm_total.num_regs + 1 &&
            (forall|i: int| 0 <= i < rm_total.num_regs as int ==>
                run(rm2, init2, g).registers[i] == c_halt.registers[i]) &&
            run(rm2, init2, g).registers[rm_total.num_regs as int] == 0 &&
            (g > 0 ==> !run_halts(rm2, init2, (g - 1) as nat));
        let c_at_n = run(rm2, init2, g);

        assert(c_at_n.registers[1] == f_1(s));
        assert(c_at_n.registers[2] == f_2(s));

        //  Halts at c_at_n in 2 steps
        lemma_at_n_halts(rm_total, c_at_n);
        let c_halted = run(rm2, c_at_n, 2);
        assert(c_halted.registers[1] == f_1(s));
        assert(c_halted.registers[2] == f_2(s));

        //  run(rm2, init2, g + 2) == c_halted
        if g == 0 {
            assert(run(rm2, init2, 2) == c_halted);
        } else {
            lemma_run_split(rm2, init2, (g - 1) as nat, 2);
        }

        //  run_halts at g + 2
        if g == 0 {
            assert(run_halts(rm2, init2, 2));
        } else {
            lemma_run_halts_split(rm2, init2, (g - 1) as nat, 2);
        }

        //  By determinism: run at fuel == run at g+2
        lemma_run_deterministic(rm2, init2, fuel, (g + 2) as nat);
    };
}

} //  verus!
