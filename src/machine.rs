use vstd::prelude::*;

verus! {

///  A register machine instruction.
pub enum Instruction {
    ///  Increment register `register` by 1.
    Inc { register: nat },
    ///  If register `register` > 0, decrement it; otherwise jump to `target`.
    DecJump { register: nat, target: nat },
    ///  Halt execution.
    Halt,
}

///  A register machine: a finite sequence of instructions with a fixed register count.
pub struct RegisterMachine {
    pub instructions: Seq<Instruction>,
    pub num_regs: nat,
}

///  A machine configuration: program counter + register contents.
pub struct Configuration {
    pub pc: nat,
    pub registers: Seq<nat>,
}

///  Well-formedness of a register machine: num_regs > 0, all register references
///  are in bounds, all jump targets are valid (≤ instructions.len()).
#[verifier::opaque]
pub open spec fn machine_wf(m: RegisterMachine) -> bool {
    m.num_regs > 0 &&
    forall|i: int| #![trigger m.instructions[i]]
        0 <= i < m.instructions.len() ==> match m.instructions[i] {
            Instruction::Inc { register } => register < m.num_regs,
            Instruction::DecJump { register, target } =>
                register < m.num_regs && target <= m.instructions.len(),
            Instruction::Halt => true,
        }
}

///  Well-formedness of a configuration w.r.t. a machine.
pub open spec fn config_wf(m: RegisterMachine, c: Configuration) -> bool {
    c.pc <= m.instructions.len() &&
    c.registers.len() == m.num_regs
}

///  Execute a single instruction. Returns None if halted or pc out of bounds.
pub open spec fn step(m: RegisterMachine, c: Configuration) -> Option<Configuration> {
    if c.pc >= m.instructions.len() {
        None
    } else {
        match m.instructions[c.pc as int] {
            Instruction::Halt => None,
            Instruction::Inc { register } => {
                if register < c.registers.len() {
                    Some(Configuration {
                        pc: c.pc + 1,
                        registers: c.registers.update(register as int, c.registers[register as int] + 1),
                    })
                } else {
                    None //  malformed
                }
            },
            Instruction::DecJump { register, target } => {
                if register < c.registers.len() {
                    if c.registers[register as int] > 0 {
                        Some(Configuration {
                            pc: c.pc + 1,
                            registers: c.registers.update(register as int, (c.registers[register as int] - 1) as nat),
                        })
                    } else {
                        Some(Configuration {
                            pc: target,
                            registers: c.registers,
                        })
                    }
                } else {
                    None //  malformed
                }
            },
        }
    }
}

///  The machine is halted (step returns None).
pub open spec fn is_halted(m: RegisterMachine, c: Configuration) -> bool {
    step(m, c) is None
}

///  Run the machine for `fuel` steps, returning the final configuration.
pub open spec fn run(m: RegisterMachine, c: Configuration, fuel: nat) -> Configuration
    decreases fuel,
{
    if fuel == 0 {
        c
    } else {
        match step(m, c) {
            Some(next) => run(m, next, (fuel - 1) as nat),
            None => c,
        }
    }
}

///  The machine halts within `fuel` steps from configuration `c`.
pub open spec fn run_halts(m: RegisterMachine, c: Configuration, fuel: nat) -> bool
    decreases fuel,
{
    if fuel == 0 {
        is_halted(m, c)
    } else {
        is_halted(m, c) || match step(m, c) {
            Some(next) => run_halts(m, next, (fuel - 1) as nat),
            None => true,
        }
    }
}

///  The initial configuration: pc=0, reg[0]=input, rest=0.
pub open spec fn initial_config(m: RegisterMachine, input: nat) -> Configuration
    recommends m.num_regs > 0,
{
    Configuration {
        pc: 0,
        registers: Seq::new(m.num_regs as nat, |i: int| if i == 0 { input } else { 0nat }),
    }
}

///  The machine halts on the given input.
pub open spec fn halts(m: RegisterMachine, input: nat) -> bool {
    exists|fuel: nat| run_halts(m, initial_config(m, input), fuel)
}

///  The output of a halting computation: register 0 of the halted configuration.
pub open spec fn output(m: RegisterMachine, input: nat) -> nat
    recommends halts(m, input) && m.num_regs > 0,
{
    let fuel = choose|fuel: nat| run_halts(m, initial_config(m, input), fuel);
    run(m, initial_config(m, input), fuel).registers[0]
}

//  ============================================================
//  Proof lemmas
//  ============================================================

///  A well-formed step preserves configuration well-formedness.
pub proof fn lemma_step_preserves_config_wf(m: RegisterMachine, c: Configuration)
    requires
        machine_wf(m),
        config_wf(m, c),
        step(m, c) is Some,
    ensures
        config_wf(m, step(m, c).unwrap()),
{
    reveal(machine_wf);
    let next = step(m, c).unwrap();
    assert(c.pc < m.instructions.len());
    let instr = m.instructions[c.pc as int];
    match instr {
        Instruction::Inc { register } => {
            assert(register < m.num_regs);
            assert(next.pc == c.pc + 1);
            assert(next.registers.len() == m.num_regs);
        },
        Instruction::DecJump { register, target } => {
            assert(register < m.num_regs);
            assert(target <= m.instructions.len());
            if c.registers[register as int] > 0 {
                assert(next.pc == c.pc + 1);
            } else {
                assert(next.pc == target);
            }
            assert(next.registers.len() == m.num_regs);
        },
        Instruction::Halt => {
            assert(false);
        },
    }
}

///  If the machine halts at fuel f1 and f2, run gives the same result.
pub proof fn lemma_run_deterministic(m: RegisterMachine, c: Configuration, f1: nat, f2: nat)
    requires
        run_halts(m, c, f1),
        run_halts(m, c, f2),
    ensures
        run(m, c, f1) == run(m, c, f2),
    decreases f1,
{
    if f1 == 0 {
        assert(is_halted(m, c));
        lemma_halted_run_identity(m, c, f2);
    } else if is_halted(m, c) {
        lemma_halted_run_identity(m, c, f1);
        lemma_halted_run_identity(m, c, f2);
    } else {
        let next = step(m, c).unwrap();
        if f2 == 0 {
            assert(false);
        } else {
            lemma_run_deterministic(m, next, (f1 - 1) as nat, (f2 - 1) as nat);
        }
    }
}

///  If the machine is halted, running for any fuel returns the same configuration.
pub proof fn lemma_halted_run_identity(m: RegisterMachine, c: Configuration, fuel: nat)
    requires
        is_halted(m, c),
    ensures
        run(m, c, fuel) == c,
    decreases fuel,
{
    if fuel == 0 {
    } else {
        assert(step(m, c) is None);
    }
}

///  If the machine halts at fuel f1, it also halts at any f2 >= f1 with same result.
pub proof fn lemma_run_monotone(m: RegisterMachine, c: Configuration, f1: nat, f2: nat)
    requires
        run_halts(m, c, f1),
        f2 >= f1,
    ensures
        run_halts(m, c, f2),
        run(m, c, f1) == run(m, c, f2),
    decreases f1,
{
    if f1 == 0 {
        assert(is_halted(m, c));
        lemma_halted_run_identity(m, c, f2);
        lemma_halted_run_halts(m, c, f2);
    } else if is_halted(m, c) {
        lemma_halted_run_identity(m, c, f1);
        lemma_halted_run_identity(m, c, f2);
        lemma_halted_run_halts(m, c, f2);
    } else {
        let next = step(m, c).unwrap();
        if f2 == 0 {
            assert(false);
        } else {
            lemma_run_monotone(m, next, (f1 - 1) as nat, (f2 - 1) as nat);
        }
    }
}

///  A halted configuration halts within any fuel.
pub proof fn lemma_halted_run_halts(m: RegisterMachine, c: Configuration, fuel: nat)
    requires
        is_halted(m, c),
    ensures
        run_halts(m, c, fuel),
{
}

///  The output of a halting computation is well-defined (unique).
pub proof fn lemma_output_well_defined(m: RegisterMachine, input: nat)
    requires
        halts(m, input),
        m.num_regs > 0,
    ensures
        forall|f1: nat, f2: nat|
            run_halts(m, initial_config(m, input), f1) &&
            run_halts(m, initial_config(m, input), f2)
            ==> run(m, initial_config(m, input), f1).registers[0]
             == run(m, initial_config(m, input), f2).registers[0],
{
    assert forall|f1: nat, f2: nat|
        run_halts(m, initial_config(m, input), f1) &&
        run_halts(m, initial_config(m, input), f2)
        implies run(m, initial_config(m, input), f1).registers[0]
             == run(m, initial_config(m, input), f2).registers[0]
    by {
        lemma_run_deterministic(m, initial_config(m, input), f1, f2);
    }
}

} //  verus!
