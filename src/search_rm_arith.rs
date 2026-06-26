//  GAP-2 / L0 brick B-L0.2a — register-machine arithmetic for the dovetail driver.
//
//  The dovetail's HALTED comparison re-pairs the enumerator's declared output `(reg1,reg2)` with the
//  forward Cantor `pair` and compares to the preserved input — avoiding the harder *unpairing*.  This
//  module builds the reusable RM arithmetic that needs:
//    * `double_dist_instrs` — drain one register into TWO destinations (the "add x to t preserving x"
//      primitive: `copy(x→backup)` then `double_dist(backup→t,x)`), mirroring
//      `multi_output_primitives::triple_dist_instrs`.
//
//  See docs/gap2-l0-search-rm-plan.md (B-L0.2a).

use vstd::prelude::*;
use crate::machine::*;
use crate::multi_output_primitives::{mk_inc, mk_dj};

verus! {

//  ============================================================
//  run unfolding helper (private copy)
//  ============================================================

proof fn lemma_run_unfold_step(m: RegisterMachine, c: Configuration, fuel: nat)
    requires
        !is_halted(m, c),
        fuel > 0,
    ensures
        step(m, c) is Some,
        run(m, c, fuel) == run(m, step(m, c).unwrap(), (fuel - 1) as nat),
{
}

//  ============================================================
//  Double distribute: src → (d1, d2) simultaneously (src destroyed).
//  4 instructions starting at start_pc. Next instruction at start_pc + 4.
//  ============================================================

pub open spec fn double_dist_instrs(
    src: nat, d1: nat, d2: nat, scratch: nat, start_pc: nat,
) -> Seq<Instruction> {
    seq![
        Instruction::DecJump { register: src, target: start_pc + 4 },
        Instruction::Inc { register: d1 },
        Instruction::Inc { register: d2 },
        Instruction::DecJump { register: scratch, target: start_pc },
    ]
}

#[verifier::rlimit(1000)]
pub proof fn lemma_double_dist_inner(
    m: RegisterMachine,
    c: Configuration,
    src: nat, d1: nat, d2: nat, scratch: nat,
    start_pc: nat,
    orig_val: nat, acc: nat, remaining: nat,
)
    requires
        start_pc + 4 <= m.instructions.len(),
        m.instructions[start_pc as int] == mk_dj(src, start_pc + 4),
        m.instructions[(start_pc + 1) as int] == mk_inc(d1),
        m.instructions[(start_pc + 2) as int] == mk_inc(d2),
        m.instructions[(start_pc + 3) as int] == mk_dj(scratch, start_pc),
        c.pc == start_pc,
        c.registers.len() == m.num_regs,
        c.registers[src as int] == remaining,
        c.registers[d1 as int] == acc,
        c.registers[d2 as int] == acc,
        c.registers[scratch as int] == 0,
        src < m.num_regs, d1 < m.num_regs, d2 < m.num_regs, scratch < m.num_regs,
        src != d1, src != d2, src != scratch,
        d1 != d2, d1 != scratch, d2 != scratch,
        acc + remaining == orig_val,
    ensures
        run(m, c, 4 * remaining + 1).pc == start_pc + 4,
        run(m, c, 4 * remaining + 1).registers[src as int] == 0,
        run(m, c, 4 * remaining + 1).registers[d1 as int] == orig_val,
        run(m, c, 4 * remaining + 1).registers[d2 as int] == orig_val,
        run(m, c, 4 * remaining + 1).registers[scratch as int] == 0,
        forall|r: int| 0 <= r < m.num_regs as int
            && r != src as int && r != d1 as int && r != d2 as int
            ==> run(m, c, 4 * remaining + 1).registers[r] == c.registers[r],
    decreases remaining,
{
    if remaining == 0 {
        assert(4 * remaining + 1 > 0) by(nonlinear_arith) requires remaining == 0;
        assert(!is_halted(m, c));
        lemma_run_unfold_step(m, c, 4 * remaining + 1);
        let c1 = step(m, c).unwrap();
        assert(c1.pc == start_pc + 4);
        assert(c1.registers == c.registers);
        assert((4 * remaining + 1 - 1) as nat == 0nat) by(nonlinear_arith) requires remaining == 0;
        assert(run(m, c1, (4 * remaining + 1 - 1) as nat) == c1);
        assert(run(m, c, 4 * remaining + 1) == c1);
        assert(run(m, c, 4 * remaining + 1).registers =~= c.registers);
    } else {
        assert(!is_halted(m, c));
        lemma_run_unfold_step(m, c, 4 * remaining + 1);
        let c1 = step(m, c).unwrap();
        assert(!is_halted(m, c1));
        assert(4 * remaining + 1 - 1 >= 1) by(nonlinear_arith) requires remaining > 0;
        lemma_run_unfold_step(m, c1, (4 * remaining + 1 - 1) as nat);
        let c2 = step(m, c1).unwrap();
        assert(!is_halted(m, c2));
        assert(4 * remaining + 1 - 2 >= 1) by(nonlinear_arith) requires remaining > 0;
        lemma_run_unfold_step(m, c2, (4 * remaining + 1 - 2) as nat);
        let c3 = step(m, c2).unwrap();
        assert(!is_halted(m, c3));
        assert(4 * remaining + 1 - 3 >= 1) by(nonlinear_arith) requires remaining > 0;
        lemma_run_unfold_step(m, c3, (4 * remaining + 1 - 3) as nat);
        let c4 = step(m, c3).unwrap();
        assert(c4.pc == start_pc);
        assert(c4.registers[src as int] == (remaining - 1) as nat);
        assert(c4.registers[d1 as int] == acc + 1);
        assert(c4.registers[d2 as int] == acc + 1);
        assert(c4.registers[scratch as int] == 0);
        assert((4 * remaining + 1 - 4) as nat == (4 * ((remaining - 1) as nat) + 1) as nat) by(nonlinear_arith)
            requires remaining > 0;
        lemma_double_dist_inner(m, c4, src, d1, d2, scratch, start_pc,
            orig_val, acc + 1, (remaining - 1) as nat);
        assert forall|r: int| 0 <= r < m.num_regs as int
            && r != src as int && r != d1 as int && r != d2 as int
        implies run(m, c, 4 * remaining + 1).registers[r] == c.registers[r]
        by {
            assert(c4.registers[r] == c.registers[r]);
        };
    }
}

} //  verus!
