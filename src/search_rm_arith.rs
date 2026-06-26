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
use crate::multi_output_primitives::{mk_inc, mk_dj, lemma_copy_loop_inner};
use crate::pairing::triangular;

verus! {

//  ============================================================
//  run unfolding helpers (private copies)
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

///  Run-composition: `run(m,c,a+b) == run(m, run(m,c,a), b)`.
pub proof fn lemma_run_add(m: RegisterMachine, c: Configuration, a: nat, b: nat)
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

///  `run` preserves the register-count (every `step` is length-preserving).
pub proof fn lemma_run_preserves_len(m: RegisterMachine, c: Configuration, fuel: nat)
    ensures
        run(m, c, fuel).registers.len() == c.registers.len(),
    decreases fuel,
{
    if fuel > 0 {
        match step(m, c) {
            Some(next) => {
                assert(next.registers.len() == c.registers.len());
                lemma_run_preserves_len(m, next, (fuel - 1) as nat);
            },
            None => {},
        }
    }
}

///  The triangular recurrence `T(k+1) == T(k) + k + 1` (local re-proof; pairing's is private).
proof fn lemma_tri_step(n: nat)
    ensures
        triangular(n + 1) == triangular(n) + n + 1,
{
    assert((n + 1) * (n + 2) == n * (n + 1) + 2 * (n + 1)) by(nonlinear_arith);
    assert(((n + 1) * (n + 2)) / 2 == (n * (n + 1)) / 2 + (n + 1)) by(nonlinear_arith);
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
    acc1: nat, acc2: nat, remaining: nat,
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
        c.registers[d1 as int] == acc1,
        c.registers[d2 as int] == acc2,
        c.registers[scratch as int] == 0,
        src < m.num_regs, d1 < m.num_regs, d2 < m.num_regs, scratch < m.num_regs,
        src != d1, src != d2, src != scratch,
        d1 != d2, d1 != scratch, d2 != scratch,
    ensures
        run(m, c, 4 * remaining + 1).pc == start_pc + 4,
        run(m, c, 4 * remaining + 1).registers[src as int] == 0,
        run(m, c, 4 * remaining + 1).registers[d1 as int] == acc1 + remaining,
        run(m, c, 4 * remaining + 1).registers[d2 as int] == acc2 + remaining,
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
        assert(c4.registers[d1 as int] == acc1 + 1);
        assert(c4.registers[d2 as int] == acc2 + 1);
        assert(c4.registers[scratch as int] == 0);
        assert((4 * remaining + 1 - 4) as nat == (4 * ((remaining - 1) as nat) + 1) as nat) by(nonlinear_arith)
            requires remaining > 0;
        lemma_double_dist_inner(m, c4, src, d1, d2, scratch, start_pc,
            acc1 + 1, acc2 + 1, (remaining - 1) as nat);
        assert(acc1 + 1 + (remaining - 1) == acc1 + remaining);
        assert(acc2 + 1 + (remaining - 1) == acc2 + remaining);
        assert forall|r: int| 0 <= r < m.num_regs as int
            && r != src as int && r != d1 as int && r != d2 as int
        implies run(m, c, 4 * remaining + 1).registers[r] == c.registers[r]
        by {
            assert(c4.registers[r] == c.registers[r]);
        };
    }
}

//  ============================================================
//  Triangular accumulation loop:  t := triangular(n)
//  ============================================================
//
//  The 10-instruction outer loop body (at `start_pc`), draining `nc` (a countdown copy of n) while
//  growing `i` and accumulating `t = triangular(i)`. The inner "t += i preserving i" is
//  `copy(i→ibak)` then `double_dist(ibak→t,i)`. `zero` is a guaranteed-0 register reused for every
//  back-edge.
//
//    +0  DecJump{nc,   start_pc+10}   guard: nc==0 ⇒ EXIT; else nc--, fall
//    +1  Inc{i}                        i++
//    +2  DecJump{i,    start_pc+5}     ┐ copy_instrs(i → ibak, scratch=zero, start_pc+2)
//    +3  Inc{ibak}                     │
//    +4  DecJump{zero, start_pc+2}     ┘
//    +5  DecJump{ibak, start_pc+9}     ┐ double_dist_instrs(ibak → t,i, scratch=zero, start_pc+5)
//    +6  Inc{t}                        │
//    +7  Inc{i}                        │
//    +8  DecJump{zero, start_pc+5}     ┘
//    +9  DecJump{zero, start_pc}       outer back-edge ⇒ TOP

pub open spec fn triangular_loop_instrs(
    nc: nat, i: nat, t: nat, ibak: nat, zero: nat, start_pc: nat,
) -> Seq<Instruction> {
    seq![
        Instruction::DecJump { register: nc,   target: start_pc + 10 },
        Instruction::Inc     { register: i },
        Instruction::DecJump { register: i,    target: start_pc + 5 },
        Instruction::Inc     { register: ibak },
        Instruction::DecJump { register: zero, target: start_pc + 2 },
        Instruction::DecJump { register: ibak, target: start_pc + 9 },
        Instruction::Inc     { register: t },
        Instruction::Inc     { register: i },
        Instruction::DecJump { register: zero, target: start_pc + 5 },
        Instruction::DecJump { register: zero, target: start_pc },
    ]
}

///  Side-condition bundle: the 10 instructions are laid out at `start_pc`, the loop registers are
///  distinct and in bounds.
pub open spec fn triangular_loop_frame(
    m: RegisterMachine, nc: nat, i: nat, t: nat, ibak: nat, zero: nat, start_pc: nat,
) -> bool {
    &&& start_pc + 10 <= m.instructions.len()
    &&& m.instructions[start_pc as int]       == mk_dj(nc, start_pc + 10)
    &&& m.instructions[(start_pc + 1) as int]  == mk_inc(i)
    &&& m.instructions[(start_pc + 2) as int]  == mk_dj(i, start_pc + 5)
    &&& m.instructions[(start_pc + 3) as int]  == mk_inc(ibak)
    &&& m.instructions[(start_pc + 4) as int]  == mk_dj(zero, start_pc + 2)
    &&& m.instructions[(start_pc + 5) as int]  == mk_dj(ibak, start_pc + 9)
    &&& m.instructions[(start_pc + 6) as int]  == mk_inc(t)
    &&& m.instructions[(start_pc + 7) as int]  == mk_inc(i)
    &&& m.instructions[(start_pc + 8) as int]  == mk_dj(zero, start_pc + 5)
    &&& m.instructions[(start_pc + 9) as int]  == mk_dj(zero, start_pc)
    &&& nc < m.num_regs && i < m.num_regs && t < m.num_regs
        && ibak < m.num_regs && zero < m.num_regs
    &&& nc != i && nc != t && nc != ibak && nc != zero
    &&& i != t && i != ibak && i != zero
    &&& t != ibak && t != zero
    &&& ibak != zero
}

///  From the loop top with `nc = remaining`, `i = k`, `t = triangular(k)`, the loop runs to EXIT
///  (`start_pc + 10`) with `t = triangular(k + remaining)`, `i = k + remaining`, `nc = 0`.
#[verifier::rlimit(6000)]
pub proof fn lemma_triangular_loop(
    m: RegisterMachine, c: Configuration,
    nc: nat, i: nat, t: nat, ibak: nat, zero: nat, start_pc: nat,
    k: nat, remaining: nat,
)
    requires
        triangular_loop_frame(m, nc, i, t, ibak, zero, start_pc),
        c.pc == start_pc,
        c.registers.len() == m.num_regs,
        c.registers[nc as int] == remaining,
        c.registers[i as int] == k,
        c.registers[t as int] == triangular(k),
        c.registers[ibak as int] == 0,
        c.registers[zero as int] == 0,
    ensures
        exists|g: nat|
            run(m, c, g).pc == start_pc + 10
            && #[trigger] run(m, c, g).registers[t as int] == triangular(k + remaining)
            && run(m, c, g).registers[i as int] == k + remaining
            && run(m, c, g).registers[nc as int] == 0
            && run(m, c, g).registers[ibak as int] == 0
            && run(m, c, g).registers[zero as int] == 0
            && run(m, c, g).registers.len() == m.num_regs
            && (forall|r: int| 0 <= r < m.num_regs as int
                    && r != nc as int && r != i as int && r != t as int && r != ibak as int
                    ==> #[trigger] run(m, c, g).registers[r] == c.registers[r]),
    decreases remaining,
{
    if remaining == 0 {
        //  guard: nc == 0 ⇒ jump to EXIT, registers unchanged
        assert(c.pc < m.instructions.len());
        assert(m.instructions[c.pc as int] == mk_dj(nc, start_pc + 10));
        assert(c.registers[nc as int] == 0);
        assert(!is_halted(m, c));
        let c1 = step(m, c).unwrap();
        assert(c1.pc == start_pc + 10);
        assert(c1.registers == c.registers);
        lemma_run_unfold_step(m, c, 1);
        assert(run(m, c, 1) == c1);
        let g: nat = 1;
        assert(run(m, c, g).registers[t as int] == triangular(k + remaining));
        assert(forall|r: int| 0 <= r < m.num_regs as int
            && r != nc as int && r != i as int && r != t as int && r != ibak as int
            ==> run(m, c, g).registers[r] == c.registers[r]);
    } else {
        //  --- slot 0: DecJump{nc, EXIT}, nc > 0 ⇒ nc--, fall to start_pc+1 ---
        assert(m.instructions[c.pc as int] == mk_dj(nc, start_pc + 10));
        assert(c.registers[nc as int] == remaining && remaining > 0);
        assert(!is_halted(m, c));
        let c0 = step(m, c).unwrap();
        assert(c0.pc == start_pc + 1);
        assert(c0.registers == c.registers.update(nc as int, (remaining - 1) as nat));

        //  --- slot 1: Inc{i}, i: k → k+1, fall to start_pc+2 ---
        assert(m.instructions[c0.pc as int] == mk_inc(i));
        assert(!is_halted(m, c0));
        let c2 = step(m, c0).unwrap();
        assert(c2.pc == start_pc + 2);
        assert(c2.registers == c0.registers.update(i as int, k + 1));
        assert(c2.registers[i as int] == k + 1);
        assert(c2.registers[ibak as int] == 0);
        assert(c2.registers[zero as int] == 0);
        assert(c2.registers[t as int] == triangular(k));
        assert(c2.registers[nc as int] == (remaining - 1) as nat);
        assert(c2.registers.len() == m.num_regs);
        lemma_run_unfold_step(m, c, 2);
        lemma_run_unfold_step(m, c0, 1);
        assert(run(m, c, 2) == c2);

        //  --- copy_instrs(i → ibak, scratch=zero, start_pc+2): 3*(k+1)+1 steps ---
        lemma_copy_loop_inner(m, c2, i, ibak, zero, start_pc + 2, k + 1, 0, k + 1);
        let cps: nat = (3 * (k + 1) + 1) as nat;
        let c3 = run(m, c2, cps);
        assert(c3.pc == start_pc + 5);
        assert(c3.registers[ibak as int] == k + 1);
        assert(c3.registers[i as int] == 0);
        assert(c3.registers[zero as int] == 0);
        //  t, nc preserved by copy (r != i, r != ibak)
        assert(c3.registers[t as int] == triangular(k)) by { assert(t != i && t != ibak); }
        assert(c3.registers[nc as int] == (remaining - 1) as nat) by { assert(nc != i && nc != ibak); }
        lemma_run_preserves_len(m, c2, cps);
        assert(c3.registers.len() == m.num_regs);

        //  --- double_dist(ibak → t, i, scratch=zero, start_pc+5): 4*(k+1)+1 steps ---
        lemma_double_dist_inner(m, c3, ibak, t, i, zero, start_pc + 5, triangular(k), 0, k + 1);
        let dds: nat = (4 * (k + 1) + 1) as nat;
        let c4 = run(m, c3, dds);
        assert(c4.pc == start_pc + 9);
        assert(c4.registers[ibak as int] == 0);
        assert(c4.registers[t as int] == triangular(k) + (k + 1));
        assert(c4.registers[i as int] == 0 + (k + 1));
        assert(c4.registers[zero as int] == 0) by { assert(zero != ibak && zero != t && zero != i); }
        assert(c4.registers[nc as int] == (remaining - 1) as nat) by { assert(nc != ibak && nc != t && nc != i); }
        lemma_run_preserves_len(m, c3, dds);
        assert(c4.registers.len() == m.num_regs);
        lemma_tri_step(k);
        assert(c4.registers[t as int] == triangular(k + 1));

        //  --- slot 9: DecJump{zero, TOP}, zero == 0 ⇒ jump to start_pc, registers unchanged ---
        assert(m.instructions[c4.pc as int] == mk_dj(zero, start_pc));
        assert(!is_halted(m, c4));
        let c5 = step(m, c4).unwrap();
        assert(c5.pc == start_pc);
        assert(c5.registers == c4.registers);
        lemma_run_unfold_step(m, c4, 1);
        assert(run(m, c4, 1) == c5);
        assert(c5.registers[nc as int] == (remaining - 1) as nat);
        assert(c5.registers[i as int] == k + 1);
        assert(c5.registers[t as int] == triangular(k + 1));
        assert(c5.registers[ibak as int] == 0);
        assert(c5.registers[zero as int] == 0);

        //  --- recurse from c5 (k+1, remaining-1) ---
        let rem1: nat = (remaining - 1) as nat;
        lemma_triangular_loop(m, c5, nc, i, t, ibak, zero, start_pc, k + 1, rem1);
        let g_inner = choose|g: nat|
            run(m, c5, g).pc == start_pc + 10
            && run(m, c5, g).registers[t as int] == triangular((k + 1) + rem1)
            && run(m, c5, g).registers[i as int] == (k + 1) + rem1
            && run(m, c5, g).registers[nc as int] == 0
            && run(m, c5, g).registers[ibak as int] == 0
            && run(m, c5, g).registers[zero as int] == 0
            && run(m, c5, g).registers.len() == m.num_regs
            && (forall|r: int| 0 <= r < m.num_regs as int
                    && r != nc as int && r != i as int && r != t as int && r != ibak as int
                    ==> #[trigger] run(m, c5, g).registers[r] == c5.registers[r]);

        //  --- chain the run segments:  run(m,c,g) == run(m,c5,g_inner) ---
        //  c2 = run(m,c,2); c3 = run(m,c2,cps); c4 = run(m,c3,dds); c5 = run(m,c4,1).
        lemma_run_add(m, c4, 1, g_inner);
        lemma_run_add(m, c3, dds, (1 + g_inner) as nat);
        lemma_run_add(m, c2, cps, (dds + 1 + g_inner) as nat);
        lemma_run_add(m, c, 2, (cps + dds + 1 + g_inner) as nat);
        let g: nat = (2 + cps + dds + 1 + g_inner) as nat;
        assert(run(m, c, g) == run(m, c5, g_inner));
        assert((k + 1) + rem1 == k + remaining);

        //  frame: out-of-{nc,i,t,ibak} regs of run(m,c,g) == c5's == ... == c's
        assert forall|r: int| 0 <= r < m.num_regs as int
            && r != nc as int && r != i as int && r != t as int && r != ibak as int
        implies #[trigger] run(m, c, g).registers[r] == c.registers[r]
        by {
            assert(run(m, c5, g_inner).registers[r] == c5.registers[r]);
            //  c5 == c4; c4 from double_dist preserves r∉{ibak,t,i}; c3 from copy preserves r∉{i,ibak};
            //  c2 == c.update(nc).update(i); for r != nc,i: c2.registers[r] == c.registers[r].
            assert(c5.registers[r] == c4.registers[r]);
            assert(c4.registers[r] == c3.registers[r]) by { assert(r != ibak as int && r != t as int && r != i as int); }
            assert(c3.registers[r] == c2.registers[r]) by { assert(r != i as int && r != ibak as int); }
            assert(c2.registers[r] == c.registers[r]) by { assert(r != nc as int && r != i as int); }
        }
        assert(run(m, c, g).registers[t as int] == triangular(k + remaining));
    }
}

} //  verus!
