use vstd::prelude::*;
use crate::machine::*;

verus! {

//  ============================================================
//  Helper: connect run(m, c, fuel) with step when fuel == 1
//  ============================================================

///  When !is_halted and fuel > 0, run(m, c, fuel) == run(m, step(m, c).unwrap(), fuel - 1).
///  This is a direct consequence of the run definition, but z3 needs help unfolding
///  when the fuel expression involves nonlinear arithmetic (e.g. 5 * 0 + 1).
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
//  Instruction constructors (avoids struct literal parsing issues in requires)
//  ============================================================

pub open spec fn mk_inc(r: nat) -> Instruction {
    Instruction::Inc { register: r }
}

pub open spec fn mk_dj(r: nat, t: nat) -> Instruction {
    Instruction::DecJump { register: r, target: t }
}

//  ============================================================
//  Instruction primitives
//  ============================================================

///  Shift register indices and PC offsets in an instruction sequence.
///  Halts are replaced with DecJump{scratch, halt_target} (unconditional jump).
pub open spec fn embed_instructions(
    instrs: Seq<Instruction>,
    reg_offset: nat,
    pc_offset: nat,
    halt_target: nat,
    scratch_reg: nat,
) -> Seq<Instruction> {
    Seq::new(instrs.len(), |i: int| match instrs[i] {
        Instruction::Inc { register } =>
            Instruction::Inc { register: register + reg_offset },
        Instruction::DecJump { register, target } =>
            Instruction::DecJump { register: register + reg_offset, target: target + pc_offset },
        Instruction::Halt =>
            Instruction::DecJump { register: scratch_reg, target: halt_target },
    })
}

///  Destructive copy: src → dst (dst must start at 0, src becomes 0).
///  3 instructions starting at start_pc. Next instruction at start_pc + 3.
pub open spec fn copy_instrs(
    src: nat, dst: nat, scratch: nat, start_pc: nat,
) -> Seq<Instruction> {
    seq![
        Instruction::DecJump { register: src, target: start_pc + 3 },
        Instruction::Inc { register: dst },
        Instruction::DecJump { register: scratch, target: start_pc },
    ]
}

///  Triple distribute: src → (d1, d2, d3) simultaneously (src destroyed).
///  5 instructions starting at start_pc. Next instruction at start_pc + 5.
pub open spec fn triple_dist_instrs(
    src: nat, d1: nat, d2: nat, d3: nat, scratch: nat, start_pc: nat,
) -> Seq<Instruction> {
    seq![
        Instruction::DecJump { register: src, target: start_pc + 5 },
        Instruction::Inc { register: d1 },
        Instruction::Inc { register: d2 },
        Instruction::Inc { register: d3 },
        Instruction::DecJump { register: scratch, target: start_pc },
    ]
}

//  ============================================================
//  Embedded machine configuration agreement
//  ============================================================

pub open spec fn embed_configs_agree(
    rm_sub: RegisterMachine,
    reg_offset: nat,
    pc_offset: nat,
    scratch: nat,
    c_sub: Configuration,
    c: Configuration,
) -> bool {
    c.pc == c_sub.pc + pc_offset &&
    c_sub.registers.len() == rm_sub.num_regs &&
    (forall|r: int| 0 <= r < rm_sub.num_regs as int ==>
        c.registers[(r + reg_offset) as int] == c_sub.registers[r]) &&
    c.registers[scratch as int] == 0
}

//  ============================================================
//  Triple distribute loop proof
//  ============================================================

#[verifier::rlimit(1000)]
pub proof fn lemma_triple_dist_inner(
    m: RegisterMachine,
    c: Configuration,
    src: nat, d1: nat, d2: nat, d3: nat, scratch: nat,
    start_pc: nat,
    orig_val: nat, acc: nat, remaining: nat,
)
    requires
        start_pc + 5 <= m.instructions.len(),
        m.instructions[start_pc as int] == mk_dj(src, start_pc + 5),
        m.instructions[(start_pc + 1) as int] == mk_inc(d1),
        m.instructions[(start_pc + 2) as int] == mk_inc(d2),
        m.instructions[(start_pc + 3) as int] == mk_inc(d3),
        m.instructions[(start_pc + 4) as int] == mk_dj(scratch, start_pc),
        c.pc == start_pc,
        c.registers.len() == m.num_regs,
        c.registers[src as int] == remaining,
        c.registers[d1 as int] == acc,
        c.registers[d2 as int] == acc,
        c.registers[d3 as int] == acc,
        c.registers[scratch as int] == 0,
        src < m.num_regs, d1 < m.num_regs, d2 < m.num_regs,
        d3 < m.num_regs, scratch < m.num_regs,
        src != d1, src != d2, src != d3, src != scratch,
        d1 != d2, d1 != d3, d1 != scratch,
        d2 != d3, d2 != scratch, d3 != scratch,
        acc + remaining == orig_val,
    ensures
        run(m, c, 5 * remaining + 1).pc == start_pc + 5,
        run(m, c, 5 * remaining + 1).registers[src as int] == 0,
        run(m, c, 5 * remaining + 1).registers[d1 as int] == orig_val,
        run(m, c, 5 * remaining + 1).registers[d2 as int] == orig_val,
        run(m, c, 5 * remaining + 1).registers[d3 as int] == orig_val,
        run(m, c, 5 * remaining + 1).registers[scratch as int] == 0,
        forall|r: int| 0 <= r < m.num_regs as int
            && r != src as int && r != d1 as int && r != d2 as int && r != d3 as int
            ==> run(m, c, 5 * remaining + 1).registers[r] == c.registers[r],
    decreases remaining,
{
    if remaining == 0 {
        assert(5 * remaining + 1 > 0) by(nonlinear_arith)
            requires remaining == 0;
        assert(!is_halted(m, c));
        lemma_run_unfold_step(m, c, 5 * remaining + 1);
        let c1 = step(m, c).unwrap();
        assert(c1.pc == start_pc + 5);
        assert(c1.registers == c.registers);
        assert((5 * remaining + 1 - 1) as nat == 0nat) by(nonlinear_arith)
            requires remaining == 0;
        assert(run(m, c1, (5 * remaining + 1 - 1) as nat) == c1);
        assert(run(m, c, 5 * remaining + 1) == c1);
        assert(run(m, c, 5 * remaining + 1).pc == start_pc + 5);
        assert(run(m, c, 5 * remaining + 1).registers =~= c.registers);
    } else {
        assert(!is_halted(m, c));
        lemma_run_unfold_step(m, c, 5 * remaining + 1);
        let c1 = step(m, c).unwrap();
        assert(!is_halted(m, c1));
        assert(5 * remaining + 1 - 1 >= 1) by(nonlinear_arith) requires remaining > 0;
        lemma_run_unfold_step(m, c1, (5 * remaining + 1 - 1) as nat);
        let c2 = step(m, c1).unwrap();
        assert(!is_halted(m, c2));
        assert(5 * remaining + 1 - 2 >= 1) by(nonlinear_arith) requires remaining > 0;
        lemma_run_unfold_step(m, c2, (5 * remaining + 1 - 2) as nat);
        let c3 = step(m, c2).unwrap();
        assert(!is_halted(m, c3));
        assert(5 * remaining + 1 - 3 >= 1) by(nonlinear_arith) requires remaining > 0;
        lemma_run_unfold_step(m, c3, (5 * remaining + 1 - 3) as nat);
        let c4 = step(m, c3).unwrap();
        assert(!is_halted(m, c4));
        assert(5 * remaining + 1 - 4 >= 1) by(nonlinear_arith) requires remaining > 0;
        lemma_run_unfold_step(m, c4, (5 * remaining + 1 - 4) as nat);
        let c5 = step(m, c4).unwrap();
        assert(c5.pc == start_pc);
        assert(c5.registers[src as int] == (remaining - 1) as nat);
        assert(c5.registers[d1 as int] == acc + 1);
        assert(c5.registers[d2 as int] == acc + 1);
        assert(c5.registers[d3 as int] == acc + 1);
        assert(c5.registers[scratch as int] == 0);
        assert((5 * remaining + 1 - 5) as nat == (5 * ((remaining - 1) as nat) + 1) as nat) by(nonlinear_arith)
            requires remaining > 0;
        lemma_triple_dist_inner(m, c5, src, d1, d2, d3, scratch,
            start_pc, orig_val, acc + 1, (remaining - 1) as nat);
        //  Help z3 with register preservation through the 5 steps
        assert forall|r: int| 0 <= r < m.num_regs as int
            && r != src as int && r != d1 as int && r != d2 as int && r != d3 as int
        implies run(m, c, 5 * remaining + 1).registers[r] == c.registers[r]
        by {
            assert(c5.registers[r] == c.registers[r]);
        };
    }
}

//  ============================================================
//  Destructive copy loop proof
//  ============================================================

#[verifier::rlimit(1000)]
pub proof fn lemma_copy_loop_inner(
    m: RegisterMachine,
    c: Configuration,
    src: nat, dst: nat, scratch: nat,
    start_pc: nat,
    orig_val: nat, acc: nat, remaining: nat,
)
    requires
        start_pc + 3 <= m.instructions.len(),
        m.instructions[start_pc as int] == mk_dj(src, start_pc + 3),
        m.instructions[(start_pc + 1) as int] == mk_inc(dst),
        m.instructions[(start_pc + 2) as int] == mk_dj(scratch, start_pc),
        c.pc == start_pc,
        c.registers.len() == m.num_regs,
        c.registers[src as int] == remaining,
        c.registers[dst as int] == acc,
        c.registers[scratch as int] == 0,
        src < m.num_regs, dst < m.num_regs, scratch < m.num_regs,
        src != dst, src != scratch, dst != scratch,
        acc + remaining == orig_val,
    ensures
        run(m, c, 3 * remaining + 1).pc == start_pc + 3,
        run(m, c, 3 * remaining + 1).registers[dst as int] == orig_val,
        run(m, c, 3 * remaining + 1).registers[src as int] == 0,
        run(m, c, 3 * remaining + 1).registers[scratch as int] == 0,
        forall|r: int| 0 <= r < m.num_regs as int && r != src as int && r != dst as int
            ==> run(m, c, 3 * remaining + 1).registers[r] == c.registers[r],
    decreases remaining,
{
    if remaining == 0 {
        assert(3 * remaining + 1 > 0) by(nonlinear_arith)
            requires remaining == 0;
        assert(!is_halted(m, c));
        lemma_run_unfold_step(m, c, 3 * remaining + 1);
        let c1 = step(m, c).unwrap();
        assert(c1.pc == start_pc + 3);
        assert(c1.registers == c.registers);
        assert((3 * remaining + 1 - 1) as nat == 0nat) by(nonlinear_arith)
            requires remaining == 0;
        assert(run(m, c1, (3 * remaining + 1 - 1) as nat) == c1);
        assert(run(m, c, 3 * remaining + 1) == c1);
        assert(run(m, c, 3 * remaining + 1).pc == start_pc + 3);
        assert(run(m, c, 3 * remaining + 1).registers =~= c.registers);
    } else {
        assert(!is_halted(m, c));
        lemma_run_unfold_step(m, c, 3 * remaining + 1);
        let c1 = step(m, c).unwrap();
        assert(!is_halted(m, c1));
        assert(3 * remaining + 1 - 1 >= 1) by(nonlinear_arith) requires remaining > 0;
        lemma_run_unfold_step(m, c1, (3 * remaining + 1 - 1) as nat);
        let c2 = step(m, c1).unwrap();
        assert(!is_halted(m, c2));
        assert(3 * remaining + 1 - 2 >= 1) by(nonlinear_arith) requires remaining > 0;
        lemma_run_unfold_step(m, c2, (3 * remaining + 1 - 2) as nat);
        let c3 = step(m, c2).unwrap();
        assert(c3.pc == start_pc);
        assert(c3.registers[src as int] == (remaining - 1) as nat);
        assert(c3.registers[dst as int] == acc + 1);
        assert(c3.registers[scratch as int] == 0);
        assert((3 * remaining + 1 - 3) as nat == (3 * ((remaining - 1) as nat) + 1) as nat) by(nonlinear_arith)
            requires remaining > 0;
        lemma_copy_loop_inner(m, c3, src, dst, scratch, start_pc,
            orig_val, acc + 1, (remaining - 1) as nat);
        //  Help z3 with register preservation through the 3 steps
        assert forall|r: int| 0 <= r < m.num_regs as int && r != src as int && r != dst as int
        implies run(m, c, 3 * remaining + 1).registers[r] == c.registers[r]
        by {
            assert(c3.registers[r] == c.registers[r]);
        };
    }
}

//  ============================================================
//  Embedded machine simulation
//  ============================================================

pub proof fn lemma_embed_step_sim(
    rm_sub: RegisterMachine,
    m: RegisterMachine,
    reg_offset: nat,
    pc_offset: nat,
    halt_target: nat,
    scratch: nat,
    c_sub: Configuration,
    c: Configuration,
)
    requires
        machine_wf(rm_sub),
        config_wf(rm_sub, c_sub),
        !is_halted(rm_sub, c_sub),
        embed_configs_agree(rm_sub, reg_offset, pc_offset, scratch, c_sub, c),
        c.registers.len() == m.num_regs,
        forall|i: int| 0 <= i < rm_sub.instructions.len() ==>
            m.instructions[(i + pc_offset) as int] ==
                embed_instructions(rm_sub.instructions, reg_offset, pc_offset, halt_target, scratch)[i],
        reg_offset + rm_sub.num_regs <= m.num_regs,
        scratch < m.num_regs,
        scratch < reg_offset || scratch >= reg_offset + rm_sub.num_regs,
        pc_offset + rm_sub.instructions.len() <= m.instructions.len(),
    ensures
        step(rm_sub, c_sub) is Some,
        step(m, c) is Some,
        embed_configs_agree(
            rm_sub, reg_offset, pc_offset, scratch,
            step(rm_sub, c_sub).unwrap(),
            step(m, c).unwrap(),
        ),
        step(m, c).unwrap().registers.len() == m.num_regs,
        config_wf(rm_sub, step(rm_sub, c_sub).unwrap()),
{
    reveal(machine_wf);
    let pc = c_sub.pc;
    let instr = rm_sub.instructions[pc as int];
    let m_instr = m.instructions[c.pc as int];
    assert(m_instr == embed_instructions(
        rm_sub.instructions, reg_offset, pc_offset, halt_target, scratch)[pc as int]);
    let s_sub = step(rm_sub, c_sub).unwrap();
    let s_m = step(m, c).unwrap();
    match instr {
        Instruction::Inc { register: r } => {
            assert(m_instr == mk_inc(r + reg_offset));
            assert forall|j: int| 0 <= j < rm_sub.num_regs as int implies
                s_m.registers[(j + reg_offset) as int] == s_sub.registers[j]
            by {
                if j == r as int {
                    assert(c.registers[(j + reg_offset) as int] == c_sub.registers[j]);
                }
            };
            assert(s_m.registers[scratch as int] == 0) by {
                assert((r + reg_offset) != scratch);
            };
        },
        Instruction::DecJump { register: r, target: t } => {
            assert(m_instr == mk_dj(r + reg_offset, t + pc_offset));
            assert(c.registers[(r + reg_offset) as int] == c_sub.registers[r as int]);
            assert forall|j: int| 0 <= j < rm_sub.num_regs as int implies
                s_m.registers[(j + reg_offset) as int] == s_sub.registers[j]
            by {
                if c_sub.registers[r as int] > 0 && j == r as int {
                    assert(c.registers[(j + reg_offset) as int] == c_sub.registers[j]);
                }
            };
            assert(s_m.registers[scratch as int] == 0) by {
                if c_sub.registers[r as int] > 0 { assert((r + reg_offset) != scratch); }
            };
        },
        Instruction::Halt => { assert(false); },
    }
}

#[verifier::rlimit(500)]
pub proof fn lemma_embed_reaches_target(
    rm_sub: RegisterMachine,
    m: RegisterMachine,
    reg_offset: nat,
    pc_offset: nat,
    halt_target: nat,
    scratch: nat,
    c_sub: Configuration,
    c: Configuration,
    fuel: nat,
)
    requires
        machine_wf(rm_sub),
        config_wf(rm_sub, c_sub),
        embed_configs_agree(rm_sub, reg_offset, pc_offset, scratch, c_sub, c),
        c.registers.len() == m.num_regs,
        run_halts(rm_sub, c_sub, fuel),
        forall|i: int| 0 <= i < rm_sub.instructions.len() ==>
            m.instructions[(i + pc_offset) as int] ==
                embed_instructions(rm_sub.instructions, reg_offset, pc_offset, halt_target, scratch)[i],
        reg_offset + rm_sub.num_regs <= m.num_regs,
        scratch < m.num_regs,
        scratch < reg_offset || scratch >= reg_offset + rm_sub.num_regs,
        pc_offset + rm_sub.instructions.len() <= m.instructions.len(),
        halt_target <= m.instructions.len(),
        halt_target == pc_offset + rm_sub.instructions.len(),
    ensures ({
        let c_sub_halt = run(rm_sub, c_sub, fuel);
        exists|g: nat| g <= fuel + 1 &&
            run(m, c, g).pc == halt_target &&
            (forall|r: int| 0 <= r < rm_sub.num_regs as int ==>
                run(m, c, g).registers[(r + reg_offset) as int] == c_sub_halt.registers[r]) &&
            run(m, c, g).registers[scratch as int] == 0 &&
            run(m, c, g).registers.len() == m.num_regs
    }),
    decreases fuel,
{
    reveal(machine_wf);
    let n = rm_sub.instructions.len();
    if is_halted(rm_sub, c_sub) {
        lemma_halted_run_identity(rm_sub, c_sub, fuel);
        let c_sub_halt = run(rm_sub, c_sub, fuel);
        if c_sub.pc >= n {
            assert(c_sub.pc == n);
            assert(c.pc == halt_target);
            //  Witness g = 0: run(m, c, 0) == c, c.pc == halt_target
            let g: nat = 0;
            assert(run(m, c, g).pc == halt_target);
            assert(forall|r: int| 0 <= r < rm_sub.num_regs as int ==>
                run(m, c, g).registers[(r + reg_offset) as int] == c_sub_halt.registers[r]);
            assert(run(m, c, g).registers[scratch as int] == 0);
            assert(run(m, c, g).registers.len() == m.num_regs);
        } else {
            assert(rm_sub.instructions[c_sub.pc as int] is Halt);
            let embedded = embed_instructions(
                rm_sub.instructions, reg_offset, pc_offset, halt_target, scratch);
            assert(m.instructions[c.pc as int] == embedded[c_sub.pc as int]);
            assert(m.instructions[c.pc as int] == mk_dj(scratch, halt_target));
            assert(!is_halted(m, c));
            let next = step(m, c).unwrap();
            assert(next.pc == halt_target);
            assert(next.registers == c.registers);
            //  Witness g = 1: run(m, c, 1) == next
            lemma_run_unfold_step(m, c, 1);
            assert(run(m, c, 1) == run(m, next, 0));
            assert(run(m, next, 0) == next);
            let g: nat = 1;
            assert(run(m, c, g).pc == halt_target);
            assert(forall|r: int| 0 <= r < rm_sub.num_regs as int ==>
                run(m, c, g).registers[(r + reg_offset) as int] == c_sub_halt.registers[r]);
            assert(run(m, c, g).registers[scratch as int] == 0);
            assert(run(m, c, g).registers.len() == m.num_regs);
        }
    } else {
        assert(fuel > 0);
        lemma_embed_step_sim(rm_sub, m, reg_offset, pc_offset, halt_target, scratch, c_sub, c);
        let s_sub = step(rm_sub, c_sub).unwrap();
        let s_m = step(m, c).unwrap();
        lemma_embed_reaches_target(rm_sub, m, reg_offset, pc_offset, halt_target, scratch,
            s_sub, s_m, (fuel - 1) as nat);
        let c_sub_halt = run(rm_sub, s_sub, (fuel - 1) as nat);
        let g_inner: nat = choose|g: nat| g <= fuel &&
            run(m, s_m, g).pc == halt_target &&
            (forall|r: int| 0 <= r < rm_sub.num_regs as int ==>
                run(m, s_m, g).registers[(r + reg_offset) as int] == c_sub_halt.registers[r]) &&
            run(m, s_m, g).registers[scratch as int] == 0 &&
            run(m, s_m, g).registers.len() == m.num_regs;
        assert(run(m, c, g_inner + 1) == run(m, s_m, g_inner));
        assert(run(rm_sub, c_sub, fuel) == c_sub_halt);
    }
}

//  ============================================================
//  Fuel composition helper
//  ============================================================

///  If the machine is not halted after `fuel` steps, it never halted.
pub proof fn lemma_not_halted_means_not_run_halts(
    m: RegisterMachine,
    c: Configuration,
    fuel: nat,
)
    requires
        !is_halted(m, run(m, c, fuel)),
    ensures
        !run_halts(m, c, fuel),
    decreases fuel,
{
    if fuel == 0 {
    } else {
        if is_halted(m, c) {
            lemma_halted_run_identity(m, c, fuel);
        } else {
            let next = step(m, c).unwrap();
            lemma_not_halted_means_not_run_halts(m, next, (fuel - 1) as nat);
        }
    }
}

} //  verus!
