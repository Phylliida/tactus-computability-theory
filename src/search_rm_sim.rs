//  GAP-2 / L0 brick B-L0.1 — fuel-instrumented bounded simulation.
//
//  `instrument(E)` embeds a register machine `E`'s instructions into a host machine with a *fuel
//  guard* (`DecJump{fuel, TIMEOUT}`) prepended to every original instruction, so that running the
//  embedded copy always returns within `fuel` simulated steps with a verdict:
//    * reaches `halted_pc`  if `E` halts within the budget (carrying the halt config's registers), or
//    * reaches `timeout_pc` if `E` is still running after the budget.
//  This is the bounded analogue of `multi_output_primitives::lemma_embed_reaches_target` (which runs
//  an embedded sub-machine *to its halt* and so diverges on a non-halting enumerator stage). The
//  dovetail driver (B-L0.2) uses it to give each stage a finite budget without wedging the search.
//
//  Layout (the "stride-2" embedding). Original instruction `i` (at absolute pc `pc_offset + 2i`):
//    even slot `pc_offset + 2i`     : the GUARD  `DecJump{fuel_reg, timeout_pc}`
//    odd  slot `pc_offset + 2i + 1`  : the BODY   = `E.instructions[i]` with registers shifted by
//                                       `reg_offset` and DecJump targets `t` remapped to `pc_offset+2t`
//                                       (so they land on the guard of the target); `Halt` becomes
//                                       `DecJump{scratch, halted_pc}` (scratch is a guaranteed-0
//                                       register, so it is an unconditional jump to HALTED).
//  With `halted_pc = pc_offset + 2*len`, both "fall off the end" (a body falling through past the last
//  slot) and an explicit jump to `len` land on HALTED uniformly.
//
//  See docs/gap2-l0-search-rm-plan.md and docs/gap2-register-to-tm-plan.md.

use vstd::prelude::*;
use crate::machine::*;

verus! {

//  ============================================================
//  run unfolding helper (private copy of the multi_output_primitives one)
//  ============================================================

///  When `!is_halted` and `fuel > 0`, `run(m,c,fuel) == run(m, step(m,c).unwrap(), fuel-1)`.
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

//  ============================================================
//  The instrumented instruction block
//  ============================================================

///  The body for one original instruction (registers shifted by `reg_offset`, DecJump targets
///  remapped to the guard of the target `pc_offset + 2*t`, `Halt` → unconditional jump to HALTED).
pub open spec fn instrument_body(
    instr: Instruction, reg_offset: nat, pc_offset: nat, halted_pc: nat, scratch: nat,
) -> Instruction {
    match instr {
        Instruction::Inc { register } =>
            Instruction::Inc { register: register + reg_offset },
        Instruction::DecJump { register, target } =>
            Instruction::DecJump { register: register + reg_offset, target: pc_offset + 2 * target },
        Instruction::Halt =>
            Instruction::DecJump { register: scratch, target: halted_pc },
    }
}

///  The instrumented block: `2*len` instructions, guard at even slots, body at odd slots.
pub open spec fn instrument_instructions(
    instrs: Seq<Instruction>,
    reg_offset: nat, pc_offset: nat, halted_pc: nat, timeout_pc: nat,
    fuel_reg: nat, scratch: nat,
) -> Seq<Instruction> {
    Seq::new(2 * instrs.len(), |j: int|
        if j % 2 == 0 {
            Instruction::DecJump { register: fuel_reg, target: timeout_pc }
        } else {
            instrument_body(instrs[j / 2], reg_offset, pc_offset, halted_pc, scratch)
        }
    )
}

//  ============================================================
//  Configuration agreement
//  ============================================================

///  The host config `c` tracks the sub-machine config `c_sub` *at the guard* of `c_sub.pc`, with the
///  E-bank shifted by `reg_offset`, the scratch register held at 0, and `phi` units of fuel remaining.
///  (When `c_sub.pc == len`, the "guard position" is `pc_offset + 2*len == halted_pc` — i.e. a halted
///  E-config is tracked already sitting on HALTED.)
pub open spec fn instr_configs_agree(
    rm_sub: RegisterMachine,
    reg_offset: nat, pc_offset: nat, fuel_reg: nat, scratch: nat, phi: nat,
    c_sub: Configuration, c: Configuration,
) -> bool {
    &&& c.pc == pc_offset + 2 * c_sub.pc
    &&& c_sub.registers.len() == rm_sub.num_regs
    &&& (forall|r: int| 0 <= r < rm_sub.num_regs as int ==>
            c.registers[(r + reg_offset) as int] == c_sub.registers[r])
    &&& c.registers[scratch as int] == 0
    &&& c.registers[fuel_reg as int] == phi
}

///  The structural side-conditions on the host machine `m` that hold throughout the simulation
///  (layout match, bank/sink disjointness, bounds). Bundled to keep lemma signatures readable.
pub open spec fn instrument_frame(
    rm_sub: RegisterMachine, m: RegisterMachine,
    reg_offset: nat, pc_offset: nat, halted_pc: nat, timeout_pc: nat,
    fuel_reg: nat, scratch: nat,
) -> bool {
    &&& (forall|j: int| 0 <= j < 2 * rm_sub.instructions.len() ==>
            m.instructions[(pc_offset + j) as int] ==
                #[trigger] instrument_instructions(
                    rm_sub.instructions, reg_offset, pc_offset, halted_pc, timeout_pc, fuel_reg, scratch)[j])
    &&& halted_pc == pc_offset + 2 * rm_sub.instructions.len()
    &&& pc_offset + 2 * rm_sub.instructions.len() <= m.instructions.len()
    &&& reg_offset + rm_sub.num_regs <= m.num_regs
    &&& fuel_reg < m.num_regs
    &&& scratch < m.num_regs
    &&& (fuel_reg < reg_offset || fuel_reg >= reg_offset + rm_sub.num_regs)
    &&& (scratch < reg_offset || scratch >= reg_offset + rm_sub.num_regs)
    &&& fuel_reg != scratch
    &&& halted_pc != timeout_pc
}

//  ============================================================
//  One simulated E-step = guard (consume 1 fuel) + body (1 E-step) = 2 host steps
//  ============================================================

#[verifier::rlimit(2000)]
pub proof fn lemma_instrument_estep(
    rm_sub: RegisterMachine, m: RegisterMachine,
    reg_offset: nat, pc_offset: nat, halted_pc: nat, timeout_pc: nat,
    fuel_reg: nat, scratch: nat,
    c_sub: Configuration, c: Configuration, phi: nat,
)
    requires
        machine_wf(rm_sub),
        config_wf(rm_sub, c_sub),
        !is_halted(rm_sub, c_sub),
        instr_configs_agree(rm_sub, reg_offset, pc_offset, fuel_reg, scratch, phi, c_sub, c),
        phi > 0,
        c.registers.len() == m.num_regs,
        instrument_frame(rm_sub, m, reg_offset, pc_offset, halted_pc, timeout_pc, fuel_reg, scratch),
    ensures
        step(rm_sub, c_sub) is Some,
        config_wf(rm_sub, step(rm_sub, c_sub).unwrap()),
        instr_configs_agree(rm_sub, reg_offset, pc_offset, fuel_reg, scratch, (phi - 1) as nat,
            step(rm_sub, c_sub).unwrap(), run(m, c, 2)),
        run(m, c, 2).registers.len() == m.num_regs,
        forall|jj: int| 0 <= jj < m.num_regs as int
            && (jj < reg_offset || jj >= reg_offset + rm_sub.num_regs)
            && jj != fuel_reg as int && jj != scratch as int
            ==> #[trigger] run(m, c, 2).registers[jj] == c.registers[jj],
{
    reveal(machine_wf);
    let len = rm_sub.instructions.len();
    let p = c_sub.pc;            //  E pc, < len (since not halted)
    assert(p < len);
    let s_sub = step(rm_sub, c_sub).unwrap();
    lemma_step_preserves_config_wf(rm_sub, c_sub);

    let instrs_block = instrument_instructions(
        rm_sub.instructions, reg_offset, pc_offset, halted_pc, timeout_pc, fuel_reg, scratch);

    //  --- guard at pc_offset + 2p ---
    assert(2 * p < 2 * len);
    assert(m.instructions[(pc_offset + 2 * p) as int] == instrs_block[2 * p as int]);
    assert((2 * p) % 2 == 0);
    assert(instrs_block[2 * p as int] == Instruction::DecJump { register: fuel_reg, target: timeout_pc });
    assert(c.pc == pc_offset + 2 * p);
    assert(c.pc < m.instructions.len());
    assert(c.registers[fuel_reg as int] == phi && phi > 0);
    assert(fuel_reg < c.registers.len());
    assert(!is_halted(m, c));
    let c1 = step(m, c).unwrap();
    assert(c1.pc == c.pc + 1);
    assert(c1.registers == c.registers.update(fuel_reg as int, (phi - 1) as nat));
    assert(c1.registers.len() == m.num_regs);
    assert(c1.registers[fuel_reg as int] == (phi - 1) as nat);
    assert(c1.registers[scratch as int] == c.registers[scratch as int]) by {
        assert(scratch != fuel_reg);
    }
    assert forall|r: int| 0 <= r < rm_sub.num_regs as int implies
        #[trigger] c1.registers[(r + reg_offset) as int] == c.registers[(r + reg_offset) as int]
    by {
        assert((r + reg_offset) != fuel_reg as int);
    }

    //  --- body at pc_offset + 2p + 1 ---
    assert(2 * p + 1 < 2 * len);
    assert(m.instructions[(pc_offset + (2 * p + 1)) as int] == instrs_block[(2 * p + 1) as int]);
    assert((2 * p + 1) % 2 == 1);
    assert((2 * p + 1) / 2 == p as int);
    assert(instrs_block[(2 * p + 1) as int]
        == instrument_body(rm_sub.instructions[p as int], reg_offset, pc_offset, halted_pc, scratch));
    assert(c1.pc == pc_offset + 2 * p + 1);
    let body = instrument_body(rm_sub.instructions[p as int], reg_offset, pc_offset, halted_pc, scratch);
    assert(m.instructions[c1.pc as int] == body);

    let instr = rm_sub.instructions[p as int];
    let c2 = step(m, c1).unwrap();

    match instr {
        Instruction::Inc { register: r } => {
            assert(body == Instruction::Inc { register: r + reg_offset });
            assert(r < rm_sub.num_regs);
            assert(r + reg_offset < m.num_regs);
            assert(!is_halted(m, c1));
            //  E step
            assert(s_sub.pc == p + 1);
            assert(s_sub.registers == c_sub.registers.update(r as int, c_sub.registers[r as int] + 1));
            //  host step
            assert(c2.pc == c1.pc + 1);
            assert(c2.pc == pc_offset + 2 * (p + 1));
            assert(c2.registers == c1.registers.update((r + reg_offset) as int,
                c1.registers[(r + reg_offset) as int] + 1));
        },
        Instruction::DecJump { register: r, target: t } => {
            assert(body == Instruction::DecJump { register: r + reg_offset, target: pc_offset + 2 * t });
            assert(r < rm_sub.num_regs);
            assert(t <= len);
            assert(c1.registers[(r + reg_offset) as int] == c_sub.registers[r as int]) by {
                assert((r + reg_offset) != fuel_reg as int);
            }
            assert(!is_halted(m, c1));
            if c_sub.registers[r as int] > 0 {
                assert(s_sub.pc == p + 1);
                assert(c2.pc == c1.pc + 1);
                assert(c2.pc == pc_offset + 2 * (p + 1));
                assert(c2.registers == c1.registers.update((r + reg_offset) as int,
                    (c1.registers[(r + reg_offset) as int] - 1) as nat));
            } else {
                assert(s_sub.pc == t);
                assert(c2.pc == pc_offset + 2 * t);
                assert(c2.registers == c1.registers);
            }
        },
        Instruction::Halt => {
            assert(false);
        },
    }

    //  --- assemble run(m,c,2) == c2 ---
    lemma_run_unfold_step(m, c, 2);
    assert(run(m, c, 2) == run(m, c1, 1));
    lemma_run_unfold_step(m, c1, 1);
    assert(run(m, c1, 1) == run(m, c2, 0));
    assert(run(m, c2, 0) == c2);
    assert(run(m, c, 2) == c2);

    //  --- now prove the agreement + frame for c2 against s_sub ---
    assert(c2.registers.len() == m.num_regs);
    assert(c2.pc == pc_offset + 2 * s_sub.pc);
    assert(c2.registers[scratch as int] == 0) by {
        match instr {
            Instruction::Inc { register: r } => { assert((r + reg_offset) != scratch as int); },
            Instruction::DecJump { register: r, target: t } => {
                if c_sub.registers[r as int] > 0 { assert((r + reg_offset) != scratch as int); }
            },
            Instruction::Halt => { assert(false); },
        }
    }
    assert(c2.registers[fuel_reg as int] == (phi - 1) as nat) by {
        match instr {
            Instruction::Inc { register: r } => { assert((r + reg_offset) != fuel_reg as int); },
            Instruction::DecJump { register: r, target: t } => {
                if c_sub.registers[r as int] > 0 { assert((r + reg_offset) != fuel_reg as int); }
            },
            Instruction::Halt => { assert(false); },
        }
    }
    assert forall|r: int| 0 <= r < rm_sub.num_regs as int implies
        c2.registers[(r + reg_offset) as int] == s_sub.registers[r]
    by {
        match instr {
            Instruction::Inc { register: rr } => {
                if r == rr as int {
                    assert(c1.registers[(rr + reg_offset) as int] == c_sub.registers[rr as int]);
                } else {
                    assert((r + reg_offset) != (rr + reg_offset) as int);
                }
            },
            Instruction::DecJump { register: rr, target: t } => {
                if c_sub.registers[rr as int] > 0 {
                    if r == rr as int {
                        assert(c1.registers[(rr + reg_offset) as int] == c_sub.registers[rr as int]);
                    } else {
                        assert((r + reg_offset) != (rr + reg_offset) as int);
                    }
                }
            },
            Instruction::Halt => { assert(false); },
        }
    }
    //  out-of-frame preservation: c -> c1 only touched fuel_reg; c1 -> c2 only touched an in-bank reg
    assert forall|jj: int| 0 <= jj < m.num_regs as int
        && (jj < reg_offset || jj >= reg_offset + rm_sub.num_regs)
        && jj != fuel_reg as int && jj != scratch as int
    implies run(m, c, 2).registers[jj] == c.registers[jj]
    by {
        assert(c1.registers[jj] == c.registers[jj]);   //  c1 only changed fuel_reg
        match instr {
            Instruction::Inc { register: rr } => { assert(jj != (rr + reg_offset) as int); },
            Instruction::DecJump { register: rr, target: t } => {
                if c_sub.registers[rr as int] > 0 { assert(jj != (rr + reg_offset) as int); }
            },
            Instruction::Halt => { assert(false); },
        }
    }
}

//  ============================================================
//  Reaching HALTED when the tracked E-config sits on a `Halt` instruction
//  ============================================================

///  When the tracked E-config is *at a `Halt` instruction* (so E is already halted, but the host is
///  still parked on that instruction's guard), 2 host steps — guard then the `DecJump{scratch, HALTED}`
///  body — reach `halted_pc` carrying the E-config's registers unchanged.
#[verifier::rlimit(2000)]
pub proof fn lemma_instrument_halt_instr(
    rm_sub: RegisterMachine, m: RegisterMachine,
    reg_offset: nat, pc_offset: nat, halted_pc: nat, timeout_pc: nat,
    fuel_reg: nat, scratch: nat,
    c_sub: Configuration, c: Configuration, phi: nat,
)
    requires
        config_wf(rm_sub, c_sub),
        c_sub.pc < rm_sub.instructions.len(),
        rm_sub.instructions[c_sub.pc as int] is Halt,
        instr_configs_agree(rm_sub, reg_offset, pc_offset, fuel_reg, scratch, phi, c_sub, c),
        phi >= 1,
        c.registers.len() == m.num_regs,
        instrument_frame(rm_sub, m, reg_offset, pc_offset, halted_pc, timeout_pc, fuel_reg, scratch),
    ensures
        run(m, c, 2).pc == halted_pc,
        run(m, c, 2).registers.len() == m.num_regs,
        (forall|r: int| 0 <= r < rm_sub.num_regs as int ==>
            run(m, c, 2).registers[(r + reg_offset) as int] == c_sub.registers[r]),
        run(m, c, 2).registers[scratch as int] == 0,
        forall|jj: int| 0 <= jj < m.num_regs as int
            && (jj < reg_offset || jj >= reg_offset + rm_sub.num_regs)
            && jj != fuel_reg as int && jj != scratch as int
            ==> #[trigger] run(m, c, 2).registers[jj] == c.registers[jj],
{
    let len = rm_sub.instructions.len();
    let p = c_sub.pc;
    let instrs_block = instrument_instructions(
        rm_sub.instructions, reg_offset, pc_offset, halted_pc, timeout_pc, fuel_reg, scratch);

    //  guard at pc_offset + 2p
    assert(2 * p < 2 * len);
    assert(m.instructions[(pc_offset + 2 * p) as int] == instrs_block[2 * p as int]);
    assert((2 * p) % 2 == 0);
    assert(instrs_block[2 * p as int] == Instruction::DecJump { register: fuel_reg, target: timeout_pc });
    assert(c.pc == pc_offset + 2 * p);
    assert(c.pc < m.instructions.len());
    assert(c.registers[fuel_reg as int] == phi && phi > 0);
    assert(!is_halted(m, c));
    let c1 = step(m, c).unwrap();
    assert(c1.pc == c.pc + 1);
    assert(c1.registers == c.registers.update(fuel_reg as int, (phi - 1) as nat));
    assert(c1.registers.len() == m.num_regs);

    //  body at pc_offset + 2p + 1 == DecJump{scratch, halted_pc}, scratch == 0 ⇒ jump to halted_pc
    assert(2 * p + 1 < 2 * len);
    assert(m.instructions[(pc_offset + (2 * p + 1)) as int] == instrs_block[(2 * p + 1) as int]);
    assert((2 * p + 1) % 2 == 1);
    assert((2 * p + 1) / 2 == p as int);
    assert(instrs_block[(2 * p + 1) as int]
        == instrument_body(rm_sub.instructions[p as int], reg_offset, pc_offset, halted_pc, scratch));
    assert(instrument_body(rm_sub.instructions[p as int], reg_offset, pc_offset, halted_pc, scratch)
        == Instruction::DecJump { register: scratch, target: halted_pc });
    assert(c1.pc == pc_offset + 2 * p + 1);
    assert(c1.registers[scratch as int] == 0) by { assert(scratch != fuel_reg); }
    assert(!is_halted(m, c1));
    let c2 = step(m, c1).unwrap();
    assert(c2.pc == halted_pc);
    assert(c2.registers == c1.registers);

    lemma_run_unfold_step(m, c, 2);
    lemma_run_unfold_step(m, c1, 1);
    assert(run(m, c, 2) == c2);

    //  registers: c2 == c1 == c.update(fuel_reg, phi-1); E-bank unchanged from c, == c_sub
    assert forall|r: int| 0 <= r < rm_sub.num_regs as int implies
        #[trigger] run(m, c, 2).registers[(r + reg_offset) as int] == c_sub.registers[r]
    by {
        assert((r + reg_offset) != fuel_reg as int);
    }
    assert(run(m, c, 2).registers[scratch as int] == 0);
    assert forall|jj: int| 0 <= jj < m.num_regs as int
        && (jj < reg_offset || jj >= reg_offset + rm_sub.num_regs)
        && jj != fuel_reg as int && jj != scratch as int
    implies #[trigger] run(m, c, 2).registers[jj] == c.registers[jj]
    by { }
}

//  ============================================================
//  ⟸ direction: if E halts within the budget, instrument reaches HALTED with the halt registers
//  ============================================================

///  If `E` halts within `phi - 1` steps from `c_sub`, then running the instrumented host from the
///  matching config `c` reaches `halted_pc` within `2*phi` steps carrying the halted E-config's
///  registers in the shifted bank. (The `phi-1` budget leaves one guard's worth of fuel slack so a
///  `Halt`-instruction halt — which costs an extra guard — still lands on HALTED.)
#[verifier::rlimit(4000)]
pub proof fn lemma_instrument_halts(
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
        run_halts(rm_sub, c_sub, (phi - 1) as nat),
        c.registers.len() == m.num_regs,
        instrument_frame(rm_sub, m, reg_offset, pc_offset, halted_pc, timeout_pc, fuel_reg, scratch),
    ensures
        exists|g: nat| g <= 2 * phi
            && run(m, c, g).pc == halted_pc
            && (forall|r: int| 0 <= r < rm_sub.num_regs as int ==>
                    #[trigger] run(m, c, g).registers[(r + reg_offset) as int]
                        == run(rm_sub, c_sub, (phi - 1) as nat).registers[r])
            && run(m, c, g).registers[scratch as int] == 0
            && run(m, c, g).registers.len() == m.num_regs
            && (forall|jj: int| 0 <= jj < m.num_regs as int
                    && (jj < reg_offset || jj >= reg_offset + rm_sub.num_regs)
                    && jj != fuel_reg as int && jj != scratch as int
                    ==> #[trigger] run(m, c, g).registers[jj] == c.registers[jj]),
    decreases phi,
{
    reveal(machine_wf);
    let len = rm_sub.instructions.len();
    let halt_cfg = run(rm_sub, c_sub, (phi - 1) as nat);

    if is_halted(rm_sub, c_sub) {
        lemma_halted_run_identity(rm_sub, c_sub, (phi - 1) as nat);
        assert(halt_cfg == c_sub);
        if c_sub.pc >= len {
            assert(c_sub.pc == len);   //  config_wf gives pc <= len
            //  c already sits on halted_pc; witness g = 0
            assert(c.pc == pc_offset + 2 * len);
            assert(c.pc == halted_pc);
            let g: nat = 0;
            assert(run(m, c, g) == c);
            assert(run(m, c, g).pc == halted_pc);
            assert(forall|r: int| 0 <= r < rm_sub.num_regs as int ==>
                run(m, c, g).registers[(r + reg_offset) as int] == halt_cfg.registers[r]);
            assert(g <= 2 * phi);
        } else {
            //  c_sub.pc < len and is_halted ⇒ the instruction is Halt
            assert(rm_sub.instructions[c_sub.pc as int] is Halt) by {
                assert(step(rm_sub, c_sub) is None);
            }
            lemma_instrument_halt_instr(rm_sub, m, reg_offset, pc_offset, halted_pc, timeout_pc,
                fuel_reg, scratch, c_sub, c, phi);
            let g: nat = 2;
            assert(run(m, c, g).pc == halted_pc);
            assert(forall|r: int| 0 <= r < rm_sub.num_regs as int ==>
                run(m, c, g).registers[(r + reg_offset) as int] == c_sub.registers[r]);
            assert(g <= 2 * phi);
        }
    } else {
        //  not halted ⇒ run_halts(.,phi-1) forces phi-1 >= 1, so phi >= 2 > 0
        assert(phi - 1 >= 1) by {
            if phi - 1 == 0 { assert(run_halts(rm_sub, c_sub, 0) == is_halted(rm_sub, c_sub)); }
        }
        assert(phi > 0);
        lemma_instrument_estep(rm_sub, m, reg_offset, pc_offset, halted_pc, timeout_pc,
            fuel_reg, scratch, c_sub, c, phi);
        let s_sub = step(rm_sub, c_sub).unwrap();
        let c2 = run(m, c, 2);
        //  run_halts unfold: run_halts(c_sub, phi-1) ∧ !halted ⇒ run_halts(s_sub, phi-2)
        assert(run_halts(rm_sub, s_sub, (phi - 2) as nat));
        //  also run(rm_sub, c_sub, phi-1) == run(rm_sub, s_sub, phi-2)
        lemma_run_unfold_step(rm_sub, c_sub, (phi - 1) as nat);
        assert(halt_cfg == run(rm_sub, s_sub, (phi - 2) as nat));

        lemma_instrument_halts(rm_sub, m, reg_offset, pc_offset, halted_pc, timeout_pc,
            fuel_reg, scratch, s_sub, c2, (phi - 1) as nat);
        let g_inner = choose|g: nat| g <= 2 * (phi - 1)
            && run(m, c2, g).pc == halted_pc
            && (forall|r: int| 0 <= r < rm_sub.num_regs as int ==>
                    #[trigger] run(m, c2, g).registers[(r + reg_offset) as int]
                        == run(rm_sub, s_sub, (phi - 2) as nat).registers[r])
            && run(m, c2, g).registers[scratch as int] == 0
            && run(m, c2, g).registers.len() == m.num_regs
            && (forall|jj: int| 0 <= jj < m.num_regs as int
                    && (jj < reg_offset || jj >= reg_offset + rm_sub.num_regs)
                    && jj != fuel_reg as int && jj != scratch as int
                    ==> #[trigger] run(m, c2, g).registers[jj] == c2.registers[jj]);

        lemma_run_add(m, c, 2, g_inner);
        assert(run(m, c, (2 + g_inner) as nat) == run(m, c2, g_inner));
        let g: nat = (2 + g_inner) as nat;
        assert(g <= 2 * phi) by { assert(g_inner <= 2 * (phi - 1)); }
        //  frame compose: out-of-frame regs of run(m,c,g) == c2's == c's
        assert forall|jj: int| 0 <= jj < m.num_regs as int
            && (jj < reg_offset || jj >= reg_offset + rm_sub.num_regs)
            && jj != fuel_reg as int && jj != scratch as int
        implies run(m, c, g).registers[jj] == c.registers[jj]
        by {
            assert(run(m, c2, g_inner).registers[jj] == c2.registers[jj]);
            assert(c2.registers[jj] == c.registers[jj]);
        }
        assert(run(m, c, g).pc == halted_pc);
        assert(forall|r: int| 0 <= r < rm_sub.num_regs as int ==>
            run(m, c, g).registers[(r + reg_offset) as int] == halt_cfg.registers[r]);
    }
}

//  ============================================================
//  Guard firing on empty fuel ⇒ TIMEOUT
//  ============================================================

///  When the budget is exhausted (`phi == 0`) and the tracked E-config is parked on a guard
///  (`c_sub.pc < len`), one host step (the guard) jumps to `timeout_pc`.
pub proof fn lemma_instrument_guard_timeout(
    rm_sub: RegisterMachine, m: RegisterMachine,
    reg_offset: nat, pc_offset: nat, halted_pc: nat, timeout_pc: nat,
    fuel_reg: nat, scratch: nat,
    c_sub: Configuration, c: Configuration,
)
    requires
        c_sub.pc < rm_sub.instructions.len(),
        instr_configs_agree(rm_sub, reg_offset, pc_offset, fuel_reg, scratch, 0, c_sub, c),
        c.registers.len() == m.num_regs,
        instrument_frame(rm_sub, m, reg_offset, pc_offset, halted_pc, timeout_pc, fuel_reg, scratch),
    ensures
        run(m, c, 1).pc == timeout_pc,
        run(m, c, 1).registers == c.registers,
        run(m, c, 1).registers.len() == m.num_regs,
{
    let len = rm_sub.instructions.len();
    let p = c_sub.pc;
    let instrs_block = instrument_instructions(
        rm_sub.instructions, reg_offset, pc_offset, halted_pc, timeout_pc, fuel_reg, scratch);
    assert(2 * p < 2 * len);
    assert(m.instructions[(pc_offset + 2 * p) as int] == instrs_block[2 * p as int]);
    assert((2 * p) % 2 == 0);
    assert(instrs_block[2 * p as int] == Instruction::DecJump { register: fuel_reg, target: timeout_pc });
    assert(c.pc == pc_offset + 2 * p);
    assert(c.pc < m.instructions.len());
    assert(c.registers[fuel_reg as int] == 0);
    assert(!is_halted(m, c));
    let c1 = step(m, c).unwrap();
    assert(c1.pc == timeout_pc);
    assert(c1.registers == c.registers);
    lemma_run_unfold_step(m, c, 1);
    assert(run(m, c, 1) == c1);
}

//  ============================================================
//  ⟹ direction: instrument always reaches a sink, and HALTED is reached only via a genuine E-halt
//  ============================================================

///  Running the instrumented host from a matching config always reaches one of the two sinks within
///  `2*phi + 1` steps, and **if it reaches `halted_pc` then `E` genuinely halted within `phi` steps**,
///  carrying that halt config's registers in the shifted bank. This is the soundness the dovetail's
///  ⟹ direction needs (a HALTED verdict reflects a real declaration) together with totality (the
///  inner loop always terminates with a verdict).
#[verifier::rlimit(4000)]
pub proof fn lemma_instrument_reaches_sink(
    rm_sub: RegisterMachine, m: RegisterMachine,
    reg_offset: nat, pc_offset: nat, halted_pc: nat, timeout_pc: nat,
    fuel_reg: nat, scratch: nat,
    c_sub: Configuration, c: Configuration, phi: nat,
)
    requires
        machine_wf(rm_sub),
        config_wf(rm_sub, c_sub),
        instr_configs_agree(rm_sub, reg_offset, pc_offset, fuel_reg, scratch, phi, c_sub, c),
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
            && run(m, c, g).registers[scratch as int] == 0
            && (forall|jj: int| 0 <= jj < m.num_regs as int
                    && (jj < reg_offset || jj >= reg_offset + rm_sub.num_regs)
                    && jj != fuel_reg as int && jj != scratch as int
                    ==> #[trigger] run(m, c, g).registers[jj] == c.registers[jj]),
    decreases phi,
{
    reveal(machine_wf);
    let len = rm_sub.instructions.len();

    if is_halted(rm_sub, c_sub) {
        lemma_halted_run_identity(rm_sub, c_sub, phi);
        lemma_halted_run_halts(rm_sub, c_sub, phi);
        if c_sub.pc >= len {
            assert(c_sub.pc == len);
            assert(c.pc == halted_pc);
            let g: nat = 0;
            assert(run(m, c, g) == c);
            assert(run(m, c, g).pc == halted_pc);
            assert(run(m, c, g).pc == halted_pc ==>
                run_halts(rm_sub, c_sub, phi)
                && (forall|r: int| 0 <= r < rm_sub.num_regs as int ==>
                        run(m, c, g).registers[(r + reg_offset) as int]
                            == run(rm_sub, c_sub, phi).registers[r]));
            assert(forall|jj: int| 0 <= jj < m.num_regs as int
                && (jj < reg_offset || jj >= reg_offset + rm_sub.num_regs)
                && jj != fuel_reg as int && jj != scratch as int
                ==> run(m, c, g).registers[jj] == c.registers[jj]);
            assert(run(m, c, g).registers[scratch as int] == 0);
            assert(g <= 2 * phi + 1);
        } else {
            assert(rm_sub.instructions[c_sub.pc as int] is Halt) by {
                assert(step(rm_sub, c_sub) is None);
            }
            if phi >= 1 {
                lemma_instrument_halt_instr(rm_sub, m, reg_offset, pc_offset, halted_pc, timeout_pc,
                    fuel_reg, scratch, c_sub, c, phi);
                let g: nat = 2;
                assert(run(m, c, g).pc == halted_pc);
                assert(run(m, c, g).pc == halted_pc ==>
                    run_halts(rm_sub, c_sub, phi)
                    && (forall|r: int| 0 <= r < rm_sub.num_regs as int ==>
                            run(m, c, g).registers[(r + reg_offset) as int]
                                == run(rm_sub, c_sub, phi).registers[r]));
                assert(forall|jj: int| 0 <= jj < m.num_regs as int
                    && (jj < reg_offset || jj >= reg_offset + rm_sub.num_regs)
                    && jj != fuel_reg as int && jj != scratch as int
                    ==> run(m, c, g).registers[jj] == c.registers[jj]);
                assert(run(m, c, g).registers[scratch as int] == 0);
                assert(g <= 2 * phi + 1);
            } else {
                assert(phi == 0);
                lemma_instrument_guard_timeout(rm_sub, m, reg_offset, pc_offset, halted_pc, timeout_pc,
                    fuel_reg, scratch, c_sub, c);
                let g: nat = 1;
                assert(run(m, c, g).pc == timeout_pc);
                assert(run(m, c, g).registers == c.registers);
                assert(g <= 2 * phi + 1);
            }
        }
    } else {
        //  c_sub not halted ⇒ c_sub.pc < len (there is a guard)
        assert(c_sub.pc < len) by { assert(step(rm_sub, c_sub) is Some); }
        if phi == 0 {
            lemma_instrument_guard_timeout(rm_sub, m, reg_offset, pc_offset, halted_pc, timeout_pc,
                fuel_reg, scratch, c_sub, c);
            let g: nat = 1;
            assert(run(m, c, g).pc == timeout_pc);
            assert(run(m, c, g).registers == c.registers);
            assert(g <= 2 * phi + 1);
        } else {
            lemma_instrument_estep(rm_sub, m, reg_offset, pc_offset, halted_pc, timeout_pc,
                fuel_reg, scratch, c_sub, c, phi);
            let s_sub = step(rm_sub, c_sub).unwrap();
            let c2 = run(m, c, 2);
            lemma_instrument_reaches_sink(rm_sub, m, reg_offset, pc_offset, halted_pc, timeout_pc,
                fuel_reg, scratch, s_sub, c2, (phi - 1) as nat);
            let g_inner = choose|g: nat| g <= 2 * (phi - 1) + 1
                && (run(m, c2, g).pc == halted_pc || run(m, c2, g).pc == timeout_pc)
                && run(m, c2, g).registers.len() == m.num_regs
                && (run(m, c2, g).pc == halted_pc ==>
                        run_halts(rm_sub, s_sub, (phi - 1) as nat)
                        && (forall|r: int| 0 <= r < rm_sub.num_regs as int ==>
                                #[trigger] run(m, c2, g).registers[(r + reg_offset) as int]
                                    == run(rm_sub, s_sub, (phi - 1) as nat).registers[r]))
                && run(m, c2, g).registers[scratch as int] == 0
                && (forall|jj: int| 0 <= jj < m.num_regs as int
                        && (jj < reg_offset || jj >= reg_offset + rm_sub.num_regs)
                        && jj != fuel_reg as int && jj != scratch as int
                        ==> #[trigger] run(m, c2, g).registers[jj] == c2.registers[jj]);
            lemma_run_add(m, c, 2, g_inner);
            let g: nat = (2 + g_inner) as nat;
            assert(run(m, c, g) == run(m, c2, g_inner));
            assert(g <= 2 * phi + 1) by { assert(g_inner <= 2 * (phi - 1) + 1); }
            //  soundness compose: halted ⇒ run_halts(c_sub,phi) ∧ bank == run(c_sub,phi)
            assert(run(m, c, g).pc == halted_pc ==>
                run_halts(rm_sub, c_sub, phi)
                && (forall|r: int| 0 <= r < rm_sub.num_regs as int ==>
                        run(m, c, g).registers[(r + reg_offset) as int]
                            == run(rm_sub, c_sub, phi).registers[r]))
            by {
                if run(m, c, g).pc == halted_pc {
                    assert(run(m, c2, g_inner).pc == halted_pc);
                    assert(run_halts(rm_sub, s_sub, (phi - 1) as nat));
                    //  run_halts(s_sub, phi-1) ∧ !is_halted(c_sub) ⇒ run_halts(c_sub, phi)
                    assert(run_halts(rm_sub, c_sub, phi));
                    //  run(c_sub, phi) == run(s_sub, phi-1)
                    lemma_run_unfold_step(rm_sub, c_sub, phi);
                    assert(run(rm_sub, c_sub, phi) == run(rm_sub, s_sub, (phi - 1) as nat));
                }
            }
            //  frame compose: out-of-bank regs of run(m,c,g) == c2's (IH frame) == c's (estep frame)
            assert forall|jj: int| 0 <= jj < m.num_regs as int
                && (jj < reg_offset || jj >= reg_offset + rm_sub.num_regs)
                && jj != fuel_reg as int && jj != scratch as int
            implies #[trigger] run(m, c, g).registers[jj] == c.registers[jj]
            by {
                assert(run(m, c2, g_inner).registers[jj] == c2.registers[jj]);
                assert(c2.registers[jj] == c.registers[jj]);
            }
            assert(run(m, c, g).registers[scratch as int] == 0);
        }
    }
}

} //  verus!
