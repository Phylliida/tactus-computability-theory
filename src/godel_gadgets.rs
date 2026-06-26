//! # GAP-2 L1 — the k→2 Gödel reduction gadgets (M1: move, M2: multiply/divide/div-test)
//!
//! Register-machine gadgets over the `{Inc, DecJump, Jump}` instruction set with **no free scratch**
//! (the 2-counter setting): every unconditional loop back-edge is a `Jump` (the R-ii primitive), not a
//! `DecJump(zero_scratch, top)` (there is no zero register to spare in RM(2)). These are the building
//! blocks of the k→2 Gödel reduction `RM(k) → RM(2)`, where `C1 = ∏ base(i)^{r_i}` is the Gödel register
//! and `C2` is the single `+1` scratch.
//!
//! M1 mirrors `multi_output_primitives::lemma_copy_loop_inner`, swapping the `DecJump(scratch, top)`
//! back-edge for `Jump(top)`. Fully verified, no verifier escape hatches.
//!
//! See `docs/gap2-register-to-tm-plan.md` §"k→2 GADGET DESIGN LOCKED".

use vstd::prelude::*;
use crate::machine::*;
use crate::multi_output_primitives::{mk_inc, mk_dj, mk_jump};

verus! {

//  ============================================================
//  Helper: connect run(m, c, fuel) with step when fuel > 0 (per-module, avoids trigger pollution).
//  ============================================================

proof fn lemma_run_unfold_step(m: RegisterMachine, c: Configuration, fuel: nat)
    requires
        fuel > 0,
        !is_halted(m, c),
    ensures
        run(m, c, fuel) == run(m, step(m, c).unwrap(), (fuel - 1) as nat),
{
}

//  ============================================================
//  M1 — the move gadget (Jump back-edge, no scratch).
//  ============================================================

/// **Move gadget**: `[DecJump(src, start_pc+3), Inc(dst), Jump(start_pc)]`. Drains `src` into `dst`
/// (`dst += src_orig`, `src := 0`). The 2-counter analogue of `copy_instrs` — the back-edge is an
/// unconditional `Jump` (R-ii) since RM(2) has no always-zero scratch register.
pub open spec fn move_instrs(src: nat, dst: nat, start_pc: nat) -> Seq<Instruction> {
    seq![
        mk_dj(src, start_pc + 3),
        mk_inc(dst),
        mk_jump(start_pc),
    ]
}

/// **The move loop.** From `c` at `start_pc` with `src = remaining`, `dst = acc`, running
/// `3*remaining + 1` steps drains `src → dst`: `dst := orig_val`, `src := 0`, all other registers
/// unchanged, landing at `start_pc + 3`. (Invariant: `acc + remaining == orig_val`.)
#[verifier::rlimit(1000)]
pub proof fn lemma_move_loop(
    m: RegisterMachine,
    c: Configuration,
    src: nat, dst: nat,
    start_pc: nat,
    orig_val: nat, acc: nat, remaining: nat,
)
    requires
        start_pc + 3 <= m.instructions.len(),
        m.instructions[start_pc as int] == mk_dj(src, start_pc + 3),
        m.instructions[(start_pc + 1) as int] == mk_inc(dst),
        m.instructions[(start_pc + 2) as int] == mk_jump(start_pc),
        c.pc == start_pc,
        c.registers.len() == m.num_regs,
        c.registers[src as int] == remaining,
        c.registers[dst as int] == acc,
        src < m.num_regs, dst < m.num_regs,
        src != dst,
        acc + remaining == orig_val,
    ensures
        run(m, c, 3 * remaining + 1).pc == start_pc + 3,
        run(m, c, 3 * remaining + 1).registers[dst as int] == orig_val,
        run(m, c, 3 * remaining + 1).registers[src as int] == 0,
        forall|r: int| 0 <= r < m.num_regs as int && r != src as int && r != dst as int
            ==> run(m, c, 3 * remaining + 1).registers[r] == c.registers[r],
    decreases remaining,
{
    if remaining == 0 {
        assert(3 * remaining + 1 > 0) by(nonlinear_arith) requires remaining == 0;
        assert(!is_halted(m, c));
        lemma_run_unfold_step(m, c, 3 * remaining + 1);
        let c1 = step(m, c).unwrap();   // DecJump(src) zero-branch: pc = start_pc+3, regs unchanged.
        assert(c1.pc == start_pc + 3);
        assert(c1.registers == c.registers);
        assert((3 * remaining + 1 - 1) as nat == 0nat) by(nonlinear_arith) requires remaining == 0;
        assert(run(m, c1, (3 * remaining + 1 - 1) as nat) == c1);
        assert(run(m, c, 3 * remaining + 1) == c1);
        assert(run(m, c, 3 * remaining + 1).pc == start_pc + 3);
        assert(run(m, c, 3 * remaining + 1).registers =~= c.registers);
    } else {
        assert(!is_halted(m, c));
        lemma_run_unfold_step(m, c, 3 * remaining + 1);
        let c1 = step(m, c).unwrap();   // DecJump(src): src--, pc = start_pc+1.
        assert(!is_halted(m, c1));
        assert(3 * remaining + 1 - 1 >= 1) by(nonlinear_arith) requires remaining > 0;
        lemma_run_unfold_step(m, c1, (3 * remaining + 1 - 1) as nat);
        let c2 = step(m, c1).unwrap();  // Inc(dst): dst++, pc = start_pc+2.
        assert(!is_halted(m, c2));
        assert(3 * remaining + 1 - 2 >= 1) by(nonlinear_arith) requires remaining > 0;
        lemma_run_unfold_step(m, c2, (3 * remaining + 1 - 2) as nat);
        let c3 = step(m, c2).unwrap();  // Jump(start_pc): pc = start_pc, regs unchanged.
        assert(c3.pc == start_pc);
        assert(c3.registers[src as int] == (remaining - 1) as nat);
        assert(c3.registers[dst as int] == acc + 1);
        assert((3 * remaining + 1 - 3) as nat == (3 * ((remaining - 1) as nat) + 1) as nat) by(nonlinear_arith)
            requires remaining > 0;
        lemma_move_loop(m, c3, src, dst, start_pc, orig_val, acc + 1, (remaining - 1) as nat);
        //  Help z3 with register preservation through the 3 steps.
        assert forall|r: int| 0 <= r < m.num_regs as int && r != src as int && r != dst as int
        implies run(m, c, 3 * remaining + 1).registers[r] == c.registers[r]
        by {
            assert(c3.registers[r] == c.registers[r]);
        };
    }
}

} //  verus!
