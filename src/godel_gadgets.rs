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

/// Run-composition: `run(m,c,a+b) == run(m, run(m,c,a), b)`.
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
//  A straight-line block of `count` Inc(reg) instructions adds `count` to `reg`.
//  ============================================================

/// Running `count` consecutive `Inc(reg)` instructions from `start_pc` adds `count` to `reg`
/// (all other registers unchanged), advancing the pc to `start_pc + count`.
pub proof fn lemma_inc_block(
    m: RegisterMachine, c: Configuration, reg: nat, count: nat, start_pc: nat,
)
    requires
        start_pc + count <= m.instructions.len(),
        forall|i: int| start_pc <= i < start_pc + count ==> #[trigger] m.instructions[i] == mk_inc(reg),
        c.pc == start_pc,
        c.registers.len() == m.num_regs,
        reg < m.num_regs,
    ensures
        run(m, c, count).pc == start_pc + count,
        run(m, c, count).registers.len() == c.registers.len(),
        run(m, c, count).registers[reg as int] == c.registers[reg as int] + count,
        forall|r: int| 0 <= r < m.num_regs as int && r != reg as int
            ==> run(m, c, count).registers[r] == c.registers[r],
    decreases count,
{
    if count == 0 {
        assert(run(m, c, 0) == c);
    } else {
        assert(m.instructions[start_pc as int] == mk_inc(reg));   // trigger at i = start_pc
        assert(!is_halted(m, c));
        lemma_run_unfold_step(m, c, count);
        let c1 = step(m, c).unwrap();   // Inc(reg): reg++, pc = start_pc+1.
        assert(c1.pc == start_pc + 1);
        assert(c1.registers == c.registers.update(reg as int, c.registers[reg as int] + 1));
        assert(c1.registers.len() == m.num_regs);
        lemma_inc_block(m, c1, reg, (count - 1) as nat, start_pc + 1);
        assert(run(m, c, count) == run(m, c1, (count - 1) as nat));
        assert forall|r: int| 0 <= r < m.num_regs as int && r != reg as int
        implies run(m, c, count).registers[r] == c.registers[r]
        by {
            assert(c1.registers[r] == c.registers[r]);
        }
    }
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

//  ============================================================
//  M1 — the multiply back-loop: add `k` to `dst` per unit of `src`.
//  ============================================================

/// **Multiply back-loop gadget**: `[DecJump(src, start_pc+k+2), Inc(dst)×k, Jump(start_pc)]`
/// (`k + 2` instructions). Drains `src`, adding `k` to `dst` for each unit — so `dst += k·src_orig`,
/// `src := 0`. The second half of multiply `(n)×k` (after `move (n)→(n+1)`).
pub open spec fn mult_back_instrs(src: nat, dst: nat, k: nat, start_pc: nat) -> Seq<Instruction> {
    Seq::new(k + 2, |i: int|
        if i == 0 { mk_dj(src, start_pc + k + 2) }
        else if i <= k { mk_inc(dst) }
        else { mk_jump(start_pc) }
    )
}

/// **The multiply back-loop.** From `c` at `start_pc` with `src = remaining`, `dst = acc`, running
/// `(k+2)·remaining + 1` steps drains `src → dst·k`: `dst := acc + k·remaining`, `src := 0`, all other
/// registers unchanged, landing at `start_pc + k + 2`. Per iteration: DecJump (1) + k·Inc + Jump (1).
#[verifier::rlimit(4000)]
pub proof fn lemma_mult_back_loop(
    m: RegisterMachine, c: Configuration,
    src: nat, dst: nat, k: nat, start_pc: nat,
    acc: nat, remaining: nat,
)
    requires
        start_pc + k + 2 <= m.instructions.len(),
        m.instructions[start_pc as int] == mk_dj(src, start_pc + k + 2),
        forall|i: int| start_pc + 1 <= i < start_pc + 1 + k ==> #[trigger] m.instructions[i] == mk_inc(dst),
        m.instructions[(start_pc + k + 1) as int] == mk_jump(start_pc),
        c.pc == start_pc,
        c.registers.len() == m.num_regs,
        c.registers[src as int] == remaining,
        c.registers[dst as int] == acc,
        src < m.num_regs, dst < m.num_regs, src != dst,
    ensures
        run(m, c, (k + 2) * remaining + 1).pc == start_pc + k + 2,
        run(m, c, (k + 2) * remaining + 1).registers[dst as int] == acc + k * remaining,
        run(m, c, (k + 2) * remaining + 1).registers[src as int] == 0,
        forall|r: int| 0 <= r < m.num_regs as int && r != src as int && r != dst as int
            ==> run(m, c, (k + 2) * remaining + 1).registers[r] == c.registers[r],
    decreases remaining,
{
    let fuel = (k + 2) * remaining + 1;
    if remaining == 0 {
        assert(fuel == 1) by(nonlinear_arith) requires fuel == (k + 2) * remaining + 1, remaining == 0;
        assert(!is_halted(m, c));
        lemma_run_unfold_step(m, c, fuel);
        let c1 = step(m, c).unwrap();    // DecJump(src) zero-branch: pc = start_pc+k+2, regs unchanged.
        assert(c1.pc == start_pc + k + 2);
        assert(c1.registers == c.registers);
        assert((fuel - 1) as nat == 0) by(nonlinear_arith) requires fuel == 1;
        assert(run(m, c1, (fuel - 1) as nat) == c1);
        assert(run(m, c, fuel) == c1);
        assert(k * remaining == 0) by(nonlinear_arith) requires remaining == 0;
        assert(run(m, c, fuel).registers =~= c.registers);
    } else {
        //  step 0: DecJump(src), src = remaining > 0 → dec src, pc = start_pc+1.
        assert(fuel >= 1) by(nonlinear_arith) requires fuel == (k + 2) * remaining + 1;
        assert(!is_halted(m, c));
        lemma_run_unfold_step(m, c, fuel);
        let c_dj = step(m, c).unwrap();
        assert(c_dj.pc == start_pc + 1);
        assert(c_dj.registers[src as int] == (remaining - 1) as nat);
        assert(c_dj.registers[dst as int] == acc);
        assert(c_dj.registers.len() == m.num_regs);
        //  Bridge the fuel arithmetic through rem1 = remaining-1 (so all the `as nat` casts and
        //  (k+2)-distributions reduce to one degree-2 identity Lean's nonlinear_arith handles).
        let rem1: nat = (remaining - 1) as nat;
        assert(remaining == rem1 + 1);
        assert((k + 2) * remaining == (k + 2) * rem1 + (k + 2)) by(nonlinear_arith)
            requires remaining == rem1 + 1;
        assert((fuel - 1) as nat == (k + 2) * rem1 + (k + 2)) by(nonlinear_arith)
            requires fuel == (k + 2) * remaining + 1, (k + 2) * remaining == (k + 2) * rem1 + (k + 2);
        assert(run(m, c, fuel) == run(m, c_dj, (fuel - 1) as nat));   // from the unfold above
        //  peel the k Inc steps: run(m, c_dj, fuel-1) == run(m, run(m, c_dj, k), (k+2)·rem1+2).
        let g: nat = ((k + 2) * rem1 + 2) as nat;
        assert((fuel - 1) as nat == (k + g) as nat);
        lemma_run_add(m, c_dj, k, g);
        assert(run(m, c_dj, (fuel - 1) as nat) == run(m, run(m, c_dj, k), g));
        lemma_inc_block(m, c_dj, dst, k, start_pc + 1);
        let c_inc = run(m, c_dj, k);
        assert(c_inc.pc == start_pc + 1 + k);
        assert(c_inc.registers.len() == m.num_regs);
        assert(c_inc.registers[dst as int] == acc + k);
        assert(c_inc.registers[src as int] == (remaining - 1) as nat);   // src != dst ⟹ preserved
        //  peel the Jump step: run(m, c_inc, g) == run(m, c_jmp, g-1) where g-1 == (k+2)·rem1+1.
        assert(c_inc.pc == start_pc + k + 1);
        assert(!is_halted(m, c_inc));
        assert(g >= 1);
        lemma_run_unfold_step(m, c_inc, g);
        let c_jmp = step(m, c_inc).unwrap();
        assert(c_jmp.pc == start_pc);
        assert(c_jmp.registers == c_inc.registers);
        assert((g - 1) as nat == (k + 2) * rem1 + 1);
        assert(run(m, c, fuel) == run(m, c_jmp, (k + 2) * rem1 + 1));
        lemma_mult_back_loop(m, c_jmp, src, dst, k, start_pc, acc + k, rem1);
        //  dst result: (acc + k) + k·rem1 == acc + k·remaining.
        assert((acc + k) + k * rem1 == acc + k * remaining) by(nonlinear_arith)
            requires remaining == rem1 + 1;
        //  register preservation through the iteration.
        assert forall|r: int| 0 <= r < m.num_regs as int && r != src as int && r != dst as int
        implies run(m, c, fuel).registers[r] == c.registers[r]
        by {
            assert(c_dj.registers[r] == c.registers[r]);       // DecJump only changed src
            assert(c_inc.registers[r] == c_dj.registers[r]);   // inc_block: r != dst
            assert(c_jmp.registers[r] == c_inc.registers[r]);
        };
    }
}

} //  verus!
