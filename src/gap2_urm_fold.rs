//! # GAP-2 G2-F — Option B (N+47), RM-domain body: brick 1, the entry-fold Horner step.
//!
//! Option B follows the Aanderaa–Cohen + Shepherdson–Sturgis [18] single-register decider convention
//! (see `docs/gap2-input-loader-plan.md` §N+38/§N+43): the whole characteristic-function computation —
//! fold the base-`m` input `α` into one register, dovetail declared pairs `(a,b)`, compute `relnum(a,b)`,
//! compare — is **register-machine arithmetic**, then TM-simulated by the existing
//! `godel`+`rm_to_tm`+`lemma_tm_h0_iff` pipeline. No immutable α tape-block, so the Q4 collision of
//! Option A cannot arise.
//!
//! This module is brick 1 of N+39's list: the **entry-fold** atom `R := m·R + d` (Horner). It folds
//! one base-`m` digit `d` into the accumulator `R`. The full entry loop (consume α's digit string) is a
//! later brick; this is its reusable inner step.
//!
//! Construction = the register-parametric `lemma_multiply_block` idiom (`godel_blocks.rs`) plus a final
//! digit-add: `move(R→tmp) ∘ mult_back(tmp→R, k=m) ∘ move(d→R)`, all `{Inc, DecJump, Jump}` loops with
//! Jump back-edges (no scratch). Purely additive; reuses only verified gadgets
//! (`godel_gadgets::lemma_move_loop` / `lemma_mult_back_loop`, `search_rm_arith::lemma_run_add`). No
//! verifier escape hatches.

use vstd::prelude::*;
use crate::machine::*;
use crate::multi_output_primitives::{mk_inc, mk_dj, mk_jump};
use crate::godel_gadgets::{move_instrs, mult_back_instrs, lemma_move_loop, lemma_mult_back_loop};
use crate::search_rm_arith::{lemma_run_add, lemma_run_preserves_len};

verus! {

//  ============================================================
//  The Horner-step instruction layout (k + 8 instructions).
//  ============================================================
//
//  Layout at `start_pc` (exit pc = start_pc + k + 8):
//    +0..+2       move(R→tmp)       [DecJump(r, sp+3), Inc(tmp), Jump(sp)]
//    +3           mult_back head    DecJump(tmp, sp+k+5)
//    +4..+3+k     Inc(r) × k
//    +k+4         mult_back jump    Jump(sp+3)
//    +k+5..+k+7   move(d→R)         [DecJump(dg, sp+k+8), Inc(r), Jump(sp+k+5)]

/// **The entry-fold Horner step layout.** `move(r→tmp)` ++ `mult_back(tmp→r, k)` ++ `move(dg→r)`,
/// `k + 8` instructions starting at `start_pc`. Computes `r := k·r + dg`, consuming `dg`, with `tmp`
/// used as transient scratch (net unchanged).
pub open spec fn horner_step_instrs(r: nat, dg: nat, tmp: nat, k: nat, start_pc: nat) -> Seq<Instruction> {
    move_instrs(r, tmp, start_pc)
        + mult_back_instrs(tmp, r, k, start_pc + 3)
        + move_instrs(dg, r, start_pc + k + 5)
}

//  ============================================================
//  The Horner-step correctness lemma:  r := k·r + dg.
//  ============================================================

/// **The entry-fold Horner step.** From `c` at `start_pc` with `r = r0`, `dg = dg0`, `tmp = 0`, runs
/// `(k+5)·r0 + 3·dg0 + 3` steps to `start_pc + k + 8` with `r := k·r0 + dg0`, `dg := 0`, `tmp := 0`,
/// every other register unchanged. `move` drains `r` into `tmp`; `mult_back` rebuilds `r := k·tmp`;
/// the final `move` adds the digit `dg` into `r`.
///
/// The base `k = m` (the alphabet/Sylvester base) is a fixed parameter of the construction, so the
/// `k` literal `Inc`s form a finite instruction block. Register values are unbounded (`r0`, `dg0`
/// arbitrary `nat`) — the fold's exponential growth is carried abstractly, never materialized (the
/// magnitude-parametric property the whole Option-B reuse rests on; plan §N+39).
#[verifier::rlimit(2000)]
pub proof fn lemma_horner_step(
    m: RegisterMachine, c: Configuration,
    r: nat, dg: nat, tmp: nat, k: nat, start_pc: nat,
    r0: nat, dg0: nat,
)
    requires
        start_pc + k + 8 <= m.instructions.len(),
        //  move(r→tmp) at start_pc:
        m.instructions[start_pc as int] == mk_dj(r, start_pc + 3),
        m.instructions[(start_pc + 1) as int] == mk_inc(tmp),
        m.instructions[(start_pc + 2) as int] == mk_jump(start_pc),
        //  mult_back(tmp→r, k) at start_pc+3:
        m.instructions[(start_pc + 3) as int] == mk_dj(tmp, start_pc + k + 5),
        forall|i: int| start_pc + 4 <= i < start_pc + 4 + k ==> #[trigger] m.instructions[i] == mk_inc(r),
        m.instructions[(start_pc + k + 4) as int] == mk_jump(start_pc + 3),
        //  move(dg→r) at start_pc+k+5:
        m.instructions[(start_pc + k + 5) as int] == mk_dj(dg, start_pc + k + 8),
        m.instructions[(start_pc + k + 6) as int] == mk_inc(r),
        m.instructions[(start_pc + k + 7) as int] == mk_jump(start_pc + k + 5),
        c.pc == start_pc,
        c.registers.len() == m.num_regs,
        c.registers[r as int] == r0,
        c.registers[dg as int] == dg0,
        c.registers[tmp as int] == 0,
        r < m.num_regs, dg < m.num_regs, tmp < m.num_regs,
        r != dg, r != tmp, dg != tmp,
    ensures
        run(m, c, (k + 5) * r0 + 3 * dg0 + 3).pc == start_pc + k + 8,
        run(m, c, (k + 5) * r0 + 3 * dg0 + 3).registers[r as int] == k * r0 + dg0,
        run(m, c, (k + 5) * r0 + 3 * dg0 + 3).registers[dg as int] == 0,
        run(m, c, (k + 5) * r0 + 3 * dg0 + 3).registers[tmp as int] == 0,
        run(m, c, (k + 5) * r0 + 3 * dg0 + 3).registers.len() == m.num_regs,
        forall|j: int| 0 <= j < m.num_regs as int
            && j != r as int && j != dg as int && j != tmp as int
            ==> run(m, c, (k + 5) * r0 + 3 * dg0 + 3).registers[j] == c.registers[j],
{
    let f1: nat = 3 * r0 + 1;
    let f2: nat = (k + 2) * r0 + 1;
    let f3: nat = 3 * dg0 + 1;

    //  --- Part A: move(r→tmp). r=r0 drains into tmp, r:=0. fuel f1 = 3·r0+1. ---
    lemma_move_loop(m, c, r, tmp, start_pc, r0, 0, r0);
    let c_a = run(m, c, f1);
    lemma_run_preserves_len(m, c, f1);
    assert(c_a.pc == start_pc + 3);
    assert(c_a.registers[tmp as int] == r0);   // dst=tmp = orig_val = 0 + r0
    assert(c_a.registers[r as int] == 0);       // src=r
    assert(c_a.registers[dg as int] == dg0);    // dg != r, dg != tmp ⟹ preserved
    assert(c_a.registers.len() == m.num_regs);

    //  --- Part B: mult_back(tmp→r, k). r := 0 + k·tmp = k·r0, tmp := 0. fuel f2 = (k+2)·r0+1. ---
    lemma_mult_back_loop(m, c_a, tmp, r, k, start_pc + 3, 0, r0);
    let c_b = run(m, c_a, f2);
    lemma_run_preserves_len(m, c_a, f2);
    assert((start_pc + 3) + k + 2 == start_pc + k + 5);
    assert(c_b.pc == start_pc + k + 5);
    assert(c_b.registers[r as int] == k * r0);   // dst=r = acc + k·remaining = 0 + k·r0
    assert(c_b.registers[tmp as int] == 0);       // src=tmp
    assert(c_b.registers[dg as int] == dg0);      // dg != tmp, dg != r ⟹ preserved
    assert(c_b.registers.len() == m.num_regs);

    //  --- Part C: move(dg→r). r := k·r0 + dg0, dg := 0. fuel f3 = 3·dg0+1. ---
    lemma_move_loop(m, c_b, dg, r, start_pc + k + 5, k * r0 + dg0, k * r0, dg0);
    let c_c = run(m, c_b, f3);
    lemma_run_preserves_len(m, c_b, f3);
    assert((start_pc + k + 5) + 3 == start_pc + k + 8);
    assert(c_c.pc == start_pc + k + 8);
    assert(c_c.registers[r as int] == k * r0 + dg0);   // dst=r = orig_val
    assert(c_c.registers[dg as int] == 0);              // src=dg
    assert(c_c.registers[tmp as int] == 0);             // tmp != dg, tmp != r ⟹ preserved (was 0)
    assert(c_c.registers.len() == m.num_regs);

    //  --- Chain the fuel:  f1 + f2 + f3 == (k+5)·r0 + 3·dg0 + 3. ---
    assert(f1 + f2 + f3 == (k + 5) * r0 + 3 * dg0 + 3) by(nonlinear_arith)
        requires f1 == 3 * r0 + 1, f2 == (k + 2) * r0 + 1, f3 == 3 * dg0 + 1;
    lemma_run_add(m, c, f1, f2);
    assert(run(m, c, (f1 + f2) as nat) == c_b);
    lemma_run_add(m, c, (f1 + f2) as nat, f3);
    assert(run(m, c, (f1 + f2 + f3) as nat) == c_c);
    assert(run(m, c, (k + 5) * r0 + 3 * dg0 + 3) == c_c);

    //  --- Register preservation through the three parts. ---
    assert forall|j: int| 0 <= j < m.num_regs as int
        && j != r as int && j != dg as int && j != tmp as int
    implies run(m, c, (k + 5) * r0 + 3 * dg0 + 3).registers[j] == c.registers[j]
    by {
        assert(c_a.registers[j] == c.registers[j]);   // move A: j != r (src), j != tmp (dst)
        assert(c_b.registers[j] == c_a.registers[j]);  // mult_back B: j != tmp (src), j != r (dst)
        assert(c_c.registers[j] == c_b.registers[j]);  // move C: j != dg (src), j != r (dst)
    };
}

} //  verus!
