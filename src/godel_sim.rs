//! # GAP-2 L1 — M3/M5: the Gödel-level per-instruction simulation lemmas.
//!
//! Wraps the M3 value-level block compositions (`godel_blocks.rs`) with the `godel.rs` value lemmas,
//! so each RM(2) block simulates ONE RM(k) instruction on the Gödel-encoded state. RM(2):
//! `reg 0 = C1 = godel_encode(regs)`, `reg 1 = C2` (scratch, `= 0` between blocks). `regs` is the
//! (ghost) RM(k) register vector; the lemmas relate an RM(2) run to its Gödel image.
//!
//!  - **`lemma_inc_sim`** (`Inc(r_i)`): the multiply block `C1 := base(i)·C1`. Via `lemma_godel_inc`,
//!    `C1' = godel_encode(regs[r_i ← regs[r_i]+1])`. Reaches the next block.
//!  - **`lemma_decjump_sim`** (`DecJump(r_i, t)`): the `Div?` test (verdict via `lemma_godel_div_iff`:
//!    `base(i) | C1 ⟺ regs[r_i] ≥ 1`), then on the divisible branch the divide block
//!    `C1 := C1/base(i)` (`= godel_encode(regs[r_i ← regs[r_i]−1])` via `lemma_godel_dec`) reaching
//!    the next block, OR on the `r_i = 0` branch a `Jump` to the translated target block (`C1`
//!    untouched).
//!  - **`lemma_jump_sim`** (`Jump(t)`): a single `Jump` to the translated target block.
//!
//! Parametric in `k = base(i)` and the block start / exit addresses (so M4's address map plugs in).
//! No verifier escape hatches.

use vstd::prelude::*;
use crate::machine::*;
use crate::multi_output_primitives::{mk_inc, mk_dj, mk_jump};
use crate::godel::{base, godel_encode, lemma_godel_inc, lemma_godel_dec, lemma_godel_div_iff, lemma_base_ge_2};
use crate::godel_blocks::{lemma_multiply_block, lemma_divide_block, lemma_divtest_block};
use crate::search_rm_arith::lemma_run_preserves_len;

verus! {

proof fn lemma_run_unfold_step(m: RegisterMachine, c: Configuration, fuel: nat)
    requires
        fuel > 0,
        !is_halted(m, c),
    ensures
        run(m, c, fuel) == run(m, step(m, c).unwrap(), (fuel - 1) as nat),
{
}

/// Run-composition: `run(m,c,a+b) == run(m, run(m,c,a), b)` (per-module local copy).
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
//  M5 — `Inc(r_i)`: multiply block `C1 := base(i)·C1`.
//  ============================================================

/// **The `Inc(r_i)` simulation.** From `C1 = godel_encode(regs)`, `C2 = 0` at `start_pc`, the
/// multiply block (`k = base(i)`) reaches `start_pc + base(i) + 5` with
/// `C1 = godel_encode(regs[r_i ← regs[r_i] + 1])`, `C2 = 0`.
pub proof fn lemma_inc_sim(
    m: RegisterMachine, c: Configuration, regs: Seq<nat>, i: nat, start_pc: nat,
)
    requires
        m.num_regs == 2,
        i < regs.len(),
        start_pc + base(i) + 5 <= m.instructions.len(),
        m.instructions[start_pc as int] == mk_dj(0, start_pc + 3),
        m.instructions[(start_pc + 1) as int] == mk_inc(1),
        m.instructions[(start_pc + 2) as int] == mk_jump(start_pc),
        m.instructions[(start_pc + 3) as int] == mk_dj(1, start_pc + base(i) + 5),
        forall|x: int| start_pc + 4 <= x < start_pc + 4 + base(i) ==> #[trigger] m.instructions[x] == mk_inc(0),
        m.instructions[(start_pc + base(i) + 4) as int] == mk_jump(start_pc + 3),
        c.pc == start_pc,
        c.registers.len() == 2,
        c.registers[0] == godel_encode(regs),
        c.registers[1] == 0,
    ensures
        exists|g: nat|
            1 <= g
            && run(m, c, g).pc == start_pc + base(i) + 5
            && run(m, c, g).registers[0] == godel_encode(regs.update(i as int, (regs[i as int] + 1) as nat))
            && run(m, c, g).registers[1] == 0
            && run(m, c, g).registers.len() == 2,
{
    let k = base(i);
    let v = godel_encode(regs);
    lemma_multiply_block(m, c, k, start_pc, v);   // C1 := k·v, fuel (k+5)v+2.
    lemma_godel_inc(regs, i);                     // godel(regs[r_i++]) == base(i)·godel(regs) == k·v.
    let g: nat = ((k + 5) * v + 2) as nat;
    assert(1 <= g);
    assert(run(m, c, g).registers[0] == k * v);
    assert(k * v == godel_encode(regs.update(i as int, (regs[i as int] + 1) as nat)));
}

//  ============================================================
//  M5 — `DecJump(r_i, t)`: Div? test, then divide (divisible) OR Jump-to-target (r_i = 0).
//  ============================================================
//
//  Block layout at `start_pc` (k = base(i)):
//    [start_pc, start_pc+2k+4)        Div? block (divtest), e1 = do_div_pc, notdiv = jump_pc
//    jump_pc  = start_pc+2k+4         Jump(target_block)         (the r_i = 0 path)
//    do_div_pc = start_pc+2k+5        divide block               (the r_i ≥ 1 path)
//    next_block = start_pc+3k+10      (= do_div_pc + k + 5)      fall-through after divide

/// **The `DecJump(r_i, t)` simulation.** From `C1 = godel_encode(regs)`, `C2 = 0` at `start_pc`:
///  - if `regs[r_i] ≥ 1`: `Div?` finds `base(i) | C1`, exits `do_div`, the divide block sets
///    `C1 := godel_encode(regs[r_i ← regs[r_i] − 1])` and reaches `next_block = start_pc + 3k + 10`;
///  - if `regs[r_i] = 0`: `Div?` finds `base(i) ∤ C1`, exits `jump_pc`, `Jump(target_block)` carries
///    the intact `C1 = godel_encode(regs)` to `target_block`.
pub proof fn lemma_decjump_sim(
    m: RegisterMachine, c: Configuration, regs: Seq<nat>, i: nat, start_pc: nat, target_block: nat,
)
    requires
        m.num_regs == 2,
        i < regs.len(),
        start_pc + 3 * base(i) + 10 <= m.instructions.len(),
        //  Div? (divtest) block at start_pc, e1 = start_pc+2k+5 (do_div), notdiv = start_pc+2k+4 (jump):
        m.instructions[start_pc as int] == mk_dj(0, start_pc + 3),
        m.instructions[(start_pc + 1) as int] == mk_inc(1),
        m.instructions[(start_pc + 2) as int] == mk_jump(start_pc),
        m.instructions[(start_pc + 3) as int] == mk_dj(1, start_pc + 2 * base(i) + 5),
        m.instructions[(start_pc + 3 + 2 * base(i)) as int] == mk_jump(start_pc + 3),
        forall|j: int| 0 <= j < base(i) ==> #[trigger] m.instructions[(start_pc + 3) + 2 * j + 1] == mk_inc(0),
        forall|j: int| 1 <= j < base(i) ==> #[trigger] m.instructions[(start_pc + 3) + 2 * j] == mk_dj(1, start_pc + 2 * base(i) + 4),
        //  Jump(target_block) at jump_pc = start_pc+2k+4 (the r_i = 0 exit):
        m.instructions[(start_pc + 2 * base(i) + 4) as int] == mk_jump(target_block),
        //  divide block at do_div_pc = start_pc+2k+5:
        m.instructions[(start_pc + 2 * base(i) + 5) as int] == mk_dj(0, start_pc + 2 * base(i) + 8),
        m.instructions[(start_pc + 2 * base(i) + 6) as int] == mk_inc(1),
        m.instructions[(start_pc + 2 * base(i) + 7) as int] == mk_jump(start_pc + 2 * base(i) + 5),
        forall|x: int| start_pc + 2 * base(i) + 8 <= x < start_pc + 3 * base(i) + 8
            ==> #[trigger] m.instructions[x] == mk_dj(1, start_pc + 3 * base(i) + 10),
        m.instructions[(start_pc + 3 * base(i) + 8) as int] == mk_inc(0),
        m.instructions[(start_pc + 3 * base(i) + 9) as int] == mk_jump(start_pc + 2 * base(i) + 8),
        c.pc == start_pc,
        c.registers.len() == 2,
        c.registers[0] == godel_encode(regs),
        c.registers[1] == 0,
    ensures
        exists|g: nat|
            1 <= g
            && run(m, c, g).registers.len() == 2
            && run(m, c, g).registers[1] == 0
            && (if regs[i as int] >= 1 {
                    run(m, c, g).pc == start_pc + 3 * base(i) + 10
                    && run(m, c, g).registers[0] == godel_encode(regs.update(i as int, (regs[i as int] - 1) as nat))
                } else {
                    run(m, c, g).pc == target_block
                    && run(m, c, g).registers[0] == godel_encode(regs)
                }),
{
    let k = base(i);
    let v = godel_encode(regs);
    let do_div_pc: nat = start_pc + 2 * k + 5;
    let jump_pc: nat = start_pc + 2 * k + 4;
    lemma_base_ge_2(i);   // k >= 2 >= 1
    //  Div? at start_pc: verdict v % k by lemma_godel_div_iff.
    lemma_divtest_block(m, c, k, start_pc, do_div_pc, jump_pc, v);
    let g_dt = choose|g: nat|
        run(m, c, g).pc == (if v % k == 0 { do_div_pc } else { jump_pc })
        && run(m, c, g).registers[0] == v
        && run(m, c, g).registers[1] == 0
        && run(m, c, g).registers.len() == 2;
    let c_dt = run(m, c, g_dt);
    lemma_godel_div_iff(regs, i);   // v % k == 0 <==> regs[i] >= 1
    if regs[i as int] >= 1 {
        //  --- divisible: v % k == 0, exit do_div_pc, then the divide block. ---
        assert(v % k == 0);
        assert(c_dt.pc == do_div_pc);
        assert(c_dt.registers[0] == v);
        assert(c_dt.registers[1] == 0);
        assert(c_dt.registers.len() == 2);
        //  v = base(i)·godel(regs[r_i--]) ⟹ C1 = k·groups for groups = godel(regs[r_i--]).
        lemma_godel_dec(regs, i);
        let groups: nat = godel_encode(regs.update(i as int, (regs[i as int] - 1) as nat));
        assert(v == k * groups);
        //  divide block: do_div_pc = start_pc+2k+5; its layout fields match the requires (see below).
        lemma_divide_block(m, c_dt, k, do_div_pc, groups);
        let f_div: nat = ((3 * (k * groups) + 1) + ((k + 2) * groups + 1)) as nat;
        assert(f_div >= 1);
        let c_div = run(m, c_dt, f_div);
        assert(do_div_pc + k + 5 == start_pc + 3 * k + 10);
        assert(c_div.pc == start_pc + 3 * k + 10);
        assert(c_div.registers[0] == groups);
        assert(c_div.registers[1] == 0);
        assert(c_div.registers.len() == 2);
        lemma_run_add(m, c, g_dt, f_div);
        let g: nat = (g_dt + f_div) as nat;
        assert(1 <= g);
        assert(run(m, c, g) == c_div);
        assert(run(m, c, g).registers[0] == godel_encode(regs.update(i as int, (regs[i as int] - 1) as nat)));
    } else {
        //  --- not divisible: r_i = 0, v % k != 0, exit jump_pc, then Jump(target_block). ---
        assert(regs[i as int] == 0);
        assert(v % k != 0);
        assert(c_dt.pc == jump_pc);
        assert(c_dt.registers[0] == v);
        assert(c_dt.registers[1] == 0);
        assert(c_dt.registers.len() == 2);
        assert(m.instructions[c_dt.pc as int] == mk_jump(target_block));
        assert(!is_halted(m, c_dt));
        lemma_run_unfold_step(m, c_dt, 1);
        let c_jmp = step(m, c_dt).unwrap();
        assert(c_jmp.pc == target_block);
        assert(c_jmp.registers == c_dt.registers);
        assert(run(m, c_dt, 1) == c_jmp);
        lemma_run_add(m, c, g_dt, 1);
        let g: nat = (g_dt + 1) as nat;
        assert(1 <= g);
        assert(run(m, c, g) == c_jmp);
        assert(run(m, c, g).registers[0] == v);
        assert(v == godel_encode(regs));
    }
}

//  ============================================================
//  M5 — `Jump(t)`: a single Jump to the translated target block.
//  ============================================================

/// **The `Jump(t)` simulation.** A single `Jump(target_block)` at `start_pc` carries the config
/// (registers untouched) to `target_block` in one step.
pub proof fn lemma_jump_sim(
    m: RegisterMachine, c: Configuration, start_pc: nat, target_block: nat,
)
    requires
        start_pc < m.instructions.len(),
        m.instructions[start_pc as int] == mk_jump(target_block),
        c.pc == start_pc,
    ensures
        run(m, c, 1).pc == target_block,
        run(m, c, 1).registers == c.registers,
{
    assert(!is_halted(m, c));
    lemma_run_unfold_step(m, c, 1);
    let c1 = step(m, c).unwrap();
    assert(c1.pc == target_block);
    assert(c1.registers == c.registers);
}

} //  verus!
