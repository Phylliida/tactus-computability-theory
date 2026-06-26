//! # GAP-2 L1 — M3: the per-instruction RM(2) block compositions.
//!
//! Composes M1's `move` gadget with the M1/M2 back-loops into the three RM(2) operations the k→2
//! Gödel reduction needs, at the **register-machine value level** (the Gödel connection
//! `C1 = godel_encode(regs)` is applied at M5). RM(2): `reg 0 = C1` (the Gödel number),
//! `reg 1 = C2` (scratch, `= 0` between blocks). Each block is `move (C1→C2)` followed by a back-loop
//! that processes `C2` into `C1`:
//!  - **`lemma_multiply_block`** (`C1 := k·C1`, the `Inc(r_i)` op, `k = base(i)`): `move` +
//!    M1 `mult_back`. Closed-form fuel `(k+5)·v + 2`.
//!  - **`lemma_divide_block`** (`C1 := C1/k` for `C1 = k·groups`, the `DecJump` decrement op): `move` +
//!    M2 `div_back`. Closed-form fuel.
//!  - **`lemma_divtest_block`** (non-destructive test `k | C1`, the `DecJump` zero-test): `move` +
//!    M2 `divtest`. Existential fuel; verdict in the exit pc (`e1_pc ⟺ v % k == 0`), `C1` restored.
//!
//! Each block begins with its OWN `move (C1→C2)`; `divtest` restores `C1`, so a following `divide`
//! block's `move` sees the intact `C1`. Parametric in `k` and the block start/exit addresses (so M4's
//! global address map plugs in without touching these proofs). No verifier escape hatches.

use vstd::prelude::*;
use crate::machine::*;
use crate::multi_output_primitives::{mk_inc, mk_dj, mk_jump};
use crate::godel_gadgets::{lemma_move_loop, lemma_mult_back_loop};
use crate::godel_gadgets2::{lemma_div_back_loop, lemma_divtest_back_loop};
use crate::search_rm_arith::lemma_run_preserves_len;

verus! {

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
//  M3 — the multiply block:  C1 := k · C1   (the `Inc(r_i)` op, k = base(i)).
//  ============================================================
//
//  Layout at `start_pc` (k + 5 instructions, exit pc = start_pc + k + 5):
//    +0..+2     move(C1→C2)      [DecJump(0, start_pc+3), Inc(1), Jump(start_pc)]
//    +3         mult_back head   DecJump(1, start_pc+k+5)
//    +4..+3+k   Inc(0) × k
//    +k+4       mult_back jump   Jump(start_pc+3)

/// **The multiply block.** From `c.registers[0] = v` (C1), `c.registers[1] = 0` (C2) at `start_pc`,
/// runs `(k+5)·v + 2` steps to `start_pc + k + 5` with `C1 := k·v`, `C2 := 0`. `move` drains C1 into
/// C2, then `mult_back` rebuilds `C1 := k·(old C1)`.
pub proof fn lemma_multiply_block(
    m: RegisterMachine, c: Configuration, k: nat, start_pc: nat, v: nat,
)
    requires
        m.num_regs == 2,
        start_pc + k + 5 <= m.instructions.len(),
        //  move(C1→C2) at start_pc:
        m.instructions[start_pc as int] == mk_dj(0, start_pc + 3),
        m.instructions[(start_pc + 1) as int] == mk_inc(1),
        m.instructions[(start_pc + 2) as int] == mk_jump(start_pc),
        //  mult_back(C2→C1, k) at start_pc+3:
        m.instructions[(start_pc + 3) as int] == mk_dj(1, start_pc + k + 5),
        forall|i: int| start_pc + 4 <= i < start_pc + 4 + k ==> #[trigger] m.instructions[i] == mk_inc(0),
        m.instructions[(start_pc + k + 4) as int] == mk_jump(start_pc + 3),
        c.pc == start_pc,
        c.registers.len() == 2,
        c.registers[0] == v,
        c.registers[1] == 0,
    ensures
        run(m, c, (k + 5) * v + 2).pc == start_pc + k + 5,
        run(m, c, (k + 5) * v + 2).registers[0] == k * v,
        run(m, c, (k + 5) * v + 2).registers[1] == 0,
        run(m, c, (k + 5) * v + 2).registers.len() == 2,
{
    //  --- move(0→1): C1=v drains into C2, C1:=0. fuel 3v+1. ---
    lemma_move_loop(m, c, 0, 1, start_pc, v, 0, v);
    let c_mv = run(m, c, 3 * v + 1);
    lemma_run_preserves_len(m, c, 3 * v + 1);
    assert(c_mv.pc == start_pc + 3);
    assert(c_mv.registers[1] == v);   // dst=1 = orig_val
    assert(c_mv.registers[0] == 0);   // src=0
    assert(c_mv.registers.len() == 2);
    //  --- mult_back(1→0, k): C1 := 0 + k·v, C2 := 0. fuel (k+2)v+1. ---
    lemma_mult_back_loop(m, c_mv, 1, 0, k, start_pc + 3, 0, v);
    let c_mb = run(m, c_mv, (k + 2) * v + 1);
    lemma_run_preserves_len(m, c_mv, (k + 2) * v + 1);
    assert((start_pc + 3) + k + 2 == start_pc + k + 5);
    assert(c_mb.pc == start_pc + k + 5);
    assert(c_mb.registers[0] == k * v);   // dst=0 = acc + k·remaining = 0 + k·v
    assert(c_mb.registers[1] == 0);        // src=1
    assert(c_mb.registers.len() == 2);
    //  --- chain the fuel:  (3v+1) + ((k+2)v+1) == (k+5)v+2. ---
    assert((3 * v + 1) + ((k + 2) * v + 1) == (k + 5) * v + 2) by(nonlinear_arith);
    lemma_run_add(m, c, 3 * v + 1, (k + 2) * v + 1);
    assert(run(m, c, (k + 5) * v + 2) == c_mb);
}

//  ============================================================
//  M3 — the divide block:  C1 := C1 / k   (the `DecJump` decrement op, requires C1 = k·groups).
//  ============================================================
//
//  Layout at `start_pc` (k + 5 instructions, exit pc = start_pc + k + 5):
//    +0..+2     move(C1→C2)      [DecJump(0, start_pc+3), Inc(1), Jump(start_pc)]
//    +3..+2+k   div_back DecJumps  DecJump(1, start_pc+k+5) × k
//    +3+k       div_back Inc     Inc(0)
//    +k+4       div_back jump    Jump(start_pc+3)

/// **The divide block.** From `c.registers[0] = k·groups` (C1), `c.registers[1] = 0` (C2) at
/// `start_pc`, runs `(3·(k·groups) + 1) + ((k+2)·groups + 1)` steps to `start_pc + k + 5` with
/// `C1 := groups`, `C2 := 0`. Invoked ONLY on the divisible branch (a `Div?` verdict already
/// established `k | C1`, so `C1 = k·groups`). `move` drains C1 into C2, then `div_back` rebuilds
/// `C1 := C2/k`.
pub proof fn lemma_divide_block(
    m: RegisterMachine, c: Configuration, k: nat, start_pc: nat, groups: nat,
)
    requires
        k >= 1,
        m.num_regs == 2,
        start_pc + k + 5 <= m.instructions.len(),
        //  move(C1→C2) at start_pc:
        m.instructions[start_pc as int] == mk_dj(0, start_pc + 3),
        m.instructions[(start_pc + 1) as int] == mk_inc(1),
        m.instructions[(start_pc + 2) as int] == mk_jump(start_pc),
        //  div_back(C2→C1, k) at start_pc+3:
        forall|i: int| start_pc + 3 <= i < start_pc + 3 + k ==> #[trigger] m.instructions[i] == mk_dj(1, start_pc + k + 5),
        m.instructions[(start_pc + 3 + k) as int] == mk_inc(0),
        m.instructions[(start_pc + k + 4) as int] == mk_jump(start_pc + 3),
        c.pc == start_pc,
        c.registers.len() == 2,
        c.registers[0] == k * groups,
        c.registers[1] == 0,
    ensures
        run(m, c, (3 * (k * groups) + 1) + ((k + 2) * groups + 1)).pc == start_pc + k + 5,
        run(m, c, (3 * (k * groups) + 1) + ((k + 2) * groups + 1)).registers[0] == groups,
        run(m, c, (3 * (k * groups) + 1) + ((k + 2) * groups + 1)).registers[1] == 0,
        run(m, c, (3 * (k * groups) + 1) + ((k + 2) * groups + 1)).registers.len() == 2,
{
    let v: nat = k * groups;
    //  --- move(0→1): C1=k·groups drains into C2, C1:=0. fuel 3v+1. ---
    lemma_move_loop(m, c, 0, 1, start_pc, v, 0, v);
    let c_mv = run(m, c, 3 * v + 1);
    lemma_run_preserves_len(m, c, 3 * v + 1);
    assert(c_mv.pc == start_pc + 3);
    assert(c_mv.registers[1] == v);   // C2 = k·groups
    assert(c_mv.registers[0] == 0);
    assert(c_mv.registers.len() == 2);
    //  --- div_back(1→0, k): C1 := 0 + groups, C2 := 0. fuel (k+2)·groups+1. ---
    lemma_div_back_loop(m, c_mv, 1, 0, k, start_pc + 3, 0, groups);
    let c_db = run(m, c_mv, (k + 2) * groups + 1);
    lemma_run_preserves_len(m, c_mv, (k + 2) * groups + 1);
    assert((start_pc + 3) + k + 2 == start_pc + k + 5);
    assert(c_db.pc == start_pc + k + 5);
    assert(c_db.registers[0] == groups);   // dst=0 = acc + groups = 0 + groups
    assert(c_db.registers[1] == 0);
    assert(c_db.registers.len() == 2);
    //  --- chain the fuel ---
    lemma_run_add(m, c, 3 * v + 1, (k + 2) * groups + 1);
    assert(run(m, c, (3 * v + 1) + ((k + 2) * groups + 1)) == c_db);
}

//  ============================================================
//  M3 — the divtest block: non-destructive `k | C1` test (the `DecJump` zero-test).
//  ============================================================
//
//  Layout at `start_pc` (2k + 4 instructions; exits e1_pc / notdiv_pc are EXTERNAL block addresses):
//    +0..+2     move(C1→C2)      [DecJump(0, start_pc+3), Inc(1), Jump(start_pc)]
//    +3..+3+2k  divtest_back     (2k+1 instrs) at start_pc+3

/// **The divtest block.** From `c.registers[0] = v` (C1), `c.registers[1] = 0` (C2) at `start_pc`,
/// runs (existential fuel) to either `e1_pc` (iff `v % k == 0` — divisible) or `notdiv_pc`, restoring
/// `C1 := v` and `C2 := 0` on **both** exits (non-destructive: the verdict is the exit pc). `move`
/// drains C1 into C2, then `divtest` walks C2 down rebuilding C1.
pub proof fn lemma_divtest_block(
    m: RegisterMachine, c: Configuration, k: nat, start_pc: nat, e1_pc: nat, notdiv_pc: nat, v: nat,
)
    requires
        k >= 1,
        m.num_regs == 2,
        start_pc + 2 * k + 4 <= m.instructions.len(),
        //  move(C1→C2) at start_pc:
        m.instructions[start_pc as int] == mk_dj(0, start_pc + 3),
        m.instructions[(start_pc + 1) as int] == mk_inc(1),
        m.instructions[(start_pc + 2) as int] == mk_jump(start_pc),
        //  divtest_back(C2→C1, k) at start_pc+3:
        m.instructions[(start_pc + 3) as int] == mk_dj(1, e1_pc),
        m.instructions[(start_pc + 3 + 2 * k) as int] == mk_jump(start_pc + 3),
        forall|j: int| 0 <= j < k ==> #[trigger] m.instructions[(start_pc + 3) + 2 * j + 1] == mk_inc(0),
        forall|j: int| 1 <= j < k ==> #[trigger] m.instructions[(start_pc + 3) + 2 * j] == mk_dj(1, notdiv_pc),
        c.pc == start_pc,
        c.registers.len() == 2,
        c.registers[0] == v,
        c.registers[1] == 0,
    ensures
        exists|g: nat|
            run(m, c, g).pc == (if v % k == 0 { e1_pc } else { notdiv_pc })
            && run(m, c, g).registers[0] == v
            && run(m, c, g).registers[1] == 0
            && run(m, c, g).registers.len() == 2,
{
    //  --- move(0→1): C1=v drains into C2, C1:=0. fuel 3v+1. ---
    lemma_move_loop(m, c, 0, 1, start_pc, v, 0, v);
    let c_mv = run(m, c, 3 * v + 1);
    lemma_run_preserves_len(m, c, 3 * v + 1);
    assert(c_mv.pc == start_pc + 3);
    assert(c_mv.registers[1] == v);   // C2 = v
    assert(c_mv.registers[0] == 0);
    assert(c_mv.registers.len() == 2);
    //  --- divtest_back(1→0, k): walk C2 down, rebuild into C1 := v; exit e1/notdiv by v%k. ---
    lemma_divtest_back_loop(m, c_mv, 1, 0, k, start_pc + 3, e1_pc, notdiv_pc, 0, v);
    let g_dt = choose|g: nat|
        run(m, c_mv, g).pc == (if v % k == 0 { e1_pc } else { notdiv_pc })
        && run(m, c_mv, g).registers[1 as int] == 0
        && run(m, c_mv, g).registers[0 as int] == 0 + v
        && run(m, c_mv, g).registers.len() == 2
        && (forall|r: int| 0 <= r < 2int && r != 1int && r != 0int
                ==> #[trigger] run(m, c_mv, g).registers[r] == c_mv.registers[r]);
    //  --- chain: run(m, c, (3v+1) + g_dt) == run(m, c_mv, g_dt). ---
    lemma_run_add(m, c, 3 * v + 1, g_dt);
    let g: nat = (3 * v + 1 + g_dt) as nat;
    assert(run(m, c, g) == run(m, c_mv, g_dt));
    assert(run(m, c, g).registers[0] == v);
    assert(run(m, c, g).registers[1] == 0);
}

} //  verus!
