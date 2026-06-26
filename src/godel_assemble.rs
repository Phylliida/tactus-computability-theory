//! # GAP-2 L1 — M4: assembling `rm_k_to_rm2`, the k→2 Gödel reduction machine.
//!
//! Lays out the per-instruction RM(2) blocks (`godel_blocks.rs` / `godel_sim.rs`) end-to-end into one
//! flat `RegisterMachine` (num_regs = 2). Each RM(k) instruction at program position `pc` owns a
//! variable-size block starting at `block_start(instrs, pc)` (a **non-uniform prefix sum** of block
//! sizes — `Inc(r_i) = base(i)+5`, `DecJump(r_i,t) = 3·base(i)+10`, `Jump = Halt = 1`). Jump targets are
//! remapped through `block_start`, so an original target `t` becomes the RM(2) address `block_start(t)`.
//!
//! The headline deliverables:
//!  - **`rm_k_to_rm2`** — the assembled machine.
//!  - **`lemma_block_at`** — the layout-match (the `lemma_quint_at` / `lemma_gen_key` analog): the RM(2)
//!    instruction at `block_start(pc) + j` equals offset `j` of `pc`'s block. This discharges the
//!    address preconditions of the M5 per-instruction sims.
//!  - **`lemma_rm_k_to_rm2_wf`** — `machine_wf` of the assembled machine.
//!
//! The assembly recurses on the block *count* `n` (threading the full `instrs`), NOT on `drop_last`:
//! that keeps `block_start` and every remapped target referencing the SAME full machine, so forward
//! and backward jumps stay consistent. No verifier escape hatches.

use vstd::prelude::*;
use crate::machine::*;
use crate::multi_output_primitives::{mk_inc, mk_dj, mk_jump};
use crate::godel::{base, lemma_base_ge_2};
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse;

verus! {

//  ============================================================
//  Block sizes and the prefix-sum address map.
//  ============================================================

/// The number of RM(2) instructions an RM(k) instruction compiles to.
pub open spec fn block_size(instr: Instruction) -> nat {
    match instr {
        Instruction::Inc { register } => base(register) + 5,
        Instruction::DecJump { register, target } => 3 * base(register) + 10,
        Instruction::Jump { target } => 1,
        Instruction::Halt => 1,
    }
}

/// The RM(2) start address of the block for RM(k) position `pc` — the prefix sum of block sizes.
/// Defined for `pc <= instrs.len()`; `block_start(instrs, instrs.len())` is the total RM(2) length.
pub open spec fn block_start(instrs: Seq<Instruction>, pc: nat) -> nat
    decreases pc,
{
    if pc == 0 {
        0
    } else {
        block_start(instrs, (pc - 1) as nat) + block_size(instrs[(pc - 1) as int])
    }
}

//  ============================================================
//  The per-instruction blocks (offset-indexed; addresses absolute via `start`).
//  ============================================================

/// `Inc(r_i)` block (`base(i)+5` instrs): `move(C1→C2)` then `mult_back(C2→C1)×base(i)`. Exit (the
/// divtest-style fall-through at offset 3) is `start + base(i) + 5 = block_start(pc+1)`.
pub open spec fn inc_block(i: nat, start: nat) -> Seq<Instruction> {
    Seq::new(base(i) + 5, |j: int|
        if j == 0 { mk_dj(0, start + 3) }
        else if j == 1 { mk_inc(1) }
        else if j == 2 { mk_jump(start) }
        else if j == 3 { mk_dj(1, start + base(i) + 5) }
        else if j < base(i) + 4 { mk_inc(0) }
        else { mk_jump(start + 3) }
    )
}

/// `DecJump(r_i, t)` block (`3·base(i)+10` instrs): the non-destructive `Div?` test, then either the
/// destructive divide (divisible, `r_i ≥ 1`) falling through to `block_start(pc+1)`, or a `Jump(mt)` to
/// the remapped target `mt = block_start(t)` (the `r_i = 0` path). `k = base(i)`.
pub open spec fn decjump_block(i: nat, start: nat, mt: nat) -> Seq<Instruction> {
    Seq::new(3 * base(i) + 10, |o: int|
        if o == 0 { mk_dj(0, start + 3) }
        else if o == 1 { mk_inc(1) }
        else if o == 2 { mk_jump(start) }
        else if o == 3 { mk_dj(1, start + 2 * base(i) + 5) }
        else if o == 2 * base(i) + 3 { mk_jump(start + 3) }
        else if o < 2 * base(i) + 3 {
            if o % 2 == 0 { mk_inc(0) } else { mk_dj(1, start + 2 * base(i) + 4) }
        }
        else if o == 2 * base(i) + 4 { mk_jump(mt) }
        else if o == 2 * base(i) + 5 { mk_dj(0, start + 2 * base(i) + 8) }
        else if o == 2 * base(i) + 6 { mk_inc(1) }
        else if o == 2 * base(i) + 7 { mk_jump(start + 2 * base(i) + 5) }
        else if o < 3 * base(i) + 8 { mk_dj(1, start + 3 * base(i) + 10) }
        else if o == 3 * base(i) + 8 { mk_inc(0) }
        else { mk_jump(start + 2 * base(i) + 8) }
    )
}

/// The block for RM(k) position `pc`, with internal addresses absolute (start = `block_start(pc)`) and
/// external jump targets remapped through `block_start`.
pub open spec fn block_instrs(instrs: Seq<Instruction>, pc: nat) -> Seq<Instruction> {
    match instrs[pc as int] {
        Instruction::Inc { register } => inc_block(register, block_start(instrs, pc)),
        Instruction::DecJump { register, target } =>
            decjump_block(register, block_start(instrs, pc), block_start(instrs, target)),
        Instruction::Jump { target } => seq![mk_jump(block_start(instrs, target))],
        Instruction::Halt => seq![Instruction::Halt],
    }
}

//  ============================================================
//  The assembled machine: concat the first `n` blocks (recurse on count, thread full `instrs`).
//  ============================================================

/// The concatenation of the blocks for positions `0..n`. Length `block_start(instrs, n)`.
pub open spec fn rm2_prefix(instrs: Seq<Instruction>, n: nat) -> Seq<Instruction>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        rm2_prefix(instrs, (n - 1) as nat) + block_instrs(instrs, (n - 1) as nat)
    }
}

/// The full RM(2) instruction sequence.
pub open spec fn rm2_instrs(instrs: Seq<Instruction>) -> Seq<Instruction> {
    rm2_prefix(instrs, instrs.len())
}

/// The assembled 2-register machine simulating `rm_k` under the Gödel encoding `C1 = godel_encode(regs)`.
pub open spec fn rm_k_to_rm2(rm_k: RegisterMachine) -> RegisterMachine {
    RegisterMachine {
        instructions: rm2_instrs(rm_k.instructions),
        num_regs: 2,
    }
}

//  ============================================================
//  Basic structural lemmas: block lengths, prefix-sum step + monotonicity.
//  ============================================================

/// Each block's length is its `block_size`.
pub proof fn lemma_block_instrs_len(instrs: Seq<Instruction>, pc: nat)
    requires
        pc < instrs.len(),
    ensures
        block_instrs(instrs, pc).len() == block_size(instrs[pc as int]),
{
    match instrs[pc as int] {
        Instruction::Inc { register } => {
            assert(block_instrs(instrs, pc) == inc_block(register, block_start(instrs, pc)));
        },
        Instruction::DecJump { register, target } => {
            assert(block_instrs(instrs, pc)
                == decjump_block(register, block_start(instrs, pc), block_start(instrs, target)));
        },
        Instruction::Jump { target } => {
            assert(block_instrs(instrs, pc) == seq![mk_jump(block_start(instrs, target))]);
        },
        Instruction::Halt => {
            assert(block_instrs(instrs, pc) == seq![Instruction::Halt]);
        },
    }
}

/// One prefix-sum step: `block_start(pc+1) == block_start(pc) + block_size(instrs[pc])`.
pub proof fn lemma_block_start_step(instrs: Seq<Instruction>, pc: nat)
    ensures
        block_start(instrs, (pc + 1) as nat)
            == block_start(instrs, pc) + block_size(instrs[pc as int]),
{
}

/// `block_start` is monotone in the position.
pub proof fn lemma_block_start_le(instrs: Seq<Instruction>, a: nat, b: nat)
    requires
        a <= b,
    ensures
        block_start(instrs, a) <= block_start(instrs, b),
    decreases b,
{
    if a == b {
    } else {
        lemma_block_start_le(instrs, a, (b - 1) as nat);
        lemma_block_start_step(instrs, (b - 1) as nat);
        assert(b == (b - 1) + 1);
    }
}

/// `rm2_prefix(instrs, n)` has length `block_start(instrs, n)`.
pub proof fn lemma_rm2_prefix_len(instrs: Seq<Instruction>, n: nat)
    requires
        n <= instrs.len(),
    ensures
        rm2_prefix(instrs, n).len() == block_start(instrs, n),
    decreases n,
{
    if n == 0 {
    } else {
        lemma_rm2_prefix_len(instrs, (n - 1) as nat);
        lemma_block_instrs_len(instrs, (n - 1) as nat);
        lemma_block_start_step(instrs, (n - 1) as nat);
        assert(n == (n - 1) + 1);
    }
}

//  ============================================================
//  The layout-match: the RM(2) instruction at `block_start(pc)+j` is offset `j` of block `pc`.
//  ============================================================

/// **The layout-match (`lemma_quint_at` analog).** In the prefix of `n` blocks, the instruction at the
/// global address `block_start(pc) + j` equals offset `j` of `pc`'s block. Append preserves earlier
/// blocks' indices; the last block is the literal suffix.
pub proof fn lemma_block_at(instrs: Seq<Instruction>, n: nat, pc: nat, j: nat)
    requires
        pc < n,
        n <= instrs.len(),
        j < block_size(instrs[pc as int]),
    ensures
        rm2_prefix(instrs, n)[(block_start(instrs, pc) + j) as int]
            == block_instrs(instrs, pc)[j as int],
    decreases n,
{
    let prev = rm2_prefix(instrs, (n - 1) as nat);
    let blk = block_instrs(instrs, (n - 1) as nat);
    assert(rm2_prefix(instrs, n) == prev + blk) by { assert(n == (n - 1) + 1); }
    lemma_rm2_prefix_len(instrs, (n - 1) as nat);   //  prev.len() == block_start(instrs, n-1)
    let idx = (block_start(instrs, pc) + j) as int;
    if pc == (n - 1) as nat {
        lemma_block_instrs_len(instrs, (n - 1) as nat);   //  blk.len() == block_size(instrs[n-1])
        assert(block_start(instrs, pc) == prev.len());
        assert(idx == prev.len() + j);
        assert((prev + blk)[idx] == blk[j as int]);
        assert(blk == block_instrs(instrs, pc));
    } else {
        lemma_block_start_step(instrs, pc);
        lemma_block_start_le(instrs, (pc + 1) as nat, (n - 1) as nat);
        assert(idx < block_start(instrs, (pc + 1) as nat));
        assert(block_start(instrs, (pc + 1) as nat) <= prev.len());
        assert((prev + blk)[idx] == prev[idx]);
        lemma_block_at(instrs, (n - 1) as nat, pc, j);
    }
}

/// **The layout-match, specialised to the full machine `rm2_instrs`.** This is the form the M5 per-
/// instruction sims consume: the RM(2) instruction at `block_start(pc) + j` is offset `j` of block `pc`.
pub proof fn lemma_block_at_full(instrs: Seq<Instruction>, pc: nat, j: nat)
    requires
        pc < instrs.len(),
        j < block_size(instrs[pc as int]),
    ensures
        rm2_instrs(instrs)[(block_start(instrs, pc) + j) as int]
            == block_instrs(instrs, pc)[j as int],
{
    lemma_block_at(instrs, instrs.len(), pc, j);
}

//  ============================================================
//  Per-instruction layout extraction: the explicit `m.instructions[…]` facts the M5 sims require.
//  ============================================================

/// The total RM(2) length and the fact that block `pc` lies within it (the length bound the sims need).
pub proof fn lemma_rm2_len(instrs: Seq<Instruction>)
    ensures
        rm2_instrs(instrs).len() == block_start(instrs, instrs.len()),
{
    lemma_rm2_prefix_len(instrs, instrs.len());
}

/// **`Inc(r_i)` block layout.** At `start = block_start(pc)` the RM(2) instructions match exactly what
/// `lemma_inc_sim` requires (with `k = base(register)`), and the block fits within the machine.
pub proof fn lemma_inc_block_layout(instrs: Seq<Instruction>, pc: nat, i: nat)
    requires
        pc < instrs.len(),
        instrs[pc as int] == mk_inc(i),
    ensures
        block_start(instrs, pc) + base(i) + 5 <= rm2_instrs(instrs).len(),
        rm2_instrs(instrs)[block_start(instrs, pc) as int] == mk_dj(0, block_start(instrs, pc) + 3),
        rm2_instrs(instrs)[(block_start(instrs, pc) + 1) as int] == mk_inc(1),
        rm2_instrs(instrs)[(block_start(instrs, pc) + 2) as int] == mk_jump(block_start(instrs, pc)),
        rm2_instrs(instrs)[(block_start(instrs, pc) + 3) as int] == mk_dj(1, block_start(instrs, pc) + base(i) + 5),
        forall|x: int| block_start(instrs, pc) + 4 <= x < block_start(instrs, pc) + 4 + base(i)
            ==> #[trigger] rm2_instrs(instrs)[x] == mk_inc(0),
        rm2_instrs(instrs)[(block_start(instrs, pc) + base(i) + 4) as int] == mk_jump(block_start(instrs, pc) + 3),
{
    let start = block_start(instrs, pc);
    let k = base(i);
    assert(block_instrs(instrs, pc) == inc_block(i, start));
    //  length bound: start + k + 5 == block_start(pc+1) <= block_start(len) == rm2 length.
    lemma_block_start_step(instrs, pc);
    lemma_block_start_le(instrs, (pc + 1) as nat, instrs.len());
    lemma_rm2_len(instrs);
    //  point facts (offsets 0,1,2,3 and k+4):
    lemma_block_at_full(instrs, pc, 0);
    lemma_block_at_full(instrs, pc, 1);
    lemma_block_at_full(instrs, pc, 2);
    lemma_block_at_full(instrs, pc, 3);
    lemma_block_at_full(instrs, pc, (k + 4) as nat);
    //  the Inc(0) run, offsets [4, 4+k):
    assert forall|x: int| start + 4 <= x < start + 4 + k
        implies #[trigger] rm2_instrs(instrs)[x] == mk_inc(0) by {
        let j = (x - start) as nat;
        lemma_block_at_full(instrs, pc, j);
        assert(start + j == x);
    }
}

/// **`Jump(t)` block layout.** A single `Jump(block_start(t))` at `start = block_start(pc)`.
pub proof fn lemma_jump_block_layout(instrs: Seq<Instruction>, pc: nat, t: nat)
    requires
        pc < instrs.len(),
        instrs[pc as int] == mk_jump(t),
    ensures
        block_start(instrs, pc) < rm2_instrs(instrs).len(),
        rm2_instrs(instrs)[block_start(instrs, pc) as int] == mk_jump(block_start(instrs, t)),
{
    let start = block_start(instrs, pc);
    assert(block_instrs(instrs, pc) == seq![mk_jump(block_start(instrs, t))]);
    assert(block_size(instrs[pc as int]) == 1);
    lemma_block_start_step(instrs, pc);
    lemma_block_start_le(instrs, (pc + 1) as nat, instrs.len());
    lemma_rm2_len(instrs);
    lemma_block_at_full(instrs, pc, 0);
}

//  --- DecJump layout: the three forall ranges, isolated into helpers (ghost-equality `start`). ---

/// The `Inc(0)` cells of the `Div?` body: offsets `2j+4` for `0 ≤ j < k` (even offsets in `[4, 2k+2]`).
proof fn lemma_decjump_inc_run(instrs: Seq<Instruction>, pc: nat, i: nat, t: nat, start: nat)
    requires
        pc < instrs.len(),
        instrs[pc as int] == mk_dj(i, t),
        start == block_start(instrs, pc),
    ensures
        forall|j: int| 0 <= j < base(i)
            ==> #[trigger] rm2_instrs(instrs)[(start + 3) + 2 * j + 1] == mk_inc(0),
{
    let k = base(i);
    assert(block_instrs(instrs, pc) == decjump_block(i, start, block_start(instrs, t)));
    assert forall|j: int| 0 <= j < k
        implies #[trigger] rm2_instrs(instrs)[(start + 3) + 2 * j + 1] == mk_inc(0) by {
        let o = (2 * j + 4) as nat;
        assert((start + 3) + 2 * j + 1 == start + o);
        assert(o < 3 * k + 10);
        lemma_block_at_full(instrs, pc, o);
        assert(o as int == (j + 2) * 2);
        lemma_fundamental_div_mod_converse(o as int, 2, j + 2, 0);
        assert(o % 2 == 0);
        assert(o < 2 * k + 3);
    }
}

/// The `DecJump(1, notdiv)` cells of the `Div?` body: offsets `2j+3` for `1 ≤ j < k` (odd, `[5, 2k+1]`).
proof fn lemma_decjump_dj_run(instrs: Seq<Instruction>, pc: nat, i: nat, t: nat, start: nat)
    requires
        pc < instrs.len(),
        instrs[pc as int] == mk_dj(i, t),
        start == block_start(instrs, pc),
    ensures
        forall|j: int| 1 <= j < base(i)
            ==> #[trigger] rm2_instrs(instrs)[(start + 3) + 2 * j] == mk_dj(1, start + 2 * base(i) + 4),
{
    let k = base(i);
    assert(block_instrs(instrs, pc) == decjump_block(i, start, block_start(instrs, t)));
    assert forall|j: int| 1 <= j < k
        implies #[trigger] rm2_instrs(instrs)[(start + 3) + 2 * j] == mk_dj(1, start + 2 * k + 4) by {
        let o = (2 * j + 3) as nat;
        assert((start + 3) + 2 * j == start + o);
        assert(o < 3 * k + 10);
        lemma_block_at_full(instrs, pc, o);
        assert(o as int == (j + 1) * 2 + 1);
        lemma_fundamental_div_mod_converse(o as int, 2, j + 1, 1);
        assert(o % 2 == 1);
        assert(o < 2 * k + 3);
        assert(o != 3);
    }
}

/// The divide block's `DecJump(1, next)` run: global addresses `[start+2k+8, start+3k+8)`.
proof fn lemma_decjump_div_run(instrs: Seq<Instruction>, pc: nat, i: nat, t: nat, start: nat)
    requires
        pc < instrs.len(),
        instrs[pc as int] == mk_dj(i, t),
        start == block_start(instrs, pc),
    ensures
        forall|x: int| start + 2 * base(i) + 8 <= x < start + 3 * base(i) + 8
            ==> #[trigger] rm2_instrs(instrs)[x] == mk_dj(1, start + 3 * base(i) + 10),
{
    let k = base(i);
    assert(block_instrs(instrs, pc) == decjump_block(i, start, block_start(instrs, t)));
    assert forall|x: int| start + 2 * k + 8 <= x < start + 3 * k + 8
        implies #[trigger] rm2_instrs(instrs)[x] == mk_dj(1, start + 3 * k + 10) by {
        let o = (x - start) as nat;
        assert(start + o == x);
        assert(o < 3 * k + 10);
        lemma_block_at_full(instrs, pc, o);
    }
}

/// **`DecJump(r_i, t)` block layout.** At `start = block_start(pc)` the RM(2) instructions match exactly
/// what `lemma_decjump_sim` requires (with `k = base(register)`, `target_block = block_start(t)`).
pub proof fn lemma_decjump_block_layout(instrs: Seq<Instruction>, pc: nat, i: nat, t: nat)
    requires
        pc < instrs.len(),
        instrs[pc as int] == mk_dj(i, t),
    ensures
        block_start(instrs, pc) + 3 * base(i) + 10 <= rm2_instrs(instrs).len(),
        rm2_instrs(instrs)[block_start(instrs, pc) as int] == mk_dj(0, block_start(instrs, pc) + 3),
        rm2_instrs(instrs)[(block_start(instrs, pc) + 1) as int] == mk_inc(1),
        rm2_instrs(instrs)[(block_start(instrs, pc) + 2) as int] == mk_jump(block_start(instrs, pc)),
        rm2_instrs(instrs)[(block_start(instrs, pc) + 3) as int] == mk_dj(1, block_start(instrs, pc) + 2 * base(i) + 5),
        rm2_instrs(instrs)[(block_start(instrs, pc) + 3 + 2 * base(i)) as int] == mk_jump(block_start(instrs, pc) + 3),
        forall|j: int| 0 <= j < base(i)
            ==> #[trigger] rm2_instrs(instrs)[(block_start(instrs, pc) + 3) + 2 * j + 1] == mk_inc(0),
        forall|j: int| 1 <= j < base(i)
            ==> #[trigger] rm2_instrs(instrs)[(block_start(instrs, pc) + 3) + 2 * j] == mk_dj(1, block_start(instrs, pc) + 2 * base(i) + 4),
        rm2_instrs(instrs)[(block_start(instrs, pc) + 2 * base(i) + 4) as int] == mk_jump(block_start(instrs, t)),
        rm2_instrs(instrs)[(block_start(instrs, pc) + 2 * base(i) + 5) as int] == mk_dj(0, block_start(instrs, pc) + 2 * base(i) + 8),
        rm2_instrs(instrs)[(block_start(instrs, pc) + 2 * base(i) + 6) as int] == mk_inc(1),
        rm2_instrs(instrs)[(block_start(instrs, pc) + 2 * base(i) + 7) as int] == mk_jump(block_start(instrs, pc) + 2 * base(i) + 5),
        forall|x: int| block_start(instrs, pc) + 2 * base(i) + 8 <= x < block_start(instrs, pc) + 3 * base(i) + 8
            ==> #[trigger] rm2_instrs(instrs)[x] == mk_dj(1, block_start(instrs, pc) + 3 * base(i) + 10),
        rm2_instrs(instrs)[(block_start(instrs, pc) + 3 * base(i) + 8) as int] == mk_inc(0),
        rm2_instrs(instrs)[(block_start(instrs, pc) + 3 * base(i) + 9) as int] == mk_jump(block_start(instrs, pc) + 2 * base(i) + 8),
{
    let start = block_start(instrs, pc);
    let k = base(i);
    assert(block_instrs(instrs, pc) == decjump_block(i, start, block_start(instrs, t)));
    //  length bound.
    lemma_block_start_step(instrs, pc);
    lemma_block_start_le(instrs, (pc + 1) as nat, instrs.len());
    lemma_rm2_len(instrs);
    //  point facts (offsets resolve through the closure's if-chain).
    lemma_block_at_full(instrs, pc, 0);
    lemma_block_at_full(instrs, pc, 1);
    lemma_block_at_full(instrs, pc, 2);
    lemma_block_at_full(instrs, pc, 3);
    lemma_block_at_full(instrs, pc, (2 * k + 3) as nat);
    lemma_block_at_full(instrs, pc, (2 * k + 4) as nat);
    lemma_block_at_full(instrs, pc, (2 * k + 5) as nat);
    lemma_block_at_full(instrs, pc, (2 * k + 6) as nat);
    lemma_block_at_full(instrs, pc, (2 * k + 7) as nat);
    lemma_block_at_full(instrs, pc, (3 * k + 8) as nat);
    lemma_block_at_full(instrs, pc, (3 * k + 9) as nat);
    //  the three forall ranges.
    lemma_decjump_inc_run(instrs, pc, i, t, start);
    lemma_decjump_dj_run(instrs, pc, i, t, start);
    lemma_decjump_div_run(instrs, pc, i, t, start);
}

//  ============================================================
//  Well-formedness of the assembled machine.
//  ============================================================

/// An RM(2) instruction is well-formed against total length `len`: registers `< 2`, targets `≤ len`.
pub open spec fn instr_wf2(instr: Instruction, len: nat) -> bool {
    match instr {
        Instruction::Inc { register } => register < 2,
        Instruction::DecJump { register, target } => register < 2 && target <= len,
        Instruction::Jump { target } => target <= len,
        Instruction::Halt => true,
    }
}

/// Every instruction in block `pc` is well-formed against the total RM(2) length. Registers are only
/// `0`/`1`; internal/fall-through targets are `≤ block_start(pc+1)`, the remapped external target is
/// `block_start(t) ≤ total` (`t ≤ rm_k.len()` from `machine_wf`).
proof fn lemma_block_wf(rm_k: RegisterMachine, pc: nat)
    requires
        machine_wf(rm_k),
        pc < rm_k.instructions.len(),
    ensures
        forall|o: int| 0 <= o < block_size(rm_k.instructions[pc as int])
            ==> instr_wf2(#[trigger] block_instrs(rm_k.instructions, pc)[o],
                          block_start(rm_k.instructions, rm_k.instructions.len())),
{
    let instrs = rm_k.instructions;
    let total = block_start(instrs, instrs.len());
    let start = block_start(instrs, pc);
    reveal(machine_wf);
    lemma_block_start_step(instrs, pc);                              //  block_start(pc+1) == start + size
    lemma_block_start_le(instrs, (pc + 1) as nat, instrs.len());     //  block_start(pc+1) <= total
    lemma_block_instrs_len(instrs, pc);
    match instrs[pc as int] {
        Instruction::Inc { register } => {
            assert(block_instrs(instrs, pc) == inc_block(register, start));
            assert forall|o: int| 0 <= o < block_size(instrs[pc as int])
                implies instr_wf2(#[trigger] block_instrs(instrs, pc)[o], total) by {
            }
        },
        Instruction::DecJump { register, target } => {
            assert(target <= instrs.len());
            lemma_block_start_le(instrs, target, instrs.len());     //  block_start(target) <= total
            assert(block_instrs(instrs, pc) == decjump_block(register, start, block_start(instrs, target)));
            assert forall|o: int| 0 <= o < block_size(instrs[pc as int])
                implies instr_wf2(#[trigger] block_instrs(instrs, pc)[o], total) by {
            }
        },
        Instruction::Jump { target } => {
            assert(target <= instrs.len());
            lemma_block_start_le(instrs, target, instrs.len());
            assert(block_instrs(instrs, pc) == seq![mk_jump(block_start(instrs, target))]);
        },
        Instruction::Halt => {
            assert(block_instrs(instrs, pc) == seq![Instruction::Halt]);
        },
    }
}

/// Every instruction in the prefix of `n` blocks is well-formed against the total RM(2) length.
proof fn lemma_rm2_prefix_wf(rm_k: RegisterMachine, n: nat)
    requires
        machine_wf(rm_k),
        n <= rm_k.instructions.len(),
    ensures
        forall|idx: int| 0 <= idx < rm2_prefix(rm_k.instructions, n).len()
            ==> instr_wf2(#[trigger] rm2_prefix(rm_k.instructions, n)[idx],
                          block_start(rm_k.instructions, rm_k.instructions.len())),
    decreases n,
{
    let instrs = rm_k.instructions;
    let total = block_start(instrs, instrs.len());
    if n == 0 {
    } else {
        let prev = rm2_prefix(instrs, (n - 1) as nat);
        let blk = block_instrs(instrs, (n - 1) as nat);
        assert(rm2_prefix(instrs, n) == prev + blk) by { assert(n == (n - 1) + 1); }
        lemma_rm2_prefix_wf(rm_k, (n - 1) as nat);
        lemma_rm2_prefix_len(instrs, (n - 1) as nat);       //  prev.len() == block_start(n-1)
        lemma_block_instrs_len(instrs, (n - 1) as nat);     //  blk.len() == block_size
        lemma_block_wf(rm_k, (n - 1) as nat);
        assert forall|idx: int| 0 <= idx < rm2_prefix(instrs, n).len()
            implies instr_wf2(#[trigger] rm2_prefix(instrs, n)[idx], total) by {
            if idx < prev.len() {
                assert((prev + blk)[idx] == prev[idx]);
            } else {
                assert((prev + blk)[idx] == blk[idx - prev.len()]);
            }
        }
    }
}

/// **`machine_wf` of the assembled RM(2) machine.** `num_regs = 2 > 0`; every instruction is
/// well-formed against the total length.
pub proof fn lemma_rm_k_to_rm2_wf(rm_k: RegisterMachine)
    requires
        machine_wf(rm_k),
    ensures
        machine_wf(rm_k_to_rm2(rm_k)),
{
    let instrs = rm_k.instructions;
    let m2 = rm_k_to_rm2(rm_k);
    let total = block_start(instrs, instrs.len());
    lemma_rm2_prefix_wf(rm_k, instrs.len());
    lemma_rm2_len(instrs);     //  m2.instructions.len() == total
    reveal(machine_wf);
    assert forall|i: int| 0 <= i < m2.instructions.len()
        implies (match #[trigger] m2.instructions[i] {
            Instruction::Inc { register } => register < m2.num_regs,
            Instruction::DecJump { register, target } => register < m2.num_regs && target <= m2.instructions.len(),
            Instruction::Jump { target } => target <= m2.instructions.len(),
            Instruction::Halt => true,
        }) by {
        assert(instr_wf2(m2.instructions[i], total));
    }
}

} //  verus!
