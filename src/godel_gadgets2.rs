//! # GAP-2 L1 — M2: the divide + non-destructive divisibility-test gadgets.
//!
//! Continuation of `godel_gadgets.rs` (M1: move + multiply). Register-machine gadgets over the
//! `{Inc, DecJump, Jump}` instruction set with **no free scratch** (the 2-counter setting); every
//! unconditional loop back-edge is a `Jump` (the R-ii primitive). Building blocks of the k→2 Gödel
//! reduction `RM(k) → RM(2)`, where `C1 = ∏ base(i)^{r_i}` and `C2` is the single scratch counter.
//!
//! Provides (all PARAMETRIC in `k`, instantiated at `k = base(i)` so the doubly-exponential Sylvester
//! magnitude never enters the proofs):
//!  - **`lemma_dec_block`** — a straight-line block of `count` `DecJump(reg, target)` instructions,
//!    when `reg ≥ count`, falls through and decrements `reg` by `count` (the dual of `lemma_inc_block`).
//!  - **`lemma_div_back_loop`** (destructive divide, `÷k`): `[DecJump(src, done)×k, Inc(dst), Jump]`,
//!    drains `src = k·groups` adding `1` to `dst` per group ⇒ `dst += groups`. Used ONLY on the
//!    divisible branch (after a `Div?` verdict), so the precondition is `src = k·groups`.
//!  - **`lemma_divtest_back_loop`** (NON-destructive divisibility test `Div?((n),k)[E1]`): walks `src`
//!    down in groups of `k` while **rebuilding `src` into `dst`**, exiting to `e1_pc` (group head hits
//!    zero ⇒ divisible) or `notdiv_pc` (mid-group zero ⇒ not divisible). On **both** exits
//!    `dst = orig`, `src = 0` — the verdict is carried purely in WHICH exit (`remaining % k == 0`),
//!    no quotient left to undo. The inner `[DecJump(src, notdiv); Inc(dst)]×(k−1)` pair block is
//!    handled by the helper `lemma_pair_block`.
//!
//! Fully verified, no verifier escape hatches. See `docs/gap2-register-to-tm-plan.md`
//! §"k→2 GADGET DESIGN LOCKED".

use vstd::prelude::*;
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse};
use crate::machine::*;
use crate::multi_output_primitives::{mk_inc, mk_dj, mk_jump};
use crate::godel_gadgets::lemma_inc_block;

verus! {

//  ============================================================
//  Run-composition helpers (per-module local copies, avoid cross-module trigger pollution).
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
//  Modular helper: subtracting one full `k` preserves the residue.
//  ============================================================

/// `(x − k) % k == x % k`, for `x ≥ k ≥ 1`. The residue invariant of the `Div?`/`÷k` group loops.
proof fn lemma_mod_sub_k(x: nat, k: nat)
    requires
        k >= 1,
        x >= k,
    ensures
        ((x - k) as nat) % k == x % k,
{
    let xi = x as int;
    let ki = k as int;
    lemma_fundamental_div_mod(xi, ki);   // xi == ki*(xi/ki) + xi%ki, 0 <= xi%ki < ki
    let q = xi / ki;
    let r = xi % ki;
    assert(xi == ki * q + r);
    assert((xi - ki) == ki * (q - 1) + r) by(nonlinear_arith)
        requires xi == ki * q + r;
    assert(0 <= r < ki);
    lemma_fundamental_div_mod_converse(xi - ki, ki, q - 1, r);   // (xi-ki) % ki == r
    assert(((x - k) as nat) % k == (xi - ki) % ki);
}

//  ============================================================
//  M2 — the dec block: `count` consecutive `DecJump(reg, target)` fall through when `reg ≥ count`.
//  ============================================================

/// Running `count` consecutive `DecJump(reg, target)` instructions from `start_pc`, when
/// `reg ≥ count` (so every one decrements rather than jumping), subtracts `count` from `reg`
/// (all other registers unchanged), advancing the pc to `start_pc + count`. The dual of
/// `lemma_inc_block`.
pub proof fn lemma_dec_block(
    m: RegisterMachine, c: Configuration, reg: nat, target: nat, count: nat, start_pc: nat,
)
    requires
        start_pc + count <= m.instructions.len(),
        forall|i: int| start_pc <= i < start_pc + count ==> #[trigger] m.instructions[i] == mk_dj(reg, target),
        c.pc == start_pc,
        c.registers.len() == m.num_regs,
        reg < m.num_regs,
        c.registers[reg as int] >= count,
    ensures
        run(m, c, count).pc == start_pc + count,
        run(m, c, count).registers.len() == c.registers.len(),
        run(m, c, count).registers[reg as int] == c.registers[reg as int] - count,
        forall|r: int| 0 <= r < m.num_regs as int && r != reg as int
            ==> run(m, c, count).registers[r] == c.registers[r],
    decreases count,
{
    if count == 0 {
        assert(run(m, c, 0) == c);
    } else {
        assert(m.instructions[start_pc as int] == mk_dj(reg, target));   // trigger at i = start_pc
        assert(c.registers[reg as int] >= count);
        assert(c.registers[reg as int] > 0);
        assert(!is_halted(m, c));
        lemma_run_unfold_step(m, c, count);
        let c1 = step(m, c).unwrap();   // DecJump(reg) pos-branch: reg--, pc = start_pc+1.
        assert(c1.pc == start_pc + 1);
        assert(c1.registers == c.registers.update(reg as int, (c.registers[reg as int] - 1) as nat));
        assert(c1.registers[reg as int] == (c.registers[reg as int] - 1) as nat);
        assert(c1.registers[reg as int] >= count - 1);
        assert(c1.registers.len() == m.num_regs);
        lemma_dec_block(m, c1, reg, target, (count - 1) as nat, start_pc + 1);
        assert(run(m, c, count) == run(m, c1, (count - 1) as nat));
        assert(run(m, c, count).registers[reg as int] == c.registers[reg as int] - count);
        assert forall|r: int| 0 <= r < m.num_regs as int && r != reg as int
        implies run(m, c, count).registers[r] == c.registers[r]
        by {
            assert(c1.registers[r] == c.registers[r]);
        }
    }
}

//  ============================================================
//  M2 — the destructive divide back-loop: `dst += src/k`, `src := 0` (requires `src = k·groups`).
//  ============================================================

/// **Divide back-loop gadget**: `[DecJump(src, start_pc+k+2)×k, Inc(dst), Jump(start_pc)]`
/// (`k + 2` instructions). Consumes `src` in groups of `k`, adding `1` to `dst` per group. Invoked
/// ONLY on the divisible branch, so the precondition is `src` a multiple of `k`.
pub open spec fn div_back_instrs(src: nat, dst: nat, k: nat, start_pc: nat) -> Seq<Instruction> {
    Seq::new(k + 2, |i: int|
        if i < k { mk_dj(src, start_pc + k + 2) }
        else if i == k { mk_inc(dst) }
        else { mk_jump(start_pc) }
    )
}

/// **The divide back-loop.** From `c` at `start_pc` with `src = k·groups`, `dst = acc`, running
/// `(k+2)·groups + 1` steps drains `src → 0` while `dst := acc + groups`, all other registers
/// unchanged, landing at `start_pc + k + 2`. Per iteration: `k` DecJumps (`lemma_dec_block`) +
/// `Inc(dst)` + `Jump`.
#[verifier::rlimit(4000)]
pub proof fn lemma_div_back_loop(
    m: RegisterMachine, c: Configuration,
    src: nat, dst: nat, k: nat, start_pc: nat,
    acc: nat, groups: nat,
)
    requires
        k >= 1,
        start_pc + k + 2 <= m.instructions.len(),
        forall|i: int| start_pc <= i < start_pc + k ==> #[trigger] m.instructions[i] == mk_dj(src, start_pc + k + 2),
        m.instructions[(start_pc + k) as int] == mk_inc(dst),
        m.instructions[(start_pc + k + 1) as int] == mk_jump(start_pc),
        c.pc == start_pc,
        c.registers.len() == m.num_regs,
        c.registers[src as int] == k * groups,
        c.registers[dst as int] == acc,
        src < m.num_regs, dst < m.num_regs, src != dst,
    ensures
        run(m, c, (k + 2) * groups + 1).pc == start_pc + k + 2,
        run(m, c, (k + 2) * groups + 1).registers[dst as int] == acc + groups,
        run(m, c, (k + 2) * groups + 1).registers[src as int] == 0,
        forall|r: int| 0 <= r < m.num_regs as int && r != src as int && r != dst as int
            ==> run(m, c, (k + 2) * groups + 1).registers[r] == c.registers[r],
    decreases groups,
{
    let fuel = (k + 2) * groups + 1;
    if groups == 0 {
        assert(k * groups == 0) by(nonlinear_arith) requires groups == 0;
        assert(c.registers[src as int] == 0);
        assert(fuel == 1) by(nonlinear_arith) requires fuel == (k + 2) * groups + 1, groups == 0;
        assert(m.instructions[start_pc as int] == mk_dj(src, start_pc + k + 2));   // trigger i=start_pc (k>=1)
        assert(!is_halted(m, c));
        lemma_run_unfold_step(m, c, fuel);
        let c1 = step(m, c).unwrap();   // DecJump(src) zero-branch: pc = start_pc+k+2, regs unchanged.
        assert(c1.pc == start_pc + k + 2);
        assert(c1.registers == c.registers);
        assert((fuel - 1) as nat == 0) by(nonlinear_arith) requires fuel == 1;
        assert(run(m, c, fuel) == c1);
        assert(run(m, c, fuel).registers =~= c.registers);
    } else {
        let g1: nat = (groups - 1) as nat;
        assert(k * groups >= k) by(nonlinear_arith) requires groups >= 1, k >= 1;
        //  --- dec_block of k DecJumps: src -= k → k·g1, pc = start_pc+k ---
        lemma_dec_block(m, c, src, start_pc + k + 2, k, start_pc);
        let c_dec = run(m, c, k);
        assert(c_dec.pc == start_pc + k);
        assert(c_dec.registers[src as int] == c.registers[src as int] - k);
        assert(k * groups - k == k * g1) by(nonlinear_arith) requires groups == g1 + 1;
        assert(c_dec.registers[src as int] == k * g1);
        assert(c_dec.registers[dst as int] == acc) by { assert(dst != src); };
        assert(c_dec.registers.len() == m.num_regs);
        //  split the fuel: run(m,c,fuel) == run(m, c_dec, fuel-k).
        assert(fuel >= k) by(nonlinear_arith) requires fuel == (k + 2) * groups + 1, groups >= 1, k >= 1;
        assert(fuel == k + (fuel - k));
        lemma_run_add(m, c, k, (fuel - k) as nat);
        assert(run(m, c, fuel) == run(m, c_dec, (fuel - k) as nat));
        //  --- Inc(dst): dst → acc+1, pc = start_pc+k+1 ---
        assert(m.instructions[c_dec.pc as int] == mk_inc(dst));
        assert(!is_halted(m, c_dec));
        assert((fuel - k) as nat >= 1) by(nonlinear_arith)
            requires fuel == (k + 2) * groups + 1, groups >= 1, k >= 1;
        lemma_run_unfold_step(m, c_dec, (fuel - k) as nat);
        let c_inc = step(m, c_dec).unwrap();
        assert(c_inc.pc == start_pc + k + 1);
        assert(c_inc.registers[dst as int] == acc + 1);
        assert(c_inc.registers[src as int] == k * g1) by { assert(src != dst); };
        assert(c_inc.registers.len() == m.num_regs);
        //  --- Jump(start_pc): pc → start_pc, regs unchanged ---
        assert(m.instructions[c_inc.pc as int] == mk_jump(start_pc));
        assert(!is_halted(m, c_inc));
        assert((fuel - k - 1) as nat >= 1) by(nonlinear_arith)
            requires fuel == (k + 2) * groups + 1, groups >= 1, k >= 1;
        lemma_run_unfold_step(m, c_inc, (fuel - k - 1) as nat);
        let c_jmp = step(m, c_inc).unwrap();
        assert(c_jmp.pc == start_pc);
        assert(c_jmp.registers == c_inc.registers);
        //  fuel bookkeeping: fuel - k - 2 == (k+2)·g1 + 1.
        assert((fuel - k - 2) as nat == (k + 2) * g1 + 1) by(nonlinear_arith)
            requires fuel == (k + 2) * groups + 1, groups == g1 + 1;
        assert(run(m, c, fuel) == run(m, c_jmp, (k + 2) * g1 + 1));
        lemma_div_back_loop(m, c_jmp, src, dst, k, start_pc, acc + 1, g1);
        assert((acc + 1) + g1 == acc + groups) by(nonlinear_arith) requires groups == g1 + 1;
        //  register preservation through the iteration.
        assert forall|r: int| 0 <= r < m.num_regs as int && r != src as int && r != dst as int
        implies run(m, c, fuel).registers[r] == c.registers[r]
        by {
            assert(c_dec.registers[r] == c.registers[r]);     // dec_block: r != src
            assert(c_inc.registers[r] == c_dec.registers[r]); // inc: r != dst
            assert(c_jmp.registers[r] == c_inc.registers[r]); // jump: unchanged
        };
    }
}

//  ============================================================
//  M2 — the pair block `[DecJump(src, notdiv); Inc(dst)]×p`: the inner walk of the div-test.
//  ============================================================

/// **The pair-block walk.** From `c` at `start_pos`, a straight-line block of `p` pairs
/// `[DecJump(src, notdiv_pc); Inc(dst)]`, walking `src` down while rebuilding it into `dst`:
///  - if `src = v ≥ p`: all `p` pairs fall through ⇒ reaches `start_pos + 2p` with `src = v − p`,
///    `dst = acc + p`;
///  - if `v < p`: the `(v+1)`-th DecJump hits zero ⇒ exits to `notdiv_pc` with `src = 0`,
///    `dst = acc + v`.
/// All other registers unchanged. (Existential fuel — the exit point depends on `v` vs `p`.)
proof fn lemma_pair_block(
    m: RegisterMachine, c: Configuration,
    src: nat, dst: nat, notdiv_pc: nat, start_pos: nat,
    p: nat, acc: nat, v: nat,
)
    requires
        start_pos + 2 * p <= m.instructions.len(),
        forall|j: int| 0 <= j < p ==> #[trigger] m.instructions[start_pos + 2 * j] == mk_dj(src, notdiv_pc),
        forall|j: int| 0 <= j < p ==> #[trigger] m.instructions[start_pos + 2 * j + 1] == mk_inc(dst),
        c.pc == start_pos,
        c.registers.len() == m.num_regs,
        c.registers[src as int] == v,
        c.registers[dst as int] == acc,
        src < m.num_regs, dst < m.num_regs, src != dst,
    ensures
        exists|g: nat|
            run(m, c, g).pc == (if v >= p { start_pos + 2 * p } else { notdiv_pc })
            && run(m, c, g).registers[src as int] == (if v >= p { (v - p) as nat } else { 0nat })
            && run(m, c, g).registers[dst as int] == (if v >= p { acc + p } else { acc + v })
            && run(m, c, g).registers.len() == m.num_regs
            && (forall|r: int| 0 <= r < m.num_regs as int && r != src as int && r != dst as int
                    ==> #[trigger] run(m, c, g).registers[r] == c.registers[r]),
    decreases p,
{
    if p == 0 {
        assert(v >= p);
        assert(start_pos + 2 * p == start_pos);
        assert(run(m, c, 0) == c);
        let g: nat = 0;
        assert(run(m, c, g).pc == (if v >= p { start_pos + 2 * p } else { notdiv_pc }));
        assert(run(m, c, g).registers[src as int] == (if v >= p { (v - p) as nat } else { 0nat }));
        assert(run(m, c, g).registers[dst as int] == (if v >= p { acc + p } else { acc + v }));
    } else {
        //  head DecJump(src, notdiv_pc) at start_pos (j = 0 of the first forall).
        assert(m.instructions[start_pos as int] == mk_dj(src, notdiv_pc)) by {
            assert(start_pos + 2 * 0 == start_pos);
        };
        assert(!is_halted(m, c));
        if v == 0 {
            //  v < p (p >= 1). DecJump(src=0) → notdiv_pc. g = 1.
            lemma_run_unfold_step(m, c, 1);
            let c1 = step(m, c).unwrap();
            assert(c1.pc == notdiv_pc);
            assert(c1.registers == c.registers);
            assert(run(m, c, 1) == c1);
            let g: nat = 1;
            assert(!(v >= p));
            assert(run(m, c, g).registers[dst as int] == acc + v);   // v == 0 ⇒ acc + 0
        } else {
            //  v > 0. head: src → v-1, pc = start_pos+1; then Inc(dst): dst → acc+1, pc = start_pos+2.
            lemma_run_unfold_step(m, c, 2);
            let c1 = step(m, c).unwrap();
            assert(c1.pc == start_pos + 1);
            assert(c1.registers[src as int] == (v - 1) as nat);
            assert(c1.registers[dst as int] == acc) by { assert(src != dst); };
            //  Inc(dst) at start_pos+1 (j = 0 of the second forall).
            assert(m.instructions[(start_pos + 1) as int] == mk_inc(dst)) by {
                assert(start_pos + 2 * 0 + 1 == start_pos + 1);
            };
            assert(!is_halted(m, c1));
            lemma_run_unfold_step(m, c1, 1);
            let c2 = step(m, c1).unwrap();
            assert(c2.pc == start_pos + 2);
            assert(c2.registers[dst as int] == acc + 1);
            assert(c2.registers[src as int] == (v - 1) as nat) by { assert(src != dst); };
            assert(c2.registers.len() == m.num_regs);
            assert(run(m, c, 2) == c2);
            //  layout for the recursive block at start_pos+2 with p-1 pairs.
            assert forall|j: int| 0 <= j < p - 1 implies
                #[trigger] m.instructions[(start_pos + 2) + 2 * j] == mk_dj(src, notdiv_pc)
            by {
                assert((start_pos + 2) + 2 * j == start_pos + 2 * (j + 1)) by(nonlinear_arith);
                assert(m.instructions[start_pos + 2 * (j + 1)] == mk_dj(src, notdiv_pc));
            };
            assert forall|j: int| 0 <= j < p - 1 implies
                #[trigger] m.instructions[(start_pos + 2) + 2 * j + 1] == mk_inc(dst)
            by {
                assert((start_pos + 2) + 2 * j + 1 == start_pos + 2 * (j + 1) + 1) by(nonlinear_arith);
                assert(m.instructions[start_pos + 2 * (j + 1) + 1] == mk_inc(dst));
            };
            assert((start_pos + 2) + 2 * (p - 1) <= m.instructions.len()) by(nonlinear_arith)
                requires start_pos + 2 * p <= m.instructions.len(), p >= 1;
            lemma_pair_block(m, c2, src, dst, notdiv_pc, start_pos + 2, (p - 1) as nat, acc + 1, (v - 1) as nat);
            let p1: nat = (p - 1) as nat;
            let vv: nat = (v - 1) as nat;
            let g_inner = choose|g: nat|
                run(m, c2, g).pc == (if vv >= p1 { (start_pos + 2) + 2 * p1 } else { notdiv_pc })
                && run(m, c2, g).registers[src as int] == (if vv >= p1 { (vv - p1) as nat } else { 0nat })
                && run(m, c2, g).registers[dst as int] == (if vv >= p1 { (acc + 1) + p1 } else { (acc + 1) + vv })
                && run(m, c2, g).registers.len() == m.num_regs
                && (forall|r: int| 0 <= r < m.num_regs as int && r != src as int && r != dst as int
                        ==> #[trigger] run(m, c2, g).registers[r] == c2.registers[r]);
            //  chain: run(m, c, 2 + g_inner) == run(m, c2, g_inner).
            lemma_run_add(m, c, 2, g_inner);
            let g: nat = (2 + g_inner) as nat;
            assert(run(m, c, g) == run(m, c2, g_inner));
            //  relate (vv >= p1) to (v >= p), and the result values.
            assert(vv >= p1 <==> v >= p);
            if v >= p {
                assert((start_pos + 2) + 2 * p1 == start_pos + 2 * p) by(nonlinear_arith) requires p == p1 + 1;
                assert((vv - p1) as nat == (v - p) as nat);
                assert((acc + 1) + p1 == acc + p);
            } else {
                assert((acc + 1) + vv == acc + v);
            }
            //  frame: out-of-{src,dst} regs preserved through c → c2 → final.
            assert forall|r: int| 0 <= r < m.num_regs as int && r != src as int && r != dst as int
            implies #[trigger] run(m, c, g).registers[r] == c.registers[r]
            by {
                assert(run(m, c2, g_inner).registers[r] == c2.registers[r]);
                assert(c2.registers[r] == c.registers[r]) by {
                    assert(c1.registers[r] == c.registers[r]);   // head DecJump: r != src
                    assert(c2.registers[r] == c1.registers[r]);  // Inc: r != dst
                };
            };
        }
    }
}

//  ============================================================
//  M2 — the non-destructive divisibility-test back-loop `Div?((src),k)[e1]`.
//  ============================================================

/// **Div-test back-loop gadget** (after `move (n)→(n+1)`, so `src` = `n+1`, `dst` = `n`):
/// ```text
///   index 0:        DecJump(src, e1_pc)        // group head: zero ⇒ DIVISIBLE
///   index 1:        Inc(dst)
///   index 2j,2j+1:  DecJump(src, notdiv_pc), Inc(dst)   // pairs j = 1..k-1
///   index 2k:       Jump(start_pc)
/// ```
/// `2k + 1` instructions. The head's zero-test exits `e1_pc` (a clean group boundary ⇒ divisible);
/// a mid-group zero exits `notdiv_pc`.
pub open spec fn divtest_back_instrs(
    src: nat, dst: nat, k: nat, start_pc: nat, e1_pc: nat, notdiv_pc: nat,
) -> Seq<Instruction> {
    Seq::new(2 * k + 1, |i: int|
        if i == 0 { mk_dj(src, e1_pc) }
        else if i == 2 * k { mk_jump(start_pc) }
        else if i % 2 == 1 { mk_inc(dst) }
        else { mk_dj(src, notdiv_pc) }
    )
}

/// **The div-test back-loop.** From `c` at `start_pc` with `src = remaining`, `dst = acc`, the gadget
/// runs (existential fuel) to either `e1_pc` (iff `remaining % k == 0` — divisible) or `notdiv_pc`,
/// restoring `dst := acc + remaining` and `src := 0` on **both** exits (non-destructive — the verdict
/// is carried purely in the exit pc). All other registers unchanged.
#[verifier::rlimit(8000)]
pub proof fn lemma_divtest_back_loop(
    m: RegisterMachine, c: Configuration,
    src: nat, dst: nat, k: nat, start_pc: nat, e1_pc: nat, notdiv_pc: nat,
    acc: nat, remaining: nat,
)
    requires
        k >= 1,
        start_pc + 2 * k + 1 <= m.instructions.len(),
        m.instructions[start_pc as int] == mk_dj(src, e1_pc),
        m.instructions[(start_pc + 2 * k) as int] == mk_jump(start_pc),
        forall|j: int| 0 <= j < k ==> #[trigger] m.instructions[start_pc + 2 * j + 1] == mk_inc(dst),
        forall|j: int| 1 <= j < k ==> #[trigger] m.instructions[start_pc + 2 * j] == mk_dj(src, notdiv_pc),
        c.pc == start_pc,
        c.registers.len() == m.num_regs,
        c.registers[src as int] == remaining,
        c.registers[dst as int] == acc,
        src < m.num_regs, dst < m.num_regs, src != dst,
    ensures
        exists|g: nat|
            run(m, c, g).pc == (if remaining % k == 0 { e1_pc } else { notdiv_pc })
            && run(m, c, g).registers[src as int] == 0
            && run(m, c, g).registers[dst as int] == acc + remaining
            && run(m, c, g).registers.len() == m.num_regs
            && (forall|r: int| 0 <= r < m.num_regs as int && r != src as int && r != dst as int
                    ==> #[trigger] run(m, c, g).registers[r] == c.registers[r]),
    decreases remaining,
{
    if remaining == 0 {
        //  0 % k == 0 ⇒ e1_pc. head DecJump(src=0) → e1_pc. g = 1.
        assert(remaining % k == 0) by(nonlinear_arith) requires remaining == 0, k >= 1;
        assert(!is_halted(m, c));
        lemma_run_unfold_step(m, c, 1);
        let c1 = step(m, c).unwrap();
        assert(c1.pc == e1_pc);
        assert(c1.registers == c.registers);
        assert(run(m, c, 1) == c1);
        let g: nat = 1;
        assert(run(m, c, g).registers[dst as int] == acc + remaining);
    } else {
        //  remaining >= 1. head DecJump(src>0): src → remaining-1, pc = start_pc+1.
        assert(!is_halted(m, c));
        lemma_run_unfold_step(m, c, 2);
        let c1 = step(m, c).unwrap();
        assert(c1.pc == start_pc + 1);
        assert(c1.registers[src as int] == (remaining - 1) as nat);
        assert(c1.registers[dst as int] == acc) by { assert(src != dst); };
        //  Inc(dst) at start_pc+1 (j = 0 of the Inc forall: start_pc + 2*0 + 1).
        assert(m.instructions[(start_pc + 1) as int] == mk_inc(dst)) by {
            assert(start_pc + 2 * 0 + 1 == start_pc + 1);
        };
        assert(!is_halted(m, c1));
        lemma_run_unfold_step(m, c1, 1);
        let c2 = step(m, c1).unwrap();
        assert(c2.pc == start_pc + 2);
        assert(c2.registers[dst as int] == acc + 1);
        assert(c2.registers[src as int] == (remaining - 1) as nat) by { assert(src != dst); };
        assert(c2.registers.len() == m.num_regs);
        assert(run(m, c, 2) == c2);
        //  feed the pair block: start_pos = start_pc+2, p = k-1, v = remaining-1, acc' = acc+1.
        let p: nat = (k - 1) as nat;
        let vv: nat = (remaining - 1) as nat;
        assert forall|j: int| 0 <= j < p implies
            #[trigger] m.instructions[(start_pc + 2) + 2 * j] == mk_dj(src, notdiv_pc)
        by {
            assert((start_pc + 2) + 2 * j == start_pc + 2 * (j + 1)) by(nonlinear_arith);
            assert(1 <= j + 1 < k);
            assert(m.instructions[start_pc + 2 * (j + 1)] == mk_dj(src, notdiv_pc));
        };
        assert forall|j: int| 0 <= j < p implies
            #[trigger] m.instructions[(start_pc + 2) + 2 * j + 1] == mk_inc(dst)
        by {
            assert((start_pc + 2) + 2 * j + 1 == start_pc + 2 * (j + 1) + 1) by(nonlinear_arith);
            assert(0 <= j + 1 < k);
            assert(m.instructions[start_pc + 2 * (j + 1) + 1] == mk_inc(dst));
        };
        assert((start_pc + 2) + 2 * p <= m.instructions.len()) by(nonlinear_arith)
            requires start_pc + 2 * k + 1 <= m.instructions.len(), p == k - 1, k >= 1;
        lemma_pair_block(m, c2, src, dst, notdiv_pc, start_pc + 2, p, acc + 1, vv);
        let g_pb = choose|g: nat|
            run(m, c2, g).pc == (if vv >= p { (start_pc + 2) + 2 * p } else { notdiv_pc })
            && run(m, c2, g).registers[src as int] == (if vv >= p { (vv - p) as nat } else { 0nat })
            && run(m, c2, g).registers[dst as int] == (if vv >= p { (acc + 1) + p } else { (acc + 1) + vv })
            && run(m, c2, g).registers.len() == m.num_regs
            && (forall|r: int| 0 <= r < m.num_regs as int && r != src as int && r != dst as int
                    ==> #[trigger] run(m, c2, g).registers[r] == c2.registers[r]);
        let cpb = run(m, c2, g_pb);
        if remaining >= k {
            //  CASE A: full group. vv = remaining-1 >= k-1 = p ⇒ pair block falls through to the Jump.
            assert(vv >= p);
            assert(cpb.pc == (start_pc + 2) + 2 * p);
            assert((start_pc + 2) + 2 * p == start_pc + 2 * k) by(nonlinear_arith) requires p == k - 1, k >= 1;
            assert(cpb.registers[src as int] == (vv - p) as nat);
            assert((vv - p) as nat == (remaining - k) as nat);
            assert(cpb.registers[dst as int] == (acc + 1) + p);
            assert((acc + 1) + p == acc + k) by(nonlinear_arith) requires p == k - 1, k >= 1;
            assert(cpb.registers.len() == m.num_regs);
            //  Jump(start_pc) at start_pc+2k.
            assert(m.instructions[cpb.pc as int] == mk_jump(start_pc));
            assert(!is_halted(m, cpb));
            lemma_run_unfold_step(m, cpb, 1);
            let c_jmp = step(m, cpb).unwrap();
            assert(c_jmp.pc == start_pc);
            assert(c_jmp.registers == cpb.registers);
            assert(c_jmp.registers[src as int] == (remaining - k) as nat);
            assert(c_jmp.registers[dst as int] == acc + k);
            assert(run(m, cpb, 1) == c_jmp);
            //  recurse on remaining - k.
            let rem_k: nat = (remaining - k) as nat;
            lemma_divtest_back_loop(m, c_jmp, src, dst, k, start_pc, e1_pc, notdiv_pc, acc + k, rem_k);
            let g_inner = choose|g: nat|
                run(m, c_jmp, g).pc == (if rem_k % k == 0 { e1_pc } else { notdiv_pc })
                && run(m, c_jmp, g).registers[src as int] == 0
                && run(m, c_jmp, g).registers[dst as int] == (acc + k) + rem_k
                && run(m, c_jmp, g).registers.len() == m.num_regs
                && (forall|r: int| 0 <= r < m.num_regs as int && r != src as int && r != dst as int
                        ==> #[trigger] run(m, c_jmp, g).registers[r] == c_jmp.registers[r]);
            //  residue preserved: (remaining-k) % k == remaining % k.
            lemma_mod_sub_k(remaining, k);
            assert(rem_k % k == remaining % k);
            assert((acc + k) + rem_k == acc + remaining);   // rem_k == remaining - k (linear)
            //  chain the run: run(m,c,2+g_pb+1+g_inner) == run(m, c_jmp, g_inner).
            lemma_run_add(m, cpb, 1, g_inner);
            lemma_run_add(m, c2, g_pb, (1 + g_inner) as nat);
            lemma_run_add(m, c, 2, (g_pb + 1 + g_inner) as nat);
            let g: nat = (2 + g_pb + 1 + g_inner) as nat;
            assert(run(m, c, g) == run(m, c_jmp, g_inner));
            //  frame: c → c2 → cpb → c_jmp → final, all preserve r ∉ {src,dst}.
            assert forall|r: int| 0 <= r < m.num_regs as int && r != src as int && r != dst as int
            implies #[trigger] run(m, c, g).registers[r] == c.registers[r]
            by {
                assert(run(m, c_jmp, g_inner).registers[r] == c_jmp.registers[r]);
                assert(c_jmp.registers[r] == cpb.registers[r]);
                assert(cpb.registers[r] == c2.registers[r]);
                assert(c2.registers[r] == c.registers[r]) by {
                    assert(c1.registers[r] == c.registers[r]);
                    assert(c2.registers[r] == c1.registers[r]);
                };
            };
        } else {
            //  CASE B: partial group. 1 <= remaining < k ⇒ vv = remaining-1 < k-1 = p ⇒ exit notdiv.
            assert(!(vv >= p));
            assert(remaining % k == remaining) by(nonlinear_arith) requires 1 <= remaining < k;
            assert(remaining % k != 0);
            assert(cpb.pc == notdiv_pc);
            assert(cpb.registers[src as int] == 0);
            assert(cpb.registers[dst as int] == (acc + 1) + vv);
            assert((acc + 1) + vv == acc + remaining);   // vv == remaining - 1 (linear)
            assert(cpb.registers.len() == m.num_regs);
            lemma_run_add(m, c, 2, g_pb);
            let g: nat = (2 + g_pb) as nat;
            assert(run(m, c, g) == cpb);
            assert forall|r: int| 0 <= r < m.num_regs as int && r != src as int && r != dst as int
            implies #[trigger] run(m, c, g).registers[r] == c.registers[r]
            by {
                assert(cpb.registers[r] == c2.registers[r]);
                assert(c2.registers[r] == c.registers[r]) by {
                    assert(c1.registers[r] == c.registers[r]);
                    assert(c2.registers[r] == c1.registers[r]);
                };
            };
        }
    }
}

} //  verus!
