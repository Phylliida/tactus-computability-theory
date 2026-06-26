//! # GAP-2-E brick B5.3 — the `rm_to_tm` assembly + well-formedness
//!
//! Assembles the per-instruction gadget blocks (peek / inc / dec / bounce) into one deterministic
//! `Tm` simulating a 2-counter register machine `R2` (num_regs = 2, register 0 = left counter `c1`
//! in `u`, register 1 = right counter `c2` in `v`). The state layout is **uniform**: every program
//! position `pc ∈ [0, len]` owns a 16-state window `[entry(pc), entry(pc)+16)` with
//! `entry(pc) = 3 + 16·pc`, and contributes exactly `48 = 16·3` quintuples — one per
//! `(state-offset, scanned-symbol)` pair in `[0,16)×{0,1,2}`. Real gadget transitions occupy the
//! `(off,sym)` slots they use; the rest are inert dummies keyed at their own `(off,sym)` (never
//! matched on any reachable trajectory). The `len`-th window is the **cleanup** block (B6 proves it
//! drives the tape to `tm_origin()`); positions `pc<len` hold the instruction gadgets.
//!
//! Because q-key = `entry(pc)+off` and scanned = `sym` are *manifest* in `block_quint` (independent of
//! the action table), the well-formedness proof splits cleanly:
//!   * `quint_wf` per quintuple: scanned `= sym ≤ 2`, state `= entry(pc)+off ∈ [3, m)`, and the
//!     written symbol / next state are bounded by `lemma_act_bounds`;
//!   * **determinism**: from `gen(i).(q,a) == gen(j).(q,a)` the flat index is recovered by pure
//!     division/modulo arithmetic (`i = (i/48)·48 + (i%48)`, the window stride 16 > 15 ≥ max offset),
//!     so `i == j`. No reasoning about the gadget contents is needed.
//!
//! Per-step simulation correctness (the gadgets actually fire) is brick B5.4; cleanup-reaches-origin
//! and the run induction are B6. Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse};
use verus_group_theory::machine_group::Dir;
use crate::machine::{RegisterMachine, Instruction, machine_wf};
use crate::tm::{Tm, Quintuple, tm_wf, quint_wf};
use crate::tm_gadget::mk_quint;

verus! {

// ─────────────────────────────────────────────────────────────────────────────
// Layout constants.  n = 2 (alphabet 0,1,2).  STRIDE = 16 states per window.
// QPB = 16·3 = 48 quintuples per window.  entry(pc) = 3 + 16·pc.
// ─────────────────────────────────────────────────────────────────────────────

/// First state of program position `pc`'s window (states are `≥ n+1 = 3`).
pub open spec fn entry(pc: nat) -> nat { 3 + 16 * pc }

/// The TM modulus: one window past the cleanup block, so every used state is `< m`.
/// `tm_mod(len) = entry(len) + 16 = 19 + 16·len`.
pub open spec fn tm_mod(len: nat) -> nat { 19 + 16 * len }

// ─────────────────────────────────────────────────────────────────────────────
// Per-instruction action tables.  Each returns `(a2, q2, dir)` for the quintuple at
// `(state = entry(pc)+off, scanned = sym)`.  Slots not used by the gadget return an inert
// dummy `(sym, entry(pc), L)` (writes the scanned symbol back; never fires on-trajectory).
// ─────────────────────────────────────────────────────────────────────────────

/// inc-left gadget + left bounce (register 0).  States: s0=entry (walk), s1 (back/bounce-entry),
/// s2 (bounce-mid).  Exit → `entry(pc)+16 = entry(pc+1)`.
pub open spec fn inc_left_act(pc: nat, off: nat, sym: nat) -> (nat, nat, Dir) {
    let e = entry(pc);
    let nx = e + 16;
    if off == 0 {
        if sym == 2 { (2, e, Dir::L) }          // (s0,2,2,s0,L) sep-peel
        else if sym == 1 { (1, e, Dir::L) }     // (s0,1,1,s0,L) walk-left
        else { (1, e + 1, Dir::R) }             // (s0,0,1,s1,R) turnaround
    } else if off == 1 {
        if sym == 1 { (1, e + 1, Dir::R) }      // (s1,1,1,s1,R) walk-back
        else if sym == 2 { (2, e + 2, Dir::L) } // (s1,2,2,s2,L) bounce-peel
        else { (sym, e, Dir::L) }
    } else if off == 2 {
        if sym == 1 { (1, nx, Dir::R) }         // (s2,1,1,next,R) bounce-back
        else if sym == 0 { (0, nx, Dir::R) }    // (s2,0,0,next,R)
        else { (sym, e, Dir::L) }
    } else { (sym, e, Dir::L) }
}

/// inc-right gadget + right bounce (register 1).  Mirror of `inc_left_act` (L↔R).
pub open spec fn inc_right_act(pc: nat, off: nat, sym: nat) -> (nat, nat, Dir) {
    let e = entry(pc);
    let nx = e + 16;
    if off == 0 {
        if sym == 2 { (2, e, Dir::R) }
        else if sym == 1 { (1, e, Dir::R) }
        else { (1, e + 1, Dir::L) }
    } else if off == 1 {
        if sym == 1 { (1, e + 1, Dir::L) }
        else if sym == 2 { (2, e + 2, Dir::R) }
        else { (sym, e, Dir::L) }
    } else if off == 2 {
        if sym == 1 { (1, nx, Dir::L) }
        else if sym == 0 { (0, nx, Dir::L) }
        else { (sym, e, Dir::L) }
    } else { (sym, e, Dir::L) }
}

/// DecJump-left gadget (register 0, jump `target=t`).  peek (s0,s1) + dec (s2,s3,s4) + bounce (s5).
/// pos-branch → s2 (dec), zero-branch → `entry(t)` (jump), dec exit → bounce → `entry(pc+1)`.
pub open spec fn decjump_left_act(pc: nat, t: nat, off: nat, sym: nat) -> (nat, nat, Dir) {
    let e = entry(pc);
    let nx = e + 16;
    let tgt = entry(t);
    if off == 0 {
        if sym == 2 { (2, e + 1, Dir::L) }      // (s0,2,2,s1,L) peek entry
        else { (sym, e, Dir::L) }
    } else if off == 1 {
        if sym == 1 { (1, e + 2, Dir::R) }      // (s1,1,1,s2,R) peek pos → s2
        else if sym == 0 { (0, tgt, Dir::R) }   // (s1,0,0,tgt,R) peek zero → jump
        else { (sym, e, Dir::L) }
    } else if off == 2 {
        if sym == 2 { (2, e + 2, Dir::L) }      // (s2,2,2,s2,L) dec sep-peel
        else if sym == 1 { (1, e + 2, Dir::L) } // (s2,1,1,s2,L) dec walk-left
        else { (0, e + 3, Dir::R) }             // (s2,0,0,s3,R) dec erase-turnaround
    } else if off == 3 {
        if sym == 1 { (0, e + 4, Dir::R) }      // (s3,1,0,s4,R) dec discard
        else { (sym, e, Dir::L) }
    } else if off == 4 {
        if sym == 1 { (1, e + 4, Dir::R) }      // (s4,1,1,s4,R) dec walk-back
        else if sym == 2 { (2, e + 5, Dir::L) } // (s4,2,2,s5,L) bounce-peel
        else { (sym, e, Dir::L) }
    } else if off == 5 {
        if sym == 1 { (1, nx, Dir::R) }         // (s5,1,1,next,R) bounce-back
        else if sym == 0 { (0, nx, Dir::R) }    // (s5,0,0,next,R)
        else { (sym, e, Dir::L) }
    } else { (sym, e, Dir::L) }
}

/// DecJump-right gadget (register 1).  Mirror of `decjump_left_act` (L↔R).
pub open spec fn decjump_right_act(pc: nat, t: nat, off: nat, sym: nat) -> (nat, nat, Dir) {
    let e = entry(pc);
    let nx = e + 16;
    let tgt = entry(t);
    if off == 0 {
        if sym == 2 { (2, e + 1, Dir::R) }
        else { (sym, e, Dir::L) }
    } else if off == 1 {
        if sym == 1 { (1, e + 2, Dir::L) }
        else if sym == 0 { (0, tgt, Dir::L) }
        else { (sym, e, Dir::L) }
    } else if off == 2 {
        if sym == 2 { (2, e + 2, Dir::R) }
        else if sym == 1 { (1, e + 2, Dir::R) }
        else { (0, e + 3, Dir::L) }
    } else if off == 3 {
        if sym == 1 { (0, e + 4, Dir::L) }
        else { (sym, e, Dir::L) }
    } else if off == 4 {
        if sym == 1 { (1, e + 4, Dir::L) }
        else if sym == 2 { (2, e + 5, Dir::R) }
        else { (sym, e, Dir::L) }
    } else if off == 5 {
        if sym == 1 { (1, nx, Dir::L) }
        else if sym == 0 { (0, nx, Dir::L) }
        else { (sym, e, Dir::L) }
    } else { (sym, e, Dir::L) }
}

/// Halt instruction: a left bounce routing `entry(pc) → entry(len)` (the cleanup entry).
pub open spec fn halt_act(pc: nat, len: nat, off: nat, sym: nat) -> (nat, nat, Dir) {
    let e = entry(pc);
    let clean = entry(len);
    if off == 0 {
        if sym == 2 { (2, e + 1, Dir::L) }      // (s0,2,2,s1,L)
        else { (sym, e, Dir::L) }
    } else if off == 1 {
        if sym == 1 { (1, clean, Dir::R) }      // (s1,1,1,clean,R)
        else if sym == 0 { (0, clean, Dir::R) } // (s1,0,0,clean,R)
        else { (sym, e, Dir::L) }
    } else { (sym, e, Dir::L) }
}

/// Jump instruction: an unconditional left bounce routing `entry(pc) → entry(target)`.
/// Bit-for-bit `halt_act` with the cleanup entry `entry(len)` replaced by the jump's own
/// (relocated) destination `entry(target)` — the counters/tape are left untouched.
pub open spec fn jump_act(pc: nat, target: nat, off: nat, sym: nat) -> (nat, nat, Dir) {
    let e = entry(pc);
    let dst = entry(target);
    if off == 0 {
        if sym == 2 { (2, e + 1, Dir::L) }      // (s0,2,2,s1,L)
        else { (sym, e, Dir::L) }
    } else if off == 1 {
        if sym == 1 { (1, dst, Dir::R) }        // (s1,1,1,dst,R)
        else if sym == 0 { (0, dst, Dir::R) }   // (s1,0,0,dst,R)
        else { (sym, e, Dir::L) }
    } else { (sym, e, Dir::L) }
}

/// The cleanup block (window `pc == len`): dec `c1` to 0 (phase A, off 0–5), dec `c2` to 0
/// (phase B, off 6–11), then blank the separator into `tm_origin()` (phase C, off 12).
pub open spec fn cleanup_act(len: nat, off: nat, sym: nat) -> (nat, nat, Dir) {
    let e = entry(len);
    if off == 0 {
        if sym == 2 { (2, e + 1, Dir::L) }       // CA peek-left entry → CAb
        else { (sym, e, Dir::L) }
    } else if off == 1 {
        if sym == 1 { (1, e + 2, Dir::R) }       // CAb pos → CApos
        else if sym == 0 { (0, e + 6, Dir::R) }  // CAb zero → CB (phase B)
        else { (sym, e, Dir::L) }
    } else if off == 2 {
        if sym == 2 { (2, e + 2, Dir::L) }       // CApos dec-left sep-peel
        else if sym == 1 { (1, e + 2, Dir::L) }  // CApos walk-left
        else { (0, e + 3, Dir::R) }              // CApos erase-turn → CAd
    } else if off == 3 {
        if sym == 1 { (0, e + 4, Dir::R) }       // CAd discard → CAbk
        else { (sym, e, Dir::L) }
    } else if off == 4 {
        if sym == 1 { (1, e + 4, Dir::R) }       // CAbk walk-back
        else if sym == 2 { (2, e + 5, Dir::L) }  // CAbk bounce-peel → CAbm
        else { (sym, e, Dir::L) }
    } else if off == 5 {
        if sym == 1 { (1, e, Dir::R) }           // CAbm bounce-back → CA (loop)
        else if sym == 0 { (0, e, Dir::R) }      // CAbm bounce-back → CA
        else { (sym, e, Dir::L) }
    } else if off == 6 {
        if sym == 2 { (2, e + 7, Dir::R) }       // CB peek-right entry → CBb
        else { (sym, e, Dir::L) }
    } else if off == 7 {
        if sym == 1 { (1, e + 8, Dir::L) }       // CBb pos → CBpos
        else if sym == 0 { (0, e + 12, Dir::L) } // CBb zero → CC (phase C)
        else { (sym, e, Dir::L) }
    } else if off == 8 {
        if sym == 2 { (2, e + 8, Dir::R) }       // CBpos dec-right sep-peel
        else if sym == 1 { (1, e + 8, Dir::R) }  // CBpos walk-right
        else { (0, e + 9, Dir::L) }              // CBpos erase-turn → CBd
    } else if off == 9 {
        if sym == 1 { (0, e + 10, Dir::L) }      // CBd discard → CBbk
        else { (sym, e, Dir::L) }
    } else if off == 10 {
        if sym == 1 { (1, e + 10, Dir::L) }      // CBbk walk-back-left
        else if sym == 2 { (2, e + 11, Dir::R) } // CBbk bounce-right peel → CBbm
        else { (sym, e, Dir::L) }
    } else if off == 11 {
        if sym == 1 { (1, e + 6, Dir::L) }       // CBbm bounce-back → CB (loop)
        else if sym == 0 { (0, e + 6, Dir::L) }  // CBbm bounce-back → CB
        else { (sym, e, Dir::L) }
    } else if off == 12 {
        if sym == 2 { (0, 0, Dir::R) }           // CC: (CC,2,0,0,R) → tm_origin()!
        else { (sym, e, Dir::L) }
    } else { (sym, e, Dir::L) }
}

/// The action for program position `pc` (`pc < len` = an instruction, `pc == len` = cleanup).
pub open spec fn pos_act(rm: RegisterMachine, pc: nat, off: nat, sym: nat) -> (nat, nat, Dir) {
    let len = rm.instructions.len();
    if pc < len {
        match rm.instructions[pc as int] {
            Instruction::Inc { register } =>
                if register == 0 { inc_left_act(pc, off, sym) } else { inc_right_act(pc, off, sym) },
            Instruction::DecJump { register, target } =>
                if register == 0 { decjump_left_act(pc, target, off, sym) }
                else { decjump_right_act(pc, target, off, sym) },
            Instruction::Jump { target } => jump_act(pc, target, off, sym),
            Instruction::Halt => halt_act(pc, len, off, sym),
        }
    } else {
        cleanup_act(len, off, sym)
    }
}

/// The quintuple at flat index `idx`: window `pc = idx/48`, offset `off = (idx%48)/3`,
/// scanned `sym = (idx%48)%3`.  State `= entry(pc)+off` and scanned `= sym` are **manifest**.
pub open spec fn gen(rm: RegisterMachine, idx: nat) -> Quintuple {
    let pc = idx / 48;
    let off = (idx % 48) / 3;
    let sym = (idx % 48) % 3;
    let act = pos_act(rm, pc, off, sym);
    mk_quint(entry(pc) + off, sym, act.0, act.1, act.2)
}

/// **The register-machine → Turing-machine assembly.** `(len+1)` uniform 48-quintuple windows:
/// the instruction gadgets at `pc ∈ [0,len)` and the cleanup at `pc = len`.
pub open spec fn rm_to_tm(rm: RegisterMachine) -> Tm {
    let len = rm.instructions.len();
    Tm {
        n: 2,
        m: tm_mod(len),
        quints: Seq::new(48 * (len + 1), |idx: int| gen(rm, idx as nat)),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The q-key / scanned-symbol of `gen(idx)` is a pure function of `idx` (manifest, table-free).
// ─────────────────────────────────────────────────────────────────────────────

/// `gen(rm, idx)` has state `entry(idx/48) + (idx%48)/3` and scanned `(idx%48)%3` — independent of
/// the action table (both are manifest in `gen`'s `mk_quint`). The hook for the determinism proof.
pub proof fn lemma_gen_key(rm: RegisterMachine, idx: nat)
    ensures
        gen(rm, idx).q == entry(idx / 48) + (idx % 48) / 3,
        gen(rm, idx).a == (idx % 48) % 3,
{
    // immediate: gen = mk_quint(entry(pc)+off, sym, ..), pc=idx/48, off=(idx%48)/3, sym=(idx%48)%3.
}

// ─────────────────────────────────────────────────────────────────────────────
// Action bounds: written symbol `≤ 2`, next state `< m`.
// ─────────────────────────────────────────────────────────────────────────────

/// Every action's written symbol is `≤ 2` and next state is `< tm_mod(len)`, given `pc ≤ len` and
/// (for `DecJump`) the machine is well-formed (so every jump target is `≤ len`).
pub proof fn lemma_act_bounds(rm: RegisterMachine, pc: nat, off: nat, sym: nat)
    requires
        machine_wf(rm),
        pc <= rm.instructions.len(),
        sym <= 2,
    ensures
        pos_act(rm, pc, off, sym).0 <= 2,
        pos_act(rm, pc, off, sym).1 < tm_mod(rm.instructions.len()),
{
    reveal(machine_wf);
    let len = rm.instructions.len();
    let m = tm_mod(len);
    // entry(pc) + 16 = entry(pc+1) ≤ entry(len) < m for pc < len; entry(t) ≤ entry(len) < m for t ≤ len.
    assert(entry(pc) <= entry(len)) by(nonlinear_arith) requires pc <= len, entry(pc) == 3 + 16 * pc, entry(len) == 3 + 16 * len;
    if pc < len {
        match rm.instructions[pc as int] {
            Instruction::Inc { register } => {
                // a2 ∈ {0,1,2,sym}; q2 ∈ {entry(pc), entry(pc)+1, entry(pc)+2, entry(pc)+16}.
                assert(entry(pc) + 16 == entry((pc + 1) as nat));
                assert(entry((pc + 1) as nat) <= entry(len)) by(nonlinear_arith)
                    requires pc + 1 <= len, entry((pc + 1) as nat) == 3 + 16 * (pc + 1), entry(len) == 3 + 16 * len;
            },
            Instruction::DecJump { register, target } => {
                assert(target <= len);   // machine_wf
                assert(entry(target) <= entry(len)) by(nonlinear_arith)
                    requires target <= len, entry(target) == 3 + 16 * target, entry(len) == 3 + 16 * len;
                assert(entry(pc) + 16 == entry((pc + 1) as nat));
                assert(entry((pc + 1) as nat) <= entry(len)) by(nonlinear_arith)
                    requires pc + 1 <= len, entry((pc + 1) as nat) == 3 + 16 * (pc + 1), entry(len) == 3 + 16 * len;
            },
            Instruction::Jump { target } => {
                // q2 ∈ {entry(pc), entry(pc)+1, entry(target)}; target ≤ len (machine_wf).
                assert(target <= len);
                assert(entry(target) <= entry(len)) by(nonlinear_arith)
                    requires target <= len, entry(target) == 3 + 16 * target, entry(len) == 3 + 16 * len;
            },
            Instruction::Halt => {
                // q2 ∈ {entry(pc), entry(pc)+1, entry(len)}; all ≤ entry(len)+1 ≤ ... < m.
            },
        }
    } else {
        // cleanup: q2 ∈ {0} ∪ {entry(len)+k : k ≤ 12}; entry(len)+12 < entry(len)+16 = m.
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Well-formedness of the assembled TM (the determinism proof).
// ─────────────────────────────────────────────────────────────────────────────

/// **`rm_to_tm` is a well-formed (deterministic) TM.** quint_wf per quintuple via `lemma_act_bounds`
/// + the manifest state/scanned; determinism by recovering the flat index from `(q, a)` arithmetic.
pub proof fn lemma_rm_to_tm_wf(rm: RegisterMachine)
    requires
        machine_wf(rm),
    ensures
        tm_wf(rm_to_tm(rm)),
{
    reveal(tm_wf);
    let tm = rm_to_tm(rm);
    let len = rm.instructions.len();
    let m = tm_mod(len);
    let total = 48 * (len + 1);
    assert(tm.m == m && tm.n == 2);
    assert(tm.quints.len() == total);
    assert(m > 1) by(nonlinear_arith) requires m == 19 + 16 * len;
    assert(0 < tm.n < tm.m) by(nonlinear_arith) requires tm.n == 2, m == 19 + 16 * len, tm.m == m;

    // quint_wf for every quintuple.
    assert forall|i: int| #![trigger tm.quints[i]] 0 <= i < total implies quint_wf(tm.quints[i], 2, m) by {
        let ii = i as nat;
        assert(tm.quints[i] == gen(rm, ii));
        lemma_gen_key(rm, ii);
        let pc = ii / 48;
        let off = (ii % 48) / 3;
        let sym = (ii % 48) % 3;
        // pc ≤ len, off < 16, sym ≤ 2.
        lemma_idx_decomp(ii, len);
        // scanned a = sym ≤ 2.
        assert(tm.quints[i].a == sym);
        // state q = entry(pc)+off ∈ [3, m).
        assert(tm.quints[i].q == entry(pc) + off);
        assert(entry(pc) + off >= 3);
        assert(entry(pc) + off < m) by(nonlinear_arith)
            requires entry(pc) == 3 + 16 * pc, pc <= len, off < 16, m == 19 + 16 * len;
        // a2 ≤ 2 and q2 < m via the action bounds.
        lemma_act_bounds(rm, pc, off, sym);
        assert(tm.quints[i].a2 == pos_act(rm, pc, off, sym).0);
        assert(tm.quints[i].q2 == pos_act(rm, pc, off, sym).1);
    }

    // determinism: gen(i).(q,a) == gen(j).(q,a) ⟹ i == j, by index recovery.
    assert forall|i: int, j: int|
        0 <= i < total && 0 <= j < total
        && #[trigger] tm.quints[i].q == #[trigger] tm.quints[j].q
        && tm.quints[i].a == tm.quints[j].a
        implies i == j
    by {
        let ii = i as nat;
        let jj = j as nat;
        assert(tm.quints[i] == gen(rm, ii));
        assert(tm.quints[j] == gen(rm, jj));
        lemma_gen_key(rm, ii);
        lemma_gen_key(rm, jj);
        lemma_idx_recover(ii, jj);
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Index arithmetic helpers.
// ─────────────────────────────────────────────────────────────────────────────

/// For a valid flat index, `pc = idx/48 ≤ len`, `off = (idx%48)/3 < 16`, `sym = (idx%48)%3 ≤ 2`.
pub proof fn lemma_idx_decomp(idx: nat, len: nat)
    requires
        idx < 48 * (len + 1),
    ensures
        idx / 48 <= len,
        (idx % 48) / 3 < 16,
        (idx % 48) % 3 <= 2,
{
    // idx < 48*(len+1) ⟹ idx/48 < len+1 ⟹ ≤ len.
    lemma_fundamental_div_mod(idx as int, 48);
    assert(idx / 48 <= len) by(nonlinear_arith)
        requires idx < 48 * (len + 1), idx == 48 * (idx / 48) + idx % 48, 0 <= idx % 48 < 48;
    // idx%48 < 48 ⟹ (idx%48)/3 < 16.
    lemma_fundamental_div_mod((idx % 48) as int, 3);
    assert((idx % 48) / 3 < 16) by(nonlinear_arith)
        requires idx % 48 < 48, (idx % 48) == 3 * ((idx % 48) / 3) + (idx % 48) % 3, 0 <= (idx % 48) % 3 < 3;
    assert((idx % 48) % 3 <= 2);
}

/// **Index recovery.** If two flat indices give `gen` quintuples with equal `(q, a)` then the indices
/// are equal. From `entry(i/48)+(i%48)/3 == entry(j/48)+(j%48)/3` (stride 16 > max offset 15) the
/// window `i/48` and offset `(i%48)/3` match; with equal scanned `(i%48)%3` the residue `i%48`
/// matches, hence `i == j`.
pub proof fn lemma_idx_recover(i: nat, j: nat)
    requires
        entry(i / 48) + (i % 48) / 3 == entry(j / 48) + (j % 48) / 3,
        (i % 48) % 3 == (j % 48) % 3,
    ensures
        i == j,
{
    let pi = i / 48; let oi = (i % 48) / 3; let si = (i % 48) % 3;
    let pj = j / 48; let oj = (j % 48) / 3; let sj = (j % 48) % 3;
    // offsets are < 16.
    lemma_fundamental_div_mod((i % 48) as int, 3);
    lemma_fundamental_div_mod((j % 48) as int, 3);
    assert(oi < 16) by(nonlinear_arith)
        requires i % 48 < 48, (i % 48) == 3 * oi + si, 0 <= si < 3;
    assert(oj < 16) by(nonlinear_arith)
        requires j % 48 < 48, (j % 48) == 3 * oj + sj, 0 <= sj < 3;
    // entry(pi)+oi == entry(pj)+oj  ⟹  16*pi+oi == 16*pj+oj  ⟹  pi==pj ∧ oi==oj (oi,oj < 16).
    assert(16 * pi + oi == 16 * pj + oj) by(nonlinear_arith)
        requires entry(pi) + oi == entry(pj) + oj, entry(pi) == 3 + 16 * pi, entry(pj) == 3 + 16 * pj;
    lemma_fundamental_div_mod_converse((16 * pi + oi) as int, 16, pi as int, oi as int);
    lemma_fundamental_div_mod_converse((16 * pj + oj) as int, 16, pj as int, oj as int);
    assert(pi == pj && oi == oj);
    // i%48 == 3*oi+si == 3*oj+sj == j%48; and i/48 == j/48; so i == j.
    assert(i % 48 == j % 48) by(nonlinear_arith)
        requires (i % 48) == 3 * oi + si, (j % 48) == 3 * oj + sj, oi == oj, si == sj;
    lemma_fundamental_div_mod(i as int, 48);
    lemma_fundamental_div_mod(j as int, 48);
    assert(i == j) by(nonlinear_arith)
        requires i == 48 * (i / 48) + i % 48, j == 48 * (j / 48) + j % 48, pi == pj, i % 48 == j % 48,
            pi == i / 48, pj == j / 48;
}

} // verus!
