//! # GAP-2-E brick B6 (part 1) — the cleanup phase + halt routing reach the origin
//!
//! `rm_to_tm`'s last window (`pc == rm.instructions.len()`) is the **cleanup** block, and every
//! `Halt` instruction routes there via a left bounce. This module proves those already-built
//! quintuples actually drive the tape to `tm_origin() = (0,0,0,0)`:
//!
//!   * `lemma_sim_halt` — a `Halt` instruction's two quintuples bounce `entry(pc) → entry(len)`
//!     (the cleanup entry), counters unchanged.
//!   * `lemma_cleanup_phaseA` — the left dec-loop: `(c1,c2,entry(len)) →* (0,c2,entry(len)+6)`,
//!     by induction on `c1` (peek + dec + bounce-back-to-entry per iteration).
//!   * `lemma_cleanup_phaseB` — the right dec-loop mirror: `(c1,c2,entry(len)+6) →* (c1,0,entry(len)+12)`.
//!   * `lemma_cleanup_phaseC` — the final `(CC,2,0,0,R)` quintuple: `(0,0,entry(len)+12) →¹ origin`.
//!   * `lemma_cleanup` — composes A (with right counter untouched) + B (left counter already 0) + C.
//!
//! Each gadget reuses the existing parametric peek/dec/bounce lemmas (`tm_gadget`, `tm_dec`,
//! `tm_bounce`, `tm_right_gadgets`) by extracting the cleanup quintuples with `lemma_quint_at` at
//! window `pc = len`. The run-algebra (`lemma_tm_run_split`) and `tm_reaches` chaining come from
//! `tm_run_lemmas` / `tm_sim`. Fully verified, no verifier escape hatches.
//!
//! See `docs/gap2-register-to-tm-plan.md` (B6 entry points + cleanup layout).

use vstd::prelude::*;
use crate::machine::{RegisterMachine, Instruction, machine_wf};
use crate::tm::{Tm, tm_run, tm_step, tm_origin, apply_quint, quint_matches};
use crate::tm_two_counter::{two_counter_config, repunit_m, sep, lemma_repunit_zero};
use crate::tm_gadget::{lemma_peek_gadget, lemma_tm_step_picks};
use crate::tm_dec::lemma_dec;
use crate::tm_bounce::{lemma_bounce_left, lemma_bounce_right};
use crate::tm_right_gadgets::{lemma_peek_right, lemma_dec_right};
use crate::tm_run_lemmas::lemma_tm_run_split;
use crate::tm_sim::{tm_reaches, lemma_tm_reaches_intro, lemma_tm_reaches_trans, lemma_quint_at};
use crate::tm_assemble::{entry, tm_mod, rm_to_tm, lemma_rm_to_tm_wf};

verus! {

// ─────────────────────────────────────────────────────────────────────────────
// Halt routing: a Halt instruction bounces into the cleanup entry.
// ─────────────────────────────────────────────────────────────────────────────

/// **A `Halt` instruction routes to cleanup.** From `two_counter_config(c1,c2,entry(pc))` the two
/// `halt_act` quintuples (a left bounce `entry(pc) → entry(len)`) leave the counters unchanged and
/// land the head on the separator in the cleanup-entry state `entry(len)`.
pub proof fn lemma_sim_halt(rm: RegisterMachine, pc: nat, c1: nat, c2: nat)
    requires
        machine_wf(rm),
        pc < rm.instructions.len(),
        rm.instructions[pc as int] == Instruction::Halt,
    ensures
        tm_reaches(rm_to_tm(rm),
            two_counter_config(c1, c2, entry(pc), tm_mod(rm.instructions.len())),
            two_counter_config(c1, c2, entry(rm.instructions.len()), tm_mod(rm.instructions.len()))),
{
    let tm = rm_to_tm(rm);
    let len = rm.instructions.len();
    let m = tm_mod(len);
    lemma_rm_to_tm_wf(rm);
    assert(tm.m == m && tm.n == 2);
    assert(tm.quints.len() == 48 * (len + 1));
    let e = entry(pc);
    assert(e < m) by(nonlinear_arith) requires e == 3 + 16 * pc, pc < len, m == 19 + 16 * len;

    lemma_quint_at(rm, pc, 0, 2);   // (e,2,2,e+1,L)
    lemma_quint_at(rm, pc, 1, 1);   // (e+1,1,1,entry(len),R)
    lemma_quint_at(rm, pc, 1, 0);   // (e+1,0,0,entry(len),R)
    let i_b = (pc * 48 + 2) as int;
    let i_one = (pc * 48 + 4) as int;
    let i_zero = (pc * 48 + 3) as int;
    assert(0 <= i_b < tm.quints.len() && 0 <= i_one < tm.quints.len() && 0 <= i_zero < tm.quints.len())
        by(nonlinear_arith)
        requires pc < len, tm.quints.len() == 48 * (len + 1),
            i_b == pc*48+2, i_one == pc*48+4, i_zero == pc*48+3;

    let start = two_counter_config(c1, c2, e, tm.m);
    lemma_bounce_left(tm, c1, c2, e, e + 1, entry(len), i_b, i_one, i_zero);
    let fin = two_counter_config(c1, c2, entry(len), tm.m);
    assert(tm_run(tm, start, 2) == fin);
    lemma_tm_reaches_intro(tm, start, fin, 2);
}

// ─────────────────────────────────────────────────────────────────────────────
// Cleanup phase A: dec the left counter to 0  (states entry(len)..entry(len)+5).
// ─────────────────────────────────────────────────────────────────────────────

/// **Cleanup phase A — drain the left counter.** From `two_counter_config(c1,c2,entry(len))` the
/// peek+dec+bounce loop reaches `two_counter_config(0,c2,entry(len)+6)` (the phase-B entry), by
/// induction on `c1`: when `c1 = 0` the peek's zero-branch jumps to `entry(len)+6`; when `c1 > 0` a
/// peek (→ dec), a dec (`c1 → c1-1`), and a bounce-back-to-`entry(len)` complete one loop iteration.
pub proof fn lemma_cleanup_phaseA(rm: RegisterMachine, c1: nat, c2: nat)
    requires
        machine_wf(rm),
    ensures
        tm_reaches(rm_to_tm(rm),
            two_counter_config(c1, c2, entry(rm.instructions.len()), tm_mod(rm.instructions.len())),
            two_counter_config(0, c2, entry(rm.instructions.len()) + 6, tm_mod(rm.instructions.len()))),
    decreases c1,
{
    let tm = rm_to_tm(rm);
    let len = rm.instructions.len();
    let m = tm_mod(len);
    lemma_rm_to_tm_wf(rm);
    assert(tm.m == m && tm.n == 2);
    assert(tm.quints.len() == 48 * (len + 1));
    let e = entry(len);
    assert(e + 6 < m && e + 4 < m && e + 2 < m) by(nonlinear_arith)
        requires e == 3 + 16 * len, m == 19 + 16 * len;

    // Peek quintuples: (e,2,2,e+1,L), (e+1,1,1,e+2,R), (e+1,0,0,e+6,R).
    lemma_quint_at(rm, len, 0, 2);
    lemma_quint_at(rm, len, 1, 1);
    lemma_quint_at(rm, len, 1, 0);
    let pk_entry = (len * 48 + 2) as int;
    let pk_pos = (len * 48 + 4) as int;
    let pk_zero = (len * 48 + 3) as int;
    assert(0 <= pk_entry < tm.quints.len() && 0 <= pk_pos < tm.quints.len()
        && 0 <= pk_zero < tm.quints.len()) by(nonlinear_arith)
        requires tm.quints.len() == 48 * (len + 1),
            pk_entry == len*48+2, pk_pos == len*48+4, pk_zero == len*48+3;

    let start = two_counter_config(c1, c2, e, tm.m);

    if c1 == 0 {
        lemma_peek_gadget(tm, c1, c2, e, e + 1, e + 2, e + 6, pk_entry, pk_pos, pk_zero);
        let fin = two_counter_config(0, c2, e + 6, tm.m);
        assert(tm_run(tm, start, 2) == fin);
        lemma_tm_reaches_intro(tm, start, fin, 2);
    } else {
        // dec quintuples: (e+2,2,2,e+2,L),(e+2,1,1,e+2,L),(e+2,0,0,e+3,R),(e+3,1,0,e+4,R),(e+4,1,1,e+4,R).
        lemma_quint_at(rm, len, 2, 2);
        lemma_quint_at(rm, len, 2, 1);
        lemma_quint_at(rm, len, 2, 0);
        lemma_quint_at(rm, len, 3, 1);
        lemma_quint_at(rm, len, 4, 1);
        // bounce quintuples: (e+4,2,2,e+5,L),(e+5,1,1,e,R),(e+5,0,0,e,R).
        lemma_quint_at(rm, len, 4, 2);
        lemma_quint_at(rm, len, 5, 1);
        lemma_quint_at(rm, len, 5, 0);
        let d_sep = (len * 48 + 8) as int;
        let d_one_l = (len * 48 + 7) as int;
        let d_turn = (len * 48 + 6) as int;
        let d_disc = (len * 48 + 10) as int;
        let d_one_r = (len * 48 + 13) as int;
        let b_b = (len * 48 + 14) as int;
        let b_one = (len * 48 + 16) as int;
        let b_zero = (len * 48 + 15) as int;
        assert(0 <= d_sep < tm.quints.len() && 0 <= d_one_l < tm.quints.len()
            && 0 <= d_turn < tm.quints.len() && 0 <= d_disc < tm.quints.len()
            && 0 <= d_one_r < tm.quints.len() && 0 <= b_b < tm.quints.len()
            && 0 <= b_one < tm.quints.len() && 0 <= b_zero < tm.quints.len()) by(nonlinear_arith)
            requires tm.quints.len() == 48 * (len + 1),
                d_sep == len*48+8, d_one_l == len*48+7, d_turn == len*48+6, d_disc == len*48+10,
                d_one_r == len*48+13, b_b == len*48+14, b_one == len*48+16, b_zero == len*48+15;

        // peek (pos) : start --2--> (c1,c2,e+2).
        lemma_peek_gadget(tm, c1, c2, e, e + 1, e + 2, e + 6, pk_entry, pk_pos, pk_zero);
        let cfg_pos = two_counter_config(c1, c2, e + 2, tm.m);
        assert(tm_run(tm, start, 2) == cfg_pos);
        // dec : (c1,c2,e+2) --(2c1+2)--> (c1-1,c2,e+4).
        lemma_dec(tm, c1, c2, e + 2, e + 3, e + 4, d_sep, d_one_l, d_turn, d_disc, d_one_r);
        let cfg_dec = two_counter_config((c1 - 1) as nat, c2, e + 4, tm.m);
        assert(tm_run(tm, cfg_pos, (2 * c1 + 2) as nat) == cfg_dec);
        // bounce : (c1-1,c2,e+4) --2--> (c1-1,c2,e).
        lemma_bounce_left(tm, (c1 - 1) as nat, c2, e + 4, e + 5, e, b_b, b_one, b_zero);
        let cfg_loop = two_counter_config((c1 - 1) as nat, c2, e, tm.m);
        assert(tm_run(tm, cfg_dec, 2) == cfg_loop);
        // chain: start --(2 + (2c1+2) + 2)--> cfg_loop.
        lemma_tm_run_split(tm, start, 2, (2 * c1 + 2) as nat);
        assert(tm_run(tm, start, (2 + (2 * c1 + 2)) as nat) == cfg_dec);
        lemma_tm_run_split(tm, start, (2 + (2 * c1 + 2)) as nat, 2);
        assert((2 + (2 * c1 + 2) + 2) as nat == (2 * c1 + 6) as nat);
        assert(tm_run(tm, start, (2 * c1 + 6) as nat) == cfg_loop);
        lemma_tm_reaches_intro(tm, start, cfg_loop, (2 * c1 + 6) as nat);
        // IH: cfg_loop --*--> (0,c2,e+6).
        lemma_cleanup_phaseA(rm, (c1 - 1) as nat, c2);
        lemma_tm_reaches_trans(tm, start, cfg_loop, two_counter_config(0, c2, e + 6, tm.m));
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Cleanup phase B: dec the right counter to 0  (states entry(len)+6..entry(len)+11).
// ─────────────────────────────────────────────────────────────────────────────

/// **Cleanup phase B — drain the right counter.** Mirror of phase A on `c2` (the head walks right
/// through `v`): from `two_counter_config(c1,c2,entry(len)+6)` reach `two_counter_config(c1,0,entry(len)+12)`,
/// by induction on `c2`. The left counter `c1` is preserved (instantiated to `0` by `lemma_cleanup`).
pub proof fn lemma_cleanup_phaseB(rm: RegisterMachine, c1: nat, c2: nat)
    requires
        machine_wf(rm),
    ensures
        tm_reaches(rm_to_tm(rm),
            two_counter_config(c1, c2, entry(rm.instructions.len()) + 6, tm_mod(rm.instructions.len())),
            two_counter_config(c1, 0, entry(rm.instructions.len()) + 12, tm_mod(rm.instructions.len()))),
    decreases c2,
{
    let tm = rm_to_tm(rm);
    let len = rm.instructions.len();
    let m = tm_mod(len);
    lemma_rm_to_tm_wf(rm);
    assert(tm.m == m && tm.n == 2);
    assert(tm.quints.len() == 48 * (len + 1));
    let e = entry(len);
    assert(e + 12 < m && e + 10 < m && e + 8 < m && e + 6 < m) by(nonlinear_arith)
        requires e == 3 + 16 * len, m == 19 + 16 * len;

    // Peek-right quintuples: (e+6,2,2,e+7,R), (e+7,1,1,e+8,L), (e+7,0,0,e+12,L).
    lemma_quint_at(rm, len, 6, 2);
    lemma_quint_at(rm, len, 7, 1);
    lemma_quint_at(rm, len, 7, 0);
    let pk_entry = (len * 48 + 20) as int;
    let pk_pos = (len * 48 + 22) as int;
    let pk_zero = (len * 48 + 21) as int;
    assert(0 <= pk_entry < tm.quints.len() && 0 <= pk_pos < tm.quints.len()
        && 0 <= pk_zero < tm.quints.len()) by(nonlinear_arith)
        requires tm.quints.len() == 48 * (len + 1),
            pk_entry == len*48+20, pk_pos == len*48+22, pk_zero == len*48+21;

    let start = two_counter_config(c1, c2, e + 6, tm.m);

    if c2 == 0 {
        lemma_peek_right(tm, c1, c2, e + 6, e + 7, e + 8, e + 12, pk_entry, pk_pos, pk_zero);
        let fin = two_counter_config(c1, 0, e + 12, tm.m);
        assert(tm_run(tm, start, 2) == fin);
        lemma_tm_reaches_intro(tm, start, fin, 2);
    } else {
        // dec-right quintuples: (e+8,2,2,e+8,R),(e+8,1,1,e+8,R),(e+8,0,0,e+9,L),(e+9,1,0,e+10,L),(e+10,1,1,e+10,L).
        lemma_quint_at(rm, len, 8, 2);
        lemma_quint_at(rm, len, 8, 1);
        lemma_quint_at(rm, len, 8, 0);
        lemma_quint_at(rm, len, 9, 1);
        lemma_quint_at(rm, len, 10, 1);
        // bounce-right quintuples: (e+10,2,2,e+11,R),(e+11,1,1,e+6,L),(e+11,0,0,e+6,L).
        lemma_quint_at(rm, len, 10, 2);
        lemma_quint_at(rm, len, 11, 1);
        lemma_quint_at(rm, len, 11, 0);
        let d_sep = (len * 48 + 26) as int;
        let d_one_r = (len * 48 + 25) as int;
        let d_turn = (len * 48 + 24) as int;
        let d_disc = (len * 48 + 28) as int;
        let d_one_l = (len * 48 + 31) as int;
        let b_b = (len * 48 + 32) as int;
        let b_one = (len * 48 + 34) as int;
        let b_zero = (len * 48 + 33) as int;
        assert(0 <= d_sep < tm.quints.len() && 0 <= d_one_r < tm.quints.len()
            && 0 <= d_turn < tm.quints.len() && 0 <= d_disc < tm.quints.len()
            && 0 <= d_one_l < tm.quints.len() && 0 <= b_b < tm.quints.len()
            && 0 <= b_one < tm.quints.len() && 0 <= b_zero < tm.quints.len()) by(nonlinear_arith)
            requires tm.quints.len() == 48 * (len + 1),
                d_sep == len*48+26, d_one_r == len*48+25, d_turn == len*48+24, d_disc == len*48+28,
                d_one_l == len*48+31, b_b == len*48+32, b_one == len*48+34, b_zero == len*48+33;

        // peek-right (pos) : start --2--> (c1,c2,e+8).
        lemma_peek_right(tm, c1, c2, e + 6, e + 7, e + 8, e + 12, pk_entry, pk_pos, pk_zero);
        let cfg_pos = two_counter_config(c1, c2, e + 8, tm.m);
        assert(tm_run(tm, start, 2) == cfg_pos);
        // dec-right : (c1,c2,e+8) --(2c2+2)--> (c1,c2-1,e+10).
        lemma_dec_right(tm, c1, c2, e + 8, e + 9, e + 10, d_sep, d_one_r, d_turn, d_disc, d_one_l);
        let cfg_dec = two_counter_config(c1, (c2 - 1) as nat, e + 10, tm.m);
        assert(tm_run(tm, cfg_pos, (2 * c2 + 2) as nat) == cfg_dec);
        // bounce-right : (c1,c2-1,e+10) --2--> (c1,c2-1,e+6).
        lemma_bounce_right(tm, c1, (c2 - 1) as nat, e + 10, e + 11, e + 6, b_b, b_one, b_zero);
        let cfg_loop = two_counter_config(c1, (c2 - 1) as nat, e + 6, tm.m);
        assert(tm_run(tm, cfg_dec, 2) == cfg_loop);
        // chain: start --(2 + (2c2+2) + 2)--> cfg_loop.
        lemma_tm_run_split(tm, start, 2, (2 * c2 + 2) as nat);
        assert(tm_run(tm, start, (2 + (2 * c2 + 2)) as nat) == cfg_dec);
        lemma_tm_run_split(tm, start, (2 + (2 * c2 + 2)) as nat, 2);
        assert((2 + (2 * c2 + 2) + 2) as nat == (2 * c2 + 6) as nat);
        assert(tm_run(tm, start, (2 * c2 + 6) as nat) == cfg_loop);
        lemma_tm_reaches_intro(tm, start, cfg_loop, (2 * c2 + 6) as nat);
        // IH: cfg_loop --*--> (c1,0,e+12).
        lemma_cleanup_phaseB(rm, c1, (c2 - 1) as nat);
        lemma_tm_reaches_trans(tm, start, cfg_loop, two_counter_config(c1, 0, e + 12, tm.m));
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Cleanup phase C: blank the separator into the origin  (one step).
// ─────────────────────────────────────────────────────────────────────────────

/// **Cleanup phase C — drop to the origin.** With both counters drained, the single quintuple
/// `(entry(len)+12, 2, 0, 0, R)` reads the lone separator (`u = v = 0`, scanned `2`), writes a blank
/// and moves right into the all-zero state: `two_counter_config(0,0,entry(len)+12) →¹ tm_origin()`.
pub proof fn lemma_cleanup_phaseC(rm: RegisterMachine)
    requires
        machine_wf(rm),
    ensures
        tm_run(rm_to_tm(rm),
            two_counter_config(0, 0, entry(rm.instructions.len()) + 12, tm_mod(rm.instructions.len())),
            1) == tm_origin(),
{
    let tm = rm_to_tm(rm);
    let len = rm.instructions.len();
    let m = tm_mod(len);
    lemma_rm_to_tm_wf(rm);
    assert(tm.m == m && tm.n == 2);
    assert(tm.quints.len() == 48 * (len + 1));
    let e = entry(len);
    assert(e + 12 < m) by(nonlinear_arith) requires e == 3 + 16 * len, m == 19 + 16 * len;

    lemma_quint_at(rm, len, 12, 2);   // (e+12, 2, 0, 0, R)
    let i_cc = (len * 48 + 38) as int;
    assert(0 <= i_cc < tm.quints.len()) by(nonlinear_arith)
        requires tm.quints.len() == 48 * (len + 1), i_cc == len*48+38;

    let cfg = two_counter_config(0, 0, e + 12, tm.m);
    lemma_repunit_zero(m);   // repunit_m(0,m) == 0
    assert(cfg.u == 0 && cfg.v == 0 && cfg.a == sep() && cfg.q == e + 12);
    // (e+12,2,...) matches cfg: q == e+12, a == sep() == 2.
    assert(quint_matches(tm.quints[i_cc], cfg));
    lemma_tm_step_picks(tm, cfg, i_cc);
    let next = apply_quint(tm.quints[i_cc], cfg, tm.m);
    assert(tm_step(tm, cfg) == Some(next));
    // R-move with a2 == 0, q2 == 0: u' = 0*m + 0 = 0, v' = 0/m = 0, a' = 0%m = 0, q' = 0 == origin.
    assert(0nat * m == 0) by(nonlinear_arith);
    assert(0nat / m == 0) by(nonlinear_arith) requires m > 0;
    assert(0nat % m == 0) by(nonlinear_arith) requires m > 0;
    assert(next == tm_origin());
    assert(tm_run(tm, next, 0) == next);
    assert(tm_run(tm, cfg, 1) == next);
}

// ─────────────────────────────────────────────────────────────────────────────
// The full cleanup: A → B → C reaches the origin from the cleanup entry.
// ─────────────────────────────────────────────────────────────────────────────

/// **The cleanup reaches the origin.** From the cleanup entry `two_counter_config(c1,c2,entry(len))`
/// the TM reaches `tm_origin()`: drain the left counter (phase A), drain the right counter (phase B,
/// left already 0), then blank the separator (phase C).
pub proof fn lemma_cleanup(rm: RegisterMachine, c1: nat, c2: nat)
    requires
        machine_wf(rm),
    ensures
        tm_reaches(rm_to_tm(rm),
            two_counter_config(c1, c2, entry(rm.instructions.len()), tm_mod(rm.instructions.len())),
            tm_origin()),
{
    let tm = rm_to_tm(rm);
    let len = rm.instructions.len();
    lemma_rm_to_tm_wf(rm);
    let e = entry(len);
    let m = tm.m;

    lemma_cleanup_phaseA(rm, c1, c2);   // (c1,c2,e) --*--> (0,c2,e+6)
    lemma_cleanup_phaseB(rm, 0, c2);    // (0,c2,e+6) --*--> (0,0,e+12)
    lemma_cleanup_phaseC(rm);           // (0,0,e+12) --1--> origin
    lemma_tm_reaches_intro(tm, two_counter_config(0, 0, e + 12, m), tm_origin(), 1);

    // chain A then B then C.
    lemma_tm_reaches_trans(tm,
        two_counter_config(c1, c2, e, m),
        two_counter_config(0, c2, e + 6, m),
        two_counter_config(0, 0, e + 12, m));
    lemma_tm_reaches_trans(tm,
        two_counter_config(c1, c2, e, m),
        two_counter_config(0, 0, e + 12, m),
        tm_origin());
}

} // verus!
