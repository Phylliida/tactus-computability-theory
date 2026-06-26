//! # GAP-2-E brick B5.4/B5.5 — per-instruction one-step simulation
//!
//! Each 2-counter instruction at program position `pc` is simulated by its gadget block: from the
//! head-on-separator layout `two_counter_config(c1, c2, entry(pc))` the TM runs (some fuel) to the
//! layout of the register machine's *next* configuration. `tm_reaches` packages the existential fuel
//! and is transitive (via the unconditional run-split), so B6 can chain it along a whole 2-counter
//! run.
//!
//! The gadget quintuples are extracted from `rm_to_tm` by `lemma_quint_at`: the quintuple at flat
//! index `pc·48 + off·3 + sym` is `mk_quint(entry(pc)+off, sym, pos_act(rm,pc,off,sym)…)`, so with the
//! instruction known each `(off,sym)` slot evaluates to the concrete gadget transition the gadget
//! lemmas (`lemma_inc`, `lemma_dec`, `lemma_peek_gadget`, `lemma_bounce_left`, and their right
//! mirrors) require. Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse;
use verus_group_theory::machine_group::Dir;
use crate::machine::{RegisterMachine, Instruction, Configuration, machine_wf, config_wf, step};
use crate::multi_output_primitives::{mk_inc, mk_dj, mk_jump};
use crate::tm::{Tm, TmConfig, tm_run};
use crate::tm_two_counter::two_counter_config;
use crate::tm_gadget::{mk_quint, lemma_peek_gadget};
use crate::tm_inc::lemma_inc;
use crate::tm_dec::lemma_dec;
use crate::tm_right_gadgets::{lemma_peek_right, lemma_inc_right, lemma_dec_right};
use crate::tm_bounce::{lemma_bounce_left, lemma_bounce_right};
use crate::tm_run_lemmas::lemma_tm_run_split;
use crate::tm_assemble::{entry, tm_mod, pos_act, gen, rm_to_tm, lemma_rm_to_tm_wf};

verus! {

/// The TM, started from `c`, reaches `c2` in some (existentially quantified) number of steps.
pub open spec fn tm_reaches(tm: Tm, c: TmConfig, c2: TmConfig) -> bool {
    exists|fuel: nat| tm_run(tm, c, fuel) == c2
}

/// Introduce `tm_reaches` from a concrete run.
pub proof fn lemma_tm_reaches_intro(tm: Tm, c: TmConfig, c2: TmConfig, fuel: nat)
    requires
        tm_run(tm, c, fuel) == c2,
    ensures
        tm_reaches(tm, c, c2),
{
    assert(tm_run(tm, c, fuel) == c2);   // witness for the exists
}

/// `tm_reaches` is transitive (compose the two fuels via the unconditional run-split).
pub proof fn lemma_tm_reaches_trans(tm: Tm, a: TmConfig, b: TmConfig, c: TmConfig)
    requires
        tm_reaches(tm, a, b),
        tm_reaches(tm, b, c),
    ensures
        tm_reaches(tm, a, c),
{
    let f1 = choose|fuel: nat| tm_run(tm, a, fuel) == b;
    let f2 = choose|fuel: nat| tm_run(tm, b, fuel) == c;
    lemma_tm_run_split(tm, a, f1, f2);
    assert(tm_run(tm, a, (f1 + f2) as nat) == c);
}

/// The TM, started from `c`, reaches `c2` in a **strictly positive** number of steps. The backward
/// direction (B6) inducts on TM fuel and needs every simulated 2-counter step to consume `≥ 1` TM
/// step, so the fuel strictly decreases — even for a `DecJump`-on-zero self-loop, where the encoded
/// configs coincide (`enc(c) == enc(step(c))`) yet the gadget still runs two peek steps.
pub open spec fn tm_reaches_pos(tm: Tm, c: TmConfig, c2: TmConfig) -> bool {
    exists|fuel: nat| 1 <= fuel && tm_run(tm, c, fuel) == c2
}

/// Introduce `tm_reaches_pos` from a concrete positive run.
pub proof fn lemma_tm_reaches_pos_intro(tm: Tm, c: TmConfig, c2: TmConfig, fuel: nat)
    requires
        1 <= fuel,
        tm_run(tm, c, fuel) == c2,
    ensures
        tm_reaches_pos(tm, c, c2),
{
    assert(1 <= fuel && tm_run(tm, c, fuel) == c2);   // witness for the exists
}

// ─────────────────────────────────────────────────────────────────────────────
// Quintuple extraction.
// ─────────────────────────────────────────────────────────────────────────────

/// The quintuple at slot `(off, sym)` of program position `pc`'s window sits at flat index
/// `pc·48 + off·3 + sym` and equals `mk_quint(entry(pc)+off, sym, pos_act(rm,pc,off,sym)…)`.
pub proof fn lemma_quint_at(rm: RegisterMachine, pc: nat, off: nat, sym: nat)
    requires
        pc <= rm.instructions.len(),
        off < 16,
        sym < 3,
    ensures
        rm_to_tm(rm).quints[(pc * 48 + off * 3 + sym) as int]
            == mk_quint(entry(pc) + off, sym,
                pos_act(rm, pc, off, sym).0, pos_act(rm, pc, off, sym).1, pos_act(rm, pc, off, sym).2),
{
    let len = rm.instructions.len();
    let r = off * 3 + sym;
    let flat = pc * 48 + r;
    assert(r < 48) by(nonlinear_arith) requires off < 16, sym < 3, r == off * 3 + sym;
    assert(flat < 48 * (len + 1)) by(nonlinear_arith)
        requires pc <= len, r < 48, flat == pc * 48 + r;
    // flat / 48 == pc, flat % 48 == r.
    lemma_fundamental_div_mod_converse(flat as int, 48, pc as int, r as int);
    // r / 3 == off, r % 3 == sym.
    lemma_fundamental_div_mod_converse(r as int, 3, off as int, sym as int);
    // gen unfolds to the claimed mk_quint at this index.
    assert(rm_to_tm(rm).quints[flat as int] == gen(rm, flat as nat));
    assert(pc * 48 + off * 3 + sym == flat);
}

// ─────────────────────────────────────────────────────────────────────────────
// Per-instruction simulation.
// ─────────────────────────────────────────────────────────────────────────────

/// **Inc on the left counter (register 0).** From `two_counter_config(c1,c2,entry(pc))` the TM
/// reaches `two_counter_config(c1+1, c2, entry(pc+1))` — the inc-left gadget then the left bounce.
pub proof fn lemma_sim_inc_left(rm: RegisterMachine, pc: nat, c1: nat, c2: nat)
    requires
        machine_wf(rm),
        pc < rm.instructions.len(),
        rm.instructions[pc as int] == mk_inc(0),
    ensures
        tm_reaches(rm_to_tm(rm),
            two_counter_config(c1, c2, entry(pc), tm_mod(rm.instructions.len())),
            two_counter_config((c1 + 1) as nat, c2, entry((pc + 1) as nat), tm_mod(rm.instructions.len()))),
        tm_reaches_pos(rm_to_tm(rm),
            two_counter_config(c1, c2, entry(pc), tm_mod(rm.instructions.len())),
            two_counter_config((c1 + 1) as nat, c2, entry((pc + 1) as nat), tm_mod(rm.instructions.len()))),
{
    let tm = rm_to_tm(rm);
    let len = rm.instructions.len();
    let m = tm_mod(len);
    lemma_rm_to_tm_wf(rm);
    assert(tm.m == m && tm.n == 2);
    let e = entry(pc);
    assert(e + 16 == entry((pc + 1) as nat));
    assert(e < m) by(nonlinear_arith) requires e == 3 + 16 * pc, pc < len, m == 19 + 16 * len;
    assert(e + 1 < m) by(nonlinear_arith) requires e == 3 + 16 * pc, pc < len, m == 19 + 16 * len;

    // Extract the four inc quintuples + three bounce quintuples; pos_act picks inc_left_act.
    lemma_quint_at(rm, pc, 0, 2);   // i_sep   @ pc*48+2 : (e,2,2,e,L)
    lemma_quint_at(rm, pc, 0, 1);   // i_one_l @ pc*48+1 : (e,1,1,e,L)
    lemma_quint_at(rm, pc, 0, 0);   // i_turn  @ pc*48+0 : (e,0,1,e+1,R)
    lemma_quint_at(rm, pc, 1, 1);   // i_one_r @ pc*48+4 : (e+1,1,1,e+1,R)
    lemma_quint_at(rm, pc, 1, 2);   // bounce i_b  @ pc*48+5 : (e+1,2,2,e+2,L)
    lemma_quint_at(rm, pc, 2, 1);   // bounce i_one@ pc*48+7 : (e+2,1,1,e+16,R)
    lemma_quint_at(rm, pc, 2, 0);   // bounce i_zero@pc*48+6 : (e+2,0,0,e+16,R)

    let i_sep = (pc * 48 + 2) as int;
    let i_one_l = (pc * 48 + 1) as int;
    let i_turn = (pc * 48 + 0) as int;
    let i_one_r = (pc * 48 + 4) as int;
    let i_b = (pc * 48 + 5) as int;
    let i_bone = (pc * 48 + 7) as int;
    let i_bzero = (pc * 48 + 6) as int;

    // index bounds (all < tm.quints.len() == 48*(len+1)).
    assert(0 <= i_sep < tm.quints.len() && 0 <= i_one_l < tm.quints.len()
        && 0 <= i_turn < tm.quints.len() && 0 <= i_one_r < tm.quints.len()
        && 0 <= i_b < tm.quints.len() && 0 <= i_bone < tm.quints.len()
        && 0 <= i_bzero < tm.quints.len()) by(nonlinear_arith)
        requires pc < len, tm.quints.len() == 48 * (len + 1),
            i_sep == pc*48+2, i_one_l == pc*48+1, i_turn == pc*48+0, i_one_r == pc*48+4,
            i_b == pc*48+5, i_bone == pc*48+7, i_bzero == pc*48+6;

    // inc gadget: cfg0 --(2c1+2)--> two_counter_config(c1+1, c2, e+1).
    let cfg0 = two_counter_config(c1, c2, e, tm.m);
    lemma_inc(tm, c1, c2, e, e + 1, i_sep, i_one_l, i_turn, i_one_r);
    let cfg_inc = two_counter_config((c1 + 1) as nat, c2, e + 1, tm.m);
    assert(tm_run(tm, cfg0, (2 * c1 + 2) as nat) == cfg_inc);

    // bounce: cfg_inc --(2)--> two_counter_config(c1+1, c2, e+16).
    lemma_bounce_left(tm, (c1 + 1) as nat, c2, e + 1, e + 2, e + 16, i_b, i_bone, i_bzero);
    let cfg_fin = two_counter_config((c1 + 1) as nat, c2, e + 16, tm.m);
    assert(tm_run(tm, cfg_inc, 2) == cfg_fin);

    // chain: cfg0 --(2c1+4)--> cfg_fin.
    lemma_tm_run_split(tm, cfg0, (2 * c1 + 2) as nat, 2);
    assert((2 * c1 + 2 + 2) as nat == (2 * c1 + 4) as nat);
    assert(tm_run(tm, cfg0, (2 * c1 + 4) as nat) == cfg_fin);
    lemma_tm_reaches_intro(tm, cfg0, cfg_fin, (2 * c1 + 4) as nat);
    lemma_tm_reaches_pos_intro(tm, cfg0, cfg_fin, (2 * c1 + 4) as nat);
}

/// **Inc on the right counter (register 1).** Mirror of `lemma_sim_inc_left`: reaches
/// `two_counter_config(c1, c2+1, entry(pc+1))`.
pub proof fn lemma_sim_inc_right(rm: RegisterMachine, pc: nat, c1: nat, c2: nat)
    requires
        machine_wf(rm),
        pc < rm.instructions.len(),
        rm.instructions[pc as int] == mk_inc(1),
    ensures
        tm_reaches(rm_to_tm(rm),
            two_counter_config(c1, c2, entry(pc), tm_mod(rm.instructions.len())),
            two_counter_config(c1, (c2 + 1) as nat, entry((pc + 1) as nat), tm_mod(rm.instructions.len()))),
        tm_reaches_pos(rm_to_tm(rm),
            two_counter_config(c1, c2, entry(pc), tm_mod(rm.instructions.len())),
            two_counter_config(c1, (c2 + 1) as nat, entry((pc + 1) as nat), tm_mod(rm.instructions.len()))),
{
    let tm = rm_to_tm(rm);
    let len = rm.instructions.len();
    let m = tm_mod(len);
    lemma_rm_to_tm_wf(rm);
    assert(tm.m == m && tm.n == 2);
    let e = entry(pc);
    assert(e + 16 == entry((pc + 1) as nat));
    assert(e < m && e + 1 < m) by(nonlinear_arith) requires e == 3 + 16 * pc, pc < len, m == 19 + 16 * len;

    lemma_quint_at(rm, pc, 0, 2);   // i_sep   @ pc*48+2 : (e,2,2,e,R)
    lemma_quint_at(rm, pc, 0, 1);   // i_one_r @ pc*48+1 : (e,1,1,e,R)
    lemma_quint_at(rm, pc, 0, 0);   // i_turn  @ pc*48+0 : (e,0,1,e+1,L)
    lemma_quint_at(rm, pc, 1, 1);   // i_one_l @ pc*48+4 : (e+1,1,1,e+1,L)
    lemma_quint_at(rm, pc, 1, 2);   // bounce i_b   @ pc*48+5 : (e+1,2,2,e+2,R)
    lemma_quint_at(rm, pc, 2, 1);   // bounce i_one @ pc*48+7 : (e+2,1,1,e+16,L)
    lemma_quint_at(rm, pc, 2, 0);   // bounce i_zero@ pc*48+6 : (e+2,0,0,e+16,L)

    let i_sep = (pc * 48 + 2) as int;
    let i_one_r = (pc * 48 + 1) as int;
    let i_turn = (pc * 48 + 0) as int;
    let i_one_l = (pc * 48 + 4) as int;
    let i_b = (pc * 48 + 5) as int;
    let i_bone = (pc * 48 + 7) as int;
    let i_bzero = (pc * 48 + 6) as int;

    assert(0 <= i_sep < tm.quints.len() && 0 <= i_one_r < tm.quints.len()
        && 0 <= i_turn < tm.quints.len() && 0 <= i_one_l < tm.quints.len()
        && 0 <= i_b < tm.quints.len() && 0 <= i_bone < tm.quints.len()
        && 0 <= i_bzero < tm.quints.len()) by(nonlinear_arith)
        requires pc < len, tm.quints.len() == 48 * (len + 1),
            i_sep == pc*48+2, i_one_r == pc*48+1, i_turn == pc*48+0, i_one_l == pc*48+4,
            i_b == pc*48+5, i_bone == pc*48+7, i_bzero == pc*48+6;

    let cfg0 = two_counter_config(c1, c2, e, tm.m);
    lemma_inc_right(tm, c1, c2, e, e + 1, i_sep, i_one_r, i_turn, i_one_l);
    let cfg_inc = two_counter_config(c1, (c2 + 1) as nat, e + 1, tm.m);
    assert(tm_run(tm, cfg0, (2 * c2 + 2) as nat) == cfg_inc);

    lemma_bounce_right(tm, c1, (c2 + 1) as nat, e + 1, e + 2, e + 16, i_b, i_bone, i_bzero);
    let cfg_fin = two_counter_config(c1, (c2 + 1) as nat, e + 16, tm.m);
    assert(tm_run(tm, cfg_inc, 2) == cfg_fin);

    lemma_tm_run_split(tm, cfg0, (2 * c2 + 2) as nat, 2);
    assert((2 * c2 + 2 + 2) as nat == (2 * c2 + 4) as nat);
    assert(tm_run(tm, cfg0, (2 * c2 + 4) as nat) == cfg_fin);
    lemma_tm_reaches_intro(tm, cfg0, cfg_fin, (2 * c2 + 4) as nat);
    lemma_tm_reaches_pos_intro(tm, cfg0, cfg_fin, (2 * c2 + 4) as nat);
}

/// **DecJump on the left counter (register 0).** Peek `c1`: if `c1 > 0`, decrement and fall through
/// to `pc+1`; if `c1 = 0`, jump to `target`. (Matches `machine::step` for `DecJump{0,target}`.)
pub proof fn lemma_sim_decjump_left(rm: RegisterMachine, pc: nat, t: nat, c1: nat, c2: nat)
    requires
        machine_wf(rm),
        pc < rm.instructions.len(),
        rm.instructions[pc as int] == mk_dj(0, t),
    ensures
        c1 > 0 ==> tm_reaches(rm_to_tm(rm),
            two_counter_config(c1, c2, entry(pc), tm_mod(rm.instructions.len())),
            two_counter_config((c1 - 1) as nat, c2, entry((pc + 1) as nat), tm_mod(rm.instructions.len()))),
        c1 == 0 ==> tm_reaches(rm_to_tm(rm),
            two_counter_config(c1, c2, entry(pc), tm_mod(rm.instructions.len())),
            two_counter_config(c1, c2, entry(t), tm_mod(rm.instructions.len()))),
        c1 > 0 ==> tm_reaches_pos(rm_to_tm(rm),
            two_counter_config(c1, c2, entry(pc), tm_mod(rm.instructions.len())),
            two_counter_config((c1 - 1) as nat, c2, entry((pc + 1) as nat), tm_mod(rm.instructions.len()))),
        c1 == 0 ==> tm_reaches_pos(rm_to_tm(rm),
            two_counter_config(c1, c2, entry(pc), tm_mod(rm.instructions.len())),
            two_counter_config(c1, c2, entry(t), tm_mod(rm.instructions.len()))),
{
    let tm = rm_to_tm(rm);
    let len = rm.instructions.len();
    let m = tm_mod(len);
    lemma_rm_to_tm_wf(rm);
    assert(tm.m == m && tm.n == 2);
    let e = entry(pc);
    assert(e + 16 == entry((pc + 1) as nat));
    assert(e < m && e + 1 < m && e + 2 < m && e + 4 < m) by(nonlinear_arith)
        requires e == 3 + 16 * pc, pc < len, m == 19 + 16 * len;

    // peek quintuples.
    lemma_quint_at(rm, pc, 0, 2);   // i_entry @ pc*48+2 : (e,2,2,e+1,L)
    lemma_quint_at(rm, pc, 1, 1);   // i_pos   @ pc*48+4 : (e+1,1,1,e+2,R)
    lemma_quint_at(rm, pc, 1, 0);   // i_zero  @ pc*48+3 : (e+1,0,0,entry(t),R)
    // dec quintuples.
    lemma_quint_at(rm, pc, 2, 2);   // d_sep   @ pc*48+8 : (e+2,2,2,e+2,L)
    lemma_quint_at(rm, pc, 2, 1);   // d_one_l @ pc*48+7 : (e+2,1,1,e+2,L)
    lemma_quint_at(rm, pc, 2, 0);   // d_turn  @ pc*48+6 : (e+2,0,0,e+3,R)
    lemma_quint_at(rm, pc, 3, 1);   // d_disc  @ pc*48+10: (e+3,1,0,e+4,R)
    lemma_quint_at(rm, pc, 4, 1);   // d_one_r @ pc*48+13: (e+4,1,1,e+4,R)
    // bounce quintuples.
    lemma_quint_at(rm, pc, 4, 2);   // b_b   @ pc*48+14 : (e+4,2,2,e+5,L)
    lemma_quint_at(rm, pc, 5, 1);   // b_one @ pc*48+16 : (e+5,1,1,e+16,R)
    lemma_quint_at(rm, pc, 5, 0);   // b_zero@ pc*48+15 : (e+5,0,0,e+16,R)

    let i_entry = (pc * 48 + 2) as int;
    let i_pos = (pc * 48 + 4) as int;
    let i_zero = (pc * 48 + 3) as int;
    let d_sep = (pc * 48 + 8) as int;
    let d_one_l = (pc * 48 + 7) as int;
    let d_turn = (pc * 48 + 6) as int;
    let d_disc = (pc * 48 + 10) as int;
    let d_one_r = (pc * 48 + 13) as int;
    let b_b = (pc * 48 + 14) as int;
    let b_one = (pc * 48 + 16) as int;
    let b_zero = (pc * 48 + 15) as int;

    assert(0 <= i_entry < tm.quints.len() && 0 <= i_pos < tm.quints.len() && 0 <= i_zero < tm.quints.len()
        && 0 <= d_sep < tm.quints.len() && 0 <= d_one_l < tm.quints.len() && 0 <= d_turn < tm.quints.len()
        && 0 <= d_disc < tm.quints.len() && 0 <= d_one_r < tm.quints.len()
        && 0 <= b_b < tm.quints.len() && 0 <= b_one < tm.quints.len() && 0 <= b_zero < tm.quints.len())
        by(nonlinear_arith)
        requires pc < len, tm.quints.len() == 48 * (len + 1),
            i_entry == pc*48+2, i_pos == pc*48+4, i_zero == pc*48+3,
            d_sep == pc*48+8, d_one_l == pc*48+7, d_turn == pc*48+6, d_disc == pc*48+10, d_one_r == pc*48+13,
            b_b == pc*48+14, b_one == pc*48+16, b_zero == pc*48+15;

    let cfg0 = two_counter_config(c1, c2, e, tm.m);
    lemma_peek_gadget(tm, c1, c2, e, e + 1, e + 2, entry(t), i_entry, i_pos, i_zero);

    if c1 > 0 {
        let cfg_pos = two_counter_config(c1, c2, e + 2, tm.m);
        assert(tm_run(tm, cfg0, 2) == cfg_pos);
        lemma_dec(tm, c1, c2, e + 2, e + 3, e + 4, d_sep, d_one_l, d_turn, d_disc, d_one_r);
        let cfg_dec = two_counter_config((c1 - 1) as nat, c2, e + 4, tm.m);
        assert(tm_run(tm, cfg_pos, (2 * c1 + 2) as nat) == cfg_dec);
        lemma_bounce_left(tm, (c1 - 1) as nat, c2, e + 4, e + 5, e + 16, b_b, b_one, b_zero);
        let cfg_fin = two_counter_config((c1 - 1) as nat, c2, e + 16, tm.m);
        assert(tm_run(tm, cfg_dec, 2) == cfg_fin);
        // chain 2 + (2c1+2) + 2 == 2c1+6.
        lemma_tm_run_split(tm, cfg0, 2, (2 * c1 + 2) as nat);
        assert(tm_run(tm, cfg0, (2 + (2 * c1 + 2)) as nat) == cfg_dec);
        lemma_tm_run_split(tm, cfg0, (2 + (2 * c1 + 2)) as nat, 2);
        assert((2 + (2 * c1 + 2) + 2) as nat == (2 * c1 + 6) as nat);
        assert(tm_run(tm, cfg0, (2 * c1 + 6) as nat) == cfg_fin);
        lemma_tm_reaches_intro(tm, cfg0, cfg_fin, (2 * c1 + 6) as nat);
        lemma_tm_reaches_pos_intro(tm, cfg0, cfg_fin, (2 * c1 + 6) as nat);
    }
    if c1 == 0 {
        let cfg_jmp = two_counter_config(c1, c2, entry(t), tm.m);
        assert(tm_run(tm, cfg0, 2) == cfg_jmp);
        lemma_tm_reaches_intro(tm, cfg0, cfg_jmp, 2);
        lemma_tm_reaches_pos_intro(tm, cfg0, cfg_jmp, 2);
    }
}

/// **DecJump on the right counter (register 1).** Mirror of `lemma_sim_decjump_left` (peek/dec/bounce
/// right).
pub proof fn lemma_sim_decjump_right(rm: RegisterMachine, pc: nat, t: nat, c1: nat, c2: nat)
    requires
        machine_wf(rm),
        pc < rm.instructions.len(),
        rm.instructions[pc as int] == mk_dj(1, t),
    ensures
        c2 > 0 ==> tm_reaches(rm_to_tm(rm),
            two_counter_config(c1, c2, entry(pc), tm_mod(rm.instructions.len())),
            two_counter_config(c1, (c2 - 1) as nat, entry((pc + 1) as nat), tm_mod(rm.instructions.len()))),
        c2 == 0 ==> tm_reaches(rm_to_tm(rm),
            two_counter_config(c1, c2, entry(pc), tm_mod(rm.instructions.len())),
            two_counter_config(c1, c2, entry(t), tm_mod(rm.instructions.len()))),
        c2 > 0 ==> tm_reaches_pos(rm_to_tm(rm),
            two_counter_config(c1, c2, entry(pc), tm_mod(rm.instructions.len())),
            two_counter_config(c1, (c2 - 1) as nat, entry((pc + 1) as nat), tm_mod(rm.instructions.len()))),
        c2 == 0 ==> tm_reaches_pos(rm_to_tm(rm),
            two_counter_config(c1, c2, entry(pc), tm_mod(rm.instructions.len())),
            two_counter_config(c1, c2, entry(t), tm_mod(rm.instructions.len()))),
{
    let tm = rm_to_tm(rm);
    let len = rm.instructions.len();
    let m = tm_mod(len);
    lemma_rm_to_tm_wf(rm);
    assert(tm.m == m && tm.n == 2);
    let e = entry(pc);
    assert(e + 16 == entry((pc + 1) as nat));
    assert(e < m && e + 1 < m && e + 2 < m && e + 4 < m) by(nonlinear_arith)
        requires e == 3 + 16 * pc, pc < len, m == 19 + 16 * len;

    lemma_quint_at(rm, pc, 0, 2);   // i_entry @ pc*48+2 : (e,2,2,e+1,R)
    lemma_quint_at(rm, pc, 1, 1);   // i_pos   @ pc*48+4 : (e+1,1,1,e+2,L)
    lemma_quint_at(rm, pc, 1, 0);   // i_zero  @ pc*48+3 : (e+1,0,0,entry(t),L)
    lemma_quint_at(rm, pc, 2, 2);   // d_sep   @ pc*48+8 : (e+2,2,2,e+2,R)
    lemma_quint_at(rm, pc, 2, 1);   // d_one_r @ pc*48+7 : (e+2,1,1,e+2,R)
    lemma_quint_at(rm, pc, 2, 0);   // d_turn  @ pc*48+6 : (e+2,0,0,e+3,L)
    lemma_quint_at(rm, pc, 3, 1);   // d_disc  @ pc*48+10: (e+3,1,0,e+4,L)
    lemma_quint_at(rm, pc, 4, 1);   // d_one_l @ pc*48+13: (e+4,1,1,e+4,L)
    lemma_quint_at(rm, pc, 4, 2);   // b_b   @ pc*48+14 : (e+4,2,2,e+5,R)
    lemma_quint_at(rm, pc, 5, 1);   // b_one @ pc*48+16 : (e+5,1,1,e+16,L)
    lemma_quint_at(rm, pc, 5, 0);   // b_zero@ pc*48+15 : (e+5,0,0,e+16,L)

    let i_entry = (pc * 48 + 2) as int;
    let i_pos = (pc * 48 + 4) as int;
    let i_zero = (pc * 48 + 3) as int;
    let d_sep = (pc * 48 + 8) as int;
    let d_one_r = (pc * 48 + 7) as int;
    let d_turn = (pc * 48 + 6) as int;
    let d_disc = (pc * 48 + 10) as int;
    let d_one_l = (pc * 48 + 13) as int;
    let b_b = (pc * 48 + 14) as int;
    let b_one = (pc * 48 + 16) as int;
    let b_zero = (pc * 48 + 15) as int;

    assert(0 <= i_entry < tm.quints.len() && 0 <= i_pos < tm.quints.len() && 0 <= i_zero < tm.quints.len()
        && 0 <= d_sep < tm.quints.len() && 0 <= d_one_r < tm.quints.len() && 0 <= d_turn < tm.quints.len()
        && 0 <= d_disc < tm.quints.len() && 0 <= d_one_l < tm.quints.len()
        && 0 <= b_b < tm.quints.len() && 0 <= b_one < tm.quints.len() && 0 <= b_zero < tm.quints.len())
        by(nonlinear_arith)
        requires pc < len, tm.quints.len() == 48 * (len + 1),
            i_entry == pc*48+2, i_pos == pc*48+4, i_zero == pc*48+3,
            d_sep == pc*48+8, d_one_r == pc*48+7, d_turn == pc*48+6, d_disc == pc*48+10, d_one_l == pc*48+13,
            b_b == pc*48+14, b_one == pc*48+16, b_zero == pc*48+15;

    let cfg0 = two_counter_config(c1, c2, e, tm.m);
    lemma_peek_right(tm, c1, c2, e, e + 1, e + 2, entry(t), i_entry, i_pos, i_zero);

    if c2 > 0 {
        let cfg_pos = two_counter_config(c1, c2, e + 2, tm.m);
        assert(tm_run(tm, cfg0, 2) == cfg_pos);
        lemma_dec_right(tm, c1, c2, e + 2, e + 3, e + 4, d_sep, d_one_r, d_turn, d_disc, d_one_l);
        let cfg_dec = two_counter_config(c1, (c2 - 1) as nat, e + 4, tm.m);
        assert(tm_run(tm, cfg_pos, (2 * c2 + 2) as nat) == cfg_dec);
        lemma_bounce_right(tm, c1, (c2 - 1) as nat, e + 4, e + 5, e + 16, b_b, b_one, b_zero);
        let cfg_fin = two_counter_config(c1, (c2 - 1) as nat, e + 16, tm.m);
        assert(tm_run(tm, cfg_dec, 2) == cfg_fin);
        lemma_tm_run_split(tm, cfg0, 2, (2 * c2 + 2) as nat);
        assert(tm_run(tm, cfg0, (2 + (2 * c2 + 2)) as nat) == cfg_dec);
        lemma_tm_run_split(tm, cfg0, (2 + (2 * c2 + 2)) as nat, 2);
        assert((2 + (2 * c2 + 2) + 2) as nat == (2 * c2 + 6) as nat);
        assert(tm_run(tm, cfg0, (2 * c2 + 6) as nat) == cfg_fin);
        lemma_tm_reaches_intro(tm, cfg0, cfg_fin, (2 * c2 + 6) as nat);
        lemma_tm_reaches_pos_intro(tm, cfg0, cfg_fin, (2 * c2 + 6) as nat);
        return;   // isolate the c2>0 postcondition check (the c2==0 implications are vacuous here)
    }
    // c2 == 0
    {
        let cfg_jmp = two_counter_config(c1, c2, entry(t), tm.m);
        assert(tm_run(tm, cfg0, 2) == cfg_jmp);
        lemma_tm_reaches_intro(tm, cfg0, cfg_jmp, 2);
        lemma_tm_reaches_pos_intro(tm, cfg0, cfg_jmp, 2);
    }
}

/// **A `Jump` instruction routes to its target.** From `two_counter_config(c1,c2,entry(pc))` the two
/// `jump_act` quintuples (a left bounce `entry(pc) → entry(target)`) leave the counters unchanged and
/// land the head on the separator in state `entry(target)`. The unconditional-jump analogue of
/// `lemma_sim_halt` (which bounces to the cleanup entry `entry(len)`); fuel = 2 ⟹ also `tm_reaches_pos`.
pub proof fn lemma_sim_jump(rm: RegisterMachine, pc: nat, target: nat, c1: nat, c2: nat)
    requires
        machine_wf(rm),
        pc < rm.instructions.len(),
        rm.instructions[pc as int] == mk_jump(target),
    ensures
        tm_reaches(rm_to_tm(rm),
            two_counter_config(c1, c2, entry(pc), tm_mod(rm.instructions.len())),
            two_counter_config(c1, c2, entry(target), tm_mod(rm.instructions.len()))),
        tm_reaches_pos(rm_to_tm(rm),
            two_counter_config(c1, c2, entry(pc), tm_mod(rm.instructions.len())),
            two_counter_config(c1, c2, entry(target), tm_mod(rm.instructions.len()))),
{
    let tm = rm_to_tm(rm);
    let len = rm.instructions.len();
    let m = tm_mod(len);
    lemma_rm_to_tm_wf(rm);
    assert(tm.m == m && tm.n == 2);
    assert(tm.quints.len() == 48 * (len + 1));
    let e = entry(pc);
    assert(e < m) by(nonlinear_arith) requires e == 3 + 16 * pc, pc < len, m == 19 + 16 * len;
    let etgt = entry(target);

    lemma_quint_at(rm, pc, 0, 2);   // (e,2,2,e+1,L)
    lemma_quint_at(rm, pc, 1, 1);   // (e+1,1,1,entry(target),R)
    lemma_quint_at(rm, pc, 1, 0);   // (e+1,0,0,entry(target),R)
    let i_b = (pc * 48 + 2) as int;
    let i_one = (pc * 48 + 4) as int;
    let i_zero = (pc * 48 + 3) as int;
    assert(0 <= i_b < tm.quints.len() && 0 <= i_one < tm.quints.len() && 0 <= i_zero < tm.quints.len())
        by(nonlinear_arith)
        requires pc < len, tm.quints.len() == 48 * (len + 1),
            i_b == pc*48+2, i_one == pc*48+4, i_zero == pc*48+3;

    let start = two_counter_config(c1, c2, e, tm.m);
    lemma_bounce_left(tm, c1, c2, e, e + 1, etgt, i_b, i_one, i_zero);
    let fin = two_counter_config(c1, c2, etgt, tm.m);
    assert(tm_run(tm, start, 2) == fin);
    lemma_tm_reaches_intro(tm, start, fin, 2);
    lemma_tm_reaches_pos_intro(tm, start, fin, 2);
}

// ─────────────────────────────────────────────────────────────────────────────
// The unified one-step simulation.
// ─────────────────────────────────────────────────────────────────────────────

/// **One 2-counter step ↔ one gadget run.** If the register machine `rm` (a 2-counter machine) takes
/// a non-halting step from `c` to `c' = step(rm,c)`, then the assembled TM `rm_to_tm(rm)` reaches the
/// encoded `c'` from the encoded `c`. Dispatches on the instruction at `c.pc` to the per-instruction
/// gadget simulations. The hook B6 chains along the whole 2-counter run (then cleanup → origin).
pub proof fn lemma_sim_step(rm: RegisterMachine, c: Configuration)
    requires
        machine_wf(rm),
        rm.num_regs == 2,
        config_wf(rm, c),
        step(rm, c) is Some,
    ensures
        tm_reaches(rm_to_tm(rm),
            two_counter_config(c.registers[0], c.registers[1], entry(c.pc), tm_mod(rm.instructions.len())),
            two_counter_config(step(rm, c).unwrap().registers[0], step(rm, c).unwrap().registers[1],
                entry(step(rm, c).unwrap().pc), tm_mod(rm.instructions.len()))),
        tm_reaches_pos(rm_to_tm(rm),
            two_counter_config(c.registers[0], c.registers[1], entry(c.pc), tm_mod(rm.instructions.len())),
            two_counter_config(step(rm, c).unwrap().registers[0], step(rm, c).unwrap().registers[1],
                entry(step(rm, c).unwrap().pc), tm_mod(rm.instructions.len()))),
{
    reveal(machine_wf);
    let len = rm.instructions.len();
    let pc = c.pc;
    let c1 = c.registers[0];
    let c2 = c.registers[1];
    let cprime = step(rm, c).unwrap();
    // step is Some ⟹ pc < len and the instruction is not Halt.
    assert(pc < len);
    assert(c.registers.len() == 2);   // config_wf
    let instr = rm.instructions[pc as int];
    match instr {
        Instruction::Inc { register } => {
            assert(register < 2);   // machine_wf + num_regs == 2
            // step: Some(pc+1, registers.update(register, registers[register]+1)).
            assert(cprime.pc == pc + 1);
            assert(cprime.registers == c.registers.update(register as int, (c.registers[register as int] + 1) as nat));
            if register == 0 {
                assert(rm.instructions[pc as int] == mk_inc(0));
                lemma_sim_inc_left(rm, pc, c1, c2);
                assert(cprime.registers[0] == c1 + 1);
                assert(cprime.registers[1] == c2);
            } else {
                assert(register == 1);
                assert(rm.instructions[pc as int] == mk_inc(1));
                lemma_sim_inc_right(rm, pc, c1, c2);
                assert(cprime.registers[0] == c1);
                assert(cprime.registers[1] == c2 + 1);
            }
            assert(cprime.pc == pc + 1);
        },
        Instruction::DecJump { register, target } => {
            assert(register < 2);
            if register == 0 {
                assert(rm.instructions[pc as int] == mk_dj(0, target));
                lemma_sim_decjump_left(rm, pc, target, c1, c2);
                if c1 > 0 {
                    assert(cprime.pc == pc + 1);
                    assert(cprime.registers == c.registers.update(0, (c1 - 1) as nat));
                    assert(cprime.registers[0] == c1 - 1);
                    assert(cprime.registers[1] == c2);
                } else {
                    assert(cprime.pc == target);
                    assert(cprime.registers == c.registers);
                    assert(cprime.registers[0] == c1 && cprime.registers[1] == c2);
                }
            } else {
                assert(register == 1);
                assert(rm.instructions[pc as int] == mk_dj(1, target));
                lemma_sim_decjump_right(rm, pc, target, c1, c2);
                if c2 > 0 {
                    assert(cprime.pc == pc + 1);
                    assert(cprime.registers == c.registers.update(1, (c2 - 1) as nat));
                    assert(cprime.registers[0] == c1);
                    assert(cprime.registers[1] == c2 - 1);
                } else {
                    assert(cprime.pc == target);
                    assert(cprime.registers == c.registers);
                    assert(cprime.registers[0] == c1 && cprime.registers[1] == c2);
                }
            }
        },
        Instruction::Jump { target } => {
            //  Unconditional jump: step → (target, registers unchanged); the gadget bounces
            //  entry(pc) → entry(target) leaving the counters intact.
            assert(rm.instructions[pc as int] == mk_jump(target));
            lemma_sim_jump(rm, pc, target, c1, c2);
            assert(cprime.pc == target);
            assert(cprime.registers == c.registers);
            assert(cprime.registers[0] == c1 && cprime.registers[1] == c2);
        },
        Instruction::Halt => {
            assert(step(rm, c) is None);   // contradicts step is Some
            assert(false);
        },
    }
}

} // verus!
