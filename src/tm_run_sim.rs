//! # GAP-2-E brick B6 (part 2) — the full run simulation + the halting iff
//!
//! Chains the per-instruction one-step simulation (`tm_sim::lemma_sim_step`) along a whole 2-counter
//! run and bolts the cleanup (`tm_cleanup::lemma_cleanup`) onto the end, yielding the headline B6
//! correspondence:
//!
//! > a 2-counter register machine `R2` halts from a (well-formed) config `c`  **iff**  the assembled
//! > TM `rm_to_tm(R2)` reaches the origin config `(0,0,0,0)` from the encoded `c`.
//!
//! `rm_config_enc(rm, c) = two_counter_config(c.r0, c.r1, entry(c.pc))` is the layout encoding of a
//! register-machine config; G2-F will pick `config_encode` to be `rm_config_enc` of the input config.
//!
//! **Forward** (`lemma_rm_halts_implies_tm_origin`): induct over the run with `lemma_sim_step`
//! (transitivity of `tm_reaches`); at the halting config the cleanup drains both counters to the
//! origin (a `Halt` instruction first bounces into the cleanup window via `lemma_sim_halt`; a
//! fall-off-the-end halt *is* already the cleanup entry). Convert `tm_reaches … origin` to
//! `tm_halts_at` with `lemma_tm_run_reaches_halts_at` (origin is terminal).
//!
//! **Backward** (`lemma_tm_origin_implies_rm_halts`): induct on the TM fuel. If the register machine
//! has already halted we are done (no TM reasoning needed — the cleanup is irrelevant). Otherwise the
//! **positive-fuel** sim (`tm_reaches_pos`) advances `g ≥ 1` TM steps to `enc(step(c))`; since the
//! origin is terminal, `g ≤ f` (else the origin would equal `enc(step(c))`, whose state is `≥ 3`), so
//! the run-split peels `g` off the fuel and we recurse on the strictly smaller `f − g`.
//!
//! Fully verified, no verifier escape hatches. See `docs/gap2-register-to-tm-plan.md`.

use vstd::prelude::*;
use crate::machine::{RegisterMachine, Configuration, Instruction, machine_wf, config_wf, step,
    is_halted, run, run_halts, lemma_step_preserves_config_wf, lemma_halted_run_identity};
use crate::tm::{Tm, TmConfig, tm_run, tm_origin, tm_halts_at};
use crate::tm_two_counter::two_counter_config;
use crate::tm_sim::{tm_reaches, tm_reaches_pos, lemma_tm_reaches_intro, lemma_tm_reaches_trans,
    lemma_sim_step};
use crate::tm_cleanup::{lemma_cleanup, lemma_sim_halt};
use crate::tm_run_lemmas::{lemma_tm_run_split, lemma_tm_terminal_run_identity,
    lemma_tm_run_reaches_halts_at, lemma_tm_halts_at_run};
use crate::tm_h0_bwd::lemma_origin_tm_terminal;
use crate::tm_assemble::{entry, tm_mod, rm_to_tm, lemma_rm_to_tm_wf};

verus! {

/// The layout encoding of a register-machine config: the head on the separator, register 0 as the
/// left unary block, register 1 as the right unary block, the program counter as the entry state.
pub open spec fn rm_config_enc(rm: RegisterMachine, c: Configuration) -> TmConfig {
    two_counter_config(c.registers[0], c.registers[1], entry(c.pc), tm_mod(rm.instructions.len()))
}

// ─────────────────────────────────────────────────────────────────────────────
// Register-machine run bookkeeping.
// ─────────────────────────────────────────────────────────────────────────────

/// `run_halts` ⟹ the run lands on a halted config. (`run` idles once halted, so the witnessed halt
/// config is exactly `run(rm, c, F)`.)
pub proof fn lemma_run_halts_is_halted(rm: RegisterMachine, c: Configuration, f: nat)
    requires
        run_halts(rm, c, f),
    ensures
        is_halted(rm, run(rm, c, f)),
    decreases f,
{
    if f == 0 {
        // run_halts(c,0) == is_halted(c); run(c,0) == c.
    } else if is_halted(rm, c) {
        lemma_halted_run_identity(rm, c, f);
    } else {
        let next = step(rm, c).unwrap();
        assert(run_halts(rm, next, (f - 1) as nat));   // disjunction, not halted ⟹ Some-branch
        lemma_run_halts_is_halted(rm, next, (f - 1) as nat);
    }
}

/// A well-formed run preserves configuration well-formedness.
pub proof fn lemma_run_preserves_config_wf(rm: RegisterMachine, c: Configuration, f: nat)
    requires
        machine_wf(rm),
        config_wf(rm, c),
    ensures
        config_wf(rm, run(rm, c, f)),
    decreases f,
{
    if f == 0 {
    } else {
        match step(rm, c) {
            Some(next) => {
                lemma_step_preserves_config_wf(rm, c);
                lemma_run_preserves_config_wf(rm, next, (f - 1) as nat);
            },
            None => {},
        }
    }
}

/// **Classification of halting configs.** A well-formed config from which the machine cannot step
/// either has its program counter at the end (`pc == len`) or sits on a `Halt` instruction. (Inc/
/// DecJump on an in-range register always step, by `machine_wf` + `config_wf`.)
pub proof fn lemma_rm_terminal_cases(rm: RegisterMachine, c: Configuration)
    requires
        machine_wf(rm),
        config_wf(rm, c),
        step(rm, c) is None,
    ensures
        c.pc == rm.instructions.len()
            || (c.pc < rm.instructions.len() && rm.instructions[c.pc as int] == Instruction::Halt),
{
    reveal(machine_wf);
    let len = rm.instructions.len();
    if c.pc < len {
        match rm.instructions[c.pc as int] {
            Instruction::Halt => {},
            Instruction::Inc { register } => {
                assert(register < rm.num_regs);             // machine_wf
                assert(c.registers.len() == rm.num_regs);   // config_wf
                assert(register < c.registers.len());
                assert(step(rm, c) is Some);                // contradiction with the hypothesis
                assert(false);
            },
            Instruction::DecJump { register, target } => {
                assert(register < rm.num_regs);
                assert(register < c.registers.len());
                assert(step(rm, c) is Some);
                assert(false);
            },
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Forward: chain the simulation along the run, then cleanup → origin.
// ─────────────────────────────────────────────────────────────────────────────

/// **The run simulation.** If `R2` halts within `F` steps from `c`, the TM reaches the encoding of
/// the halted config `run(rm, c, F)` from `enc(c)`, by chaining `lemma_sim_step` (transitively) along
/// the non-halting prefix of the run.
pub proof fn lemma_sim_run(rm: RegisterMachine, c: Configuration, f: nat)
    requires
        machine_wf(rm),
        rm.num_regs == 2,
        config_wf(rm, c),
        run_halts(rm, c, f),
    ensures
        tm_reaches(rm_to_tm(rm), rm_config_enc(rm, c), rm_config_enc(rm, run(rm, c, f))),
    decreases f,
{
    let tm = rm_to_tm(rm);
    if f == 0 {
        assert(run(rm, c, 0) == c);
        assert(tm_run(tm, rm_config_enc(rm, c), 0) == rm_config_enc(rm, c));
        lemma_tm_reaches_intro(tm, rm_config_enc(rm, c), rm_config_enc(rm, c), 0);
    } else if is_halted(rm, c) {
        lemma_halted_run_identity(rm, c, f);   // run(c,f) == c
        assert(tm_run(tm, rm_config_enc(rm, c), 0) == rm_config_enc(rm, c));
        lemma_tm_reaches_intro(tm, rm_config_enc(rm, c), rm_config_enc(rm, c), 0);
    } else {
        let next = step(rm, c).unwrap();
        assert(step(rm, c) is Some);
        lemma_sim_step(rm, c);                          // tm_reaches(enc(c), enc(next))
        lemma_step_preserves_config_wf(rm, c);          // config_wf(next)
        assert(run_halts(rm, next, (f - 1) as nat));    // not halted ⟹ Some-branch
        lemma_sim_run(rm, next, (f - 1) as nat);        // tm_reaches(enc(next), enc(run(next,f-1)))
        assert(run(rm, c, f) == run(rm, next, (f - 1) as nat));
        lemma_tm_reaches_trans(tm, rm_config_enc(rm, c), rm_config_enc(rm, next),
            rm_config_enc(rm, run(rm, c, f)));
    }
}

/// **Forward halting correspondence.** If `R2` halts from a well-formed `c`, the TM reaches the origin
/// config from `enc(c)`.
pub proof fn lemma_rm_halts_implies_tm_origin(rm: RegisterMachine, c: Configuration)
    requires
        machine_wf(rm),
        rm.num_regs == 2,
        config_wf(rm, c),
        exists|f: nat| run_halts(rm, c, f),
    ensures
        exists|fuel: nat| tm_halts_at(rm_to_tm(rm), rm_config_enc(rm, c), tm_origin(), fuel),
{
    let tm = rm_to_tm(rm);
    let len = rm.instructions.len();
    let m = tm_mod(len);
    lemma_rm_to_tm_wf(rm);

    let f = choose|f: nat| run_halts(rm, c, f);
    let c_halt = run(rm, c, f);
    lemma_sim_run(rm, c, f);                    // tm_reaches(enc(c), enc(c_halt))
    lemma_run_halts_is_halted(rm, c, f);        // step(rm, c_halt) is None
    lemma_run_preserves_config_wf(rm, c, f);    // config_wf(c_halt)
    lemma_rm_terminal_cases(rm, c_halt);        // pc == len  OR  (pc < len ∧ Halt)

    let c1h = c_halt.registers[0];
    let c2h = c_halt.registers[1];
    let clean_entry = two_counter_config(c1h, c2h, entry(len), m);

    if c_halt.pc == len {
        assert(rm_config_enc(rm, c_halt) == clean_entry);   // entry(c_halt.pc) == entry(len)
        lemma_cleanup(rm, c1h, c2h);                        // tm_reaches(clean_entry, origin)
    } else {
        assert(c_halt.pc < len && rm.instructions[c_halt.pc as int] == Instruction::Halt);
        lemma_sim_halt(rm, c_halt.pc, c1h, c2h);            // tm_reaches(enc(c_halt), clean_entry)
        lemma_cleanup(rm, c1h, c2h);                        // tm_reaches(clean_entry, origin)
        lemma_tm_reaches_trans(tm, rm_config_enc(rm, c_halt), clean_entry, tm_origin());
    }
    // tm_reaches(enc(c_halt), origin) established in both arms.
    lemma_tm_reaches_trans(tm, rm_config_enc(rm, c), rm_config_enc(rm, c_halt), tm_origin());

    // Convert tm_reaches(enc(c), origin) into tm_halts_at via the terminal origin.
    let fuel = choose|fuel: nat| tm_run(tm, rm_config_enc(rm, c), fuel) == tm_origin();
    assert(tm_run(tm, rm_config_enc(rm, c), fuel) == tm_origin());
    lemma_origin_tm_terminal(tm);
    lemma_tm_run_reaches_halts_at(tm, rm_config_enc(rm, c), tm_origin(), fuel);
    assert(tm_halts_at(tm, rm_config_enc(rm, c), tm_origin(), fuel));
}

// ─────────────────────────────────────────────────────────────────────────────
// Backward: TM reaches origin ⟹ the register machine halts.
// ─────────────────────────────────────────────────────────────────────────────

/// **Backward halting correspondence.** If the TM reaches the origin from `enc(c)` within `f` steps,
/// `R2` halts from `c`. Induction on `f`: bottom out the instant `R2` is halted (the cleanup is then
/// irrelevant); otherwise peel `g ≥ 1` TM steps of the gadget simulating the next register step
/// (`g ≤ f` because the origin is terminal and `enc(step(c))` is not the origin), and recurse on
/// `f − g`.
pub proof fn lemma_tm_origin_implies_rm_halts(rm: RegisterMachine, c: Configuration, f: nat)
    requires
        machine_wf(rm),
        rm.num_regs == 2,
        config_wf(rm, c),
        tm_run(rm_to_tm(rm), rm_config_enc(rm, c), f) == tm_origin(),
    ensures
        exists|fc: nat| run_halts(rm, c, fc),
    decreases f,
{
    let tm = rm_to_tm(rm);
    lemma_rm_to_tm_wf(rm);

    if step(rm, c) is None {
        assert(is_halted(rm, c));
        assert(run_halts(rm, c, 0));
    } else {
        let next = step(rm, c).unwrap();
        lemma_step_preserves_config_wf(rm, c);
        lemma_sim_step(rm, c);                  // tm_reaches_pos(enc(c), enc(next))
        let a = rm_config_enc(rm, c);
        let b = rm_config_enc(rm, next);
        assert(tm_reaches_pos(tm, a, b));
        let g = choose|g: nat| 1 <= g && tm_run(tm, a, g) == b;
        assert(1 <= g && tm_run(tm, a, g) == b);

        lemma_origin_tm_terminal(tm);           // tm_terminal(tm, origin)

        // g ≤ f: otherwise origin (terminal, hence absorbing) would equal enc(next).
        if f < g {
            lemma_tm_run_split(tm, a, f, (g - f) as nat);   // tm_run(a, g) == tm_run(tm_run(a,f), g-f)
            assert((f + (g - f)) as nat == g);
            lemma_tm_terminal_run_identity(tm, tm_origin(), (g - f) as nat);
            assert(tm_run(tm, a, g) == tm_origin());
            assert(b == tm_origin());
            assert(b.q == entry(next.pc));          // two_counter_config's state field
            assert(entry(next.pc) >= 3);
            assert(tm_origin().q == 0);
            assert(false);
        }
        assert(g <= f);

        // Peel the gadget: tm_run(b, f-g) == tm_run(a, f) == origin.
        lemma_tm_run_split(tm, a, g, (f - g) as nat);
        assert((g + (f - g)) as nat == f);
        assert(tm_run(tm, b, (f - g) as nat) == tm_origin());

        lemma_tm_origin_implies_rm_halts(rm, next, (f - g) as nat);   // run_halts(next, F2)
        let f2 = choose|f2: nat| run_halts(rm, next, f2);
        assert(run_halts(rm, next, f2));
        assert(step(rm, c) == Some(next));
        assert(((f2 + 1) - 1) as nat == f2);
        assert(run_halts(rm, c, (f2 + 1) as nat));   // not halted, Some(next), run_halts(next, f2)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The B6 headline iff.
// ─────────────────────────────────────────────────────────────────────────────

/// **B6 — register-machine halting ⟺ the assembled TM reaches the origin.** For a well-formed
/// 2-counter machine and a well-formed config `c`, `R2` halts from `c` iff `rm_to_tm(R2)` reaches the
/// origin config `(0,0,0,0)` from `enc(c)`. Composing with `tm_h0::lemma_tm_h0_iff` (TM reaches origin
/// ⟺ `mm_in_H0`) gives `R2` halts ⟺ `mm_in_H0`, the machine content of `ceer_realizes` (G2-F wires the
/// initial-config encoding and discharges the remaining GAP-2 obligation).
pub proof fn lemma_rm_tm_origin_iff(rm: RegisterMachine, c: Configuration)
    requires
        machine_wf(rm),
        rm.num_regs == 2,
        config_wf(rm, c),
    ensures
        (exists|fc: nat| run_halts(rm, c, fc))
            <==> (exists|fuel: nat| tm_halts_at(rm_to_tm(rm), rm_config_enc(rm, c), tm_origin(), fuel)),
{
    let tm = rm_to_tm(rm);
    if exists|fc: nat| run_halts(rm, c, fc) {
        lemma_rm_halts_implies_tm_origin(rm, c);
    }
    if exists|fuel: nat| tm_halts_at(tm, rm_config_enc(rm, c), tm_origin(), fuel) {
        let fuel = choose|fuel: nat| tm_halts_at(tm, rm_config_enc(rm, c), tm_origin(), fuel);
        lemma_tm_halts_at_run(tm, rm_config_enc(rm, c), tm_origin(), fuel);   // tm_run(...) == origin
        lemma_tm_origin_implies_rm_halts(rm, c, fuel);
    }
}

} // verus!
