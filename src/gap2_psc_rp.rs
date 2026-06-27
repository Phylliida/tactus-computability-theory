//! # GAP-2 G2-F Route (i) brick R-P (assembly) — the copy-and-park `psc_act` window dispatch.
//!
//! Wires the abstract copy-and-park core ([`crate::tm_rp::lemma_rp_copy_park`]) onto the concrete
//! [`crate::tm_assemble4`] uniform-window scaffold. This is the first phase of the relator-decider TM
//! `psc_tm(e)`: it places the five handshake quintuples (start / deposit / walk) into windows of the
//! n=4 assembly and proves that, from the ignition output, the head parks `α`'s digit sequence reversed
//! in `v` (freeing `u` as workspace). It also **pins the ignition handoff state** `start(d0) = entry4(d0)`
//! (the abstract `start` parameter [`crate::gap2_ignition::ignition_quads`] left open) — so the modular
//! ignition step `(α,0) → (α/m, entry4(d0))` lands exactly on `rep1(c1)` for the reading config `c1`.
//!
//! ## Window layout (the full-`psc_tm` state allocation begins here)
//! Windows are the assemble4 blocks `[entry4(pc), entry4(pc)+16)`, `entry4(pc) = 5 + 16·pc`. R-P owns
//! windows `0..=4`:
//!   * **window 0 — the walk window.** `q_walk = entry4(0) = 5`. The four loop quintuples
//!     `(q_walk, s, s, q_walk, L)` (`s ∈ 1..4`) live at slots `(0, 0, s)`. The blank turnaround
//!     `(q_walk, 0)` at slot `(0,0,0)` is the **hand-off to the search phase** (placeholder `→ 0` here;
//!     the full machine retargets it to the R-S entry).
//!   * **windows 1..=4 — one per low digit `d0`.** `q_start(d0) = entry4(d0)`, `q_deposit(d0) =
//!     entry4(d0)+1`. The start quintuples `(q_start(d0), s, s, q_deposit(d0), R)` (`s ∈ 1..4`) at slots
//!     `(d0, 0, s)`; the deposit quintuple `(q_deposit(d0), 0, d0, q_walk, L)` at slot `(d0, 1, 0)`.
//!
//! Every other slot is an inert dummy (write the scanned symbol back, return to the window entry, move
//! L) — never reached, present only so the manifest layout is total and [`lemma_tm_wf_n4`] applies.
//!
//! `docs/gap2-input-loader-plan.md` §5 (R-P copy-and-park ASSEMBLY). Fully verified, no escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use crate::tm::{Tm, TmConfig, Quintuple, tm_wf, tm_run};
use crate::tm_gadget::mk_quint;
use crate::tm_assemble4::{entry4, tm_mod4, lemma_tm_wf_n4, lemma_slot_index, lemma_idx4_decomp};
use crate::tm_dstring::{dpack, dpile};
use crate::tm_rp::lemma_rp_copy_park;

verus! {

// ─────────────────────────────────────────────────────────────────────────────
// The ignition handoff state — pins the abstract `start` of `ignition_quads`.
// ─────────────────────────────────────────────────────────────────────────────

/// **The ignition handoff state for low digit `i`.** `start(i) = entry4(i)` = the entry state of the
/// digit-`i` window (= `q_start(i)`). The modular ignition step `(α,0) → (α/m, start(α%m))` thus lands
/// the machine in state `entry4(d0)` scanning `α`'s second digit `d1` — exactly `rep1(c1)` for
/// `c1 = {u: α/m², v: 0, a: d1, q: entry4(d0)}`. This is the concrete `start` the eventual R-MC feeds to
/// [`crate::gap2_ignition::ignition_quads`].
pub open spec fn rp_start(i: nat) -> nat { entry4(i) }

// ─────────────────────────────────────────────────────────────────────────────
// The R-P action table + generator.
// ─────────────────────────────────────────────────────────────────────────────

/// The R-P phase action table over windows `0..=4`: returns `(write, next_state, dir)` for the slot
/// `(pc, off, sym)`. See the module docs for the layout.
pub open spec fn rp_act(pc: nat, off: nat, sym: nat) -> (nat, nat, Dir) {
    if pc == 0 {
        // walk window: q_walk = entry4(0) = 5.
        if off == 0 && 1 <= sym && sym <= 4 {
            (sym, 5, Dir::L)              // (q_walk, s, s, q_walk, L)
        } else if off == 0 && sym == 0 {
            (0, 0, Dir::R)               // blank turnaround → search entry (placeholder: halt state 0)
        } else {
            (sym, 5, Dir::L)             // inert (stay at q_walk)
        }
    } else if 1 <= pc && pc <= 4 {
        // digit-pc window: q_start = entry4(pc), q_deposit = entry4(pc)+1.
        if off == 0 && 1 <= sym && sym <= 4 {
            (sym, entry4(pc) + 1, Dir::R)   // (q_start, s, s, q_deposit, R)
        } else if off == 1 && sym == 0 {
            (pc, 5, Dir::L)                 // (q_deposit, 0, d0=pc, q_walk, L)
        } else {
            (sym, entry4(pc), Dir::L)       // inert
        }
    } else {
        (sym, entry4(pc), Dir::L)           // other windows: inert
    }
}

/// The R-P generator: the manifest-keyed quintuple for flat index `idx` (q-key `entry4(pc)+off`,
/// scanned `sym`, action from [`rp_act`]).
pub open spec fn rp_gen(idx: nat) -> Quintuple {
    let pc = idx / 80;
    let off = (idx % 80) / 5;
    let sym = (idx % 80) % 5;
    let a = rp_act(pc, off, sym);
    mk_quint(entry4(pc) + off, sym, a.0, a.1, a.2)
}

/// The quintuple R-P places at slot `(pc, off, sym)` — the slot-indexed view of [`rp_gen`].
pub open spec fn rp_quint(pc: nat, off: nat, sym: nat) -> Quintuple {
    let a = rp_act(pc, off, sym);
    mk_quint(entry4(pc) + off, sym, a.0, a.1, a.2)
}

// ─────────────────────────────────────────────────────────────────────────────
// Boundedness of the action table (feeds lemma_tm_wf_n4).
// ─────────────────────────────────────────────────────────────────────────────

/// Every R-P action writes a real symbol (`≤ 4`) and targets an in-range state (`< tm_mod4(len)`),
/// for any window `pc ≤ len`. The per-quintuple boundedness hypothesis of [`lemma_tm_wf_n4`].
pub proof fn lemma_rp_act_bounded(pc: nat, off: nat, sym: nat, len: nat)
    requires
        pc <= len,
        sym <= 4,
    ensures
        rp_act(pc, off, sym).0 <= 4,
        rp_act(pc, off, sym).1 < tm_mod4(len),
{
    assert(entry4(pc) == 5 + 16 * pc);
    assert(tm_mod4(len) == 21 + 16 * len);
    assert(entry4(pc) + 1 < tm_mod4(len)) by(nonlinear_arith)
        requires pc <= len, entry4(pc) == 5 + 16 * pc, tm_mod4(len) == 21 + 16 * len;
    assert(entry4(pc) < tm_mod4(len)) by(nonlinear_arith)
        requires pc <= len, entry4(pc) == 5 + 16 * pc, tm_mod4(len) == 21 + 16 * len;
    assert(5 < tm_mod4(len)) by(nonlinear_arith) requires tm_mod4(len) == 21 + 16 * len;
    // rp_act's value is one of {5, 0, entry4(pc)+1, entry4(pc)} (all < tm_mod4(len)); write ∈ {sym,0,pc} ≤ 4.
}

// ─────────────────────────────────────────────────────────────────────────────
// The reusable R-P phase lemma (abstract over the full machine).
// ─────────────────────────────────────────────────────────────────────────────

/// **R-P phase (the copy-and-park splice).** Any well-formed n=4 assemble4 machine whose windows
/// `0..=4` carry the R-P action table (`tm.quints[i] == rp_gen(i)` for `i < 400`) parks `α`'s digit
/// sequence `[d0, d1] + tail` (all digits `1..4`): from the ignition reading config
/// `{u: dpack(tail), v: 0, a: d1, q: entry4(d0)}`, after `3 + tail.len()` steps the head is on the left
/// blank with `α` reversed in `v` and `u` freed:
/// `{u: 0, v: dpile(dpack([d0]), [d1] + tail), a: 0, q: q_walk = 5}`.
///
/// The hypothesis `tm.quints[i] == rp_gen(i)` for `i < 400` is exactly what a full-`psc_tm` dispatch
/// generator delivers (its first five windows are the R-P windows). This makes R-P a drop-in splice for
/// the eventual machine.
pub proof fn lemma_rp_phase(tm: Tm, len: nat, tail: Seq<nat>, d0: nat, d1: nat)
    requires
        tm_wf(tm),
        tm.n == 4,
        tm.m == tm_mod4(len),
        len >= 4,
        tm.quints.len() == 80 * (len + 1),
        forall|i: int| 0 <= i < 400 ==> #[trigger] tm.quints[i] == rp_gen(i as nat),
        1 <= d0 <= 4,
        1 <= d1 <= 4,
        forall|k: int| 0 <= k < tail.len() ==> 1 <= #[trigger] tail[k] <= 4,
    ensures
        tm_run(tm, TmConfig { u: dpack(tail, tm.m), v: 0, a: d1, q: entry4(d0) },
            (3 + tail.len()) as nat)
            == (TmConfig { u: 0, v: dpile(dpack(seq![d0], tm.m), seq![d1] + tail, tm.m), a: 0, q: 5 }),
{
    // total quint count ≥ 400 (len ≥ 4).
    assert(tm.quints.len() >= 400) by(nonlinear_arith) requires tm.quints.len() == 80 * (len + 1), len >= 4;

    // ── locate the four walk quintuples at slots (0, 0, s), index = s. ──
    let i_w1 = 1int; let i_w2 = 2int; let i_w3 = 3int; let i_w4 = 4int;
    assert(tm.quints[i_w1] == mk_quint(5, 1, 1, 5, Dir::L)) by {
        lemma_slot_index(0, 0, 1);
        assert(tm.quints[i_w1] == rp_gen(1));
    }
    assert(tm.quints[i_w2] == mk_quint(5, 2, 2, 5, Dir::L)) by {
        lemma_slot_index(0, 0, 2);
        assert(tm.quints[i_w2] == rp_gen(2));
    }
    assert(tm.quints[i_w3] == mk_quint(5, 3, 3, 5, Dir::L)) by {
        lemma_slot_index(0, 0, 3);
        assert(tm.quints[i_w3] == rp_gen(3));
    }
    assert(tm.quints[i_w4] == mk_quint(5, 4, 4, 5, Dir::L)) by {
        lemma_slot_index(0, 0, 4);
        assert(tm.quints[i_w4] == rp_gen(4));
    }

    // ── locate the four start quintuples at slots (d0, 0, s), index = d0*80 + s. ──
    let i_s1 = (d0 * 80 + 1) as int;
    let i_s2 = (d0 * 80 + 2) as int;
    let i_s3 = (d0 * 80 + 3) as int;
    let i_s4 = (d0 * 80 + 4) as int;
    assert(d0 * 80 + 4 < 400) by(nonlinear_arith) requires d0 <= 4;
    let qdep = (entry4(d0) + 1) as nat;
    assert(tm.quints[i_s1] == mk_quint(entry4(d0), 1, 1, qdep, Dir::R)) by {
        lemma_slot_index(d0, 0, 1);
        assert(tm.quints[i_s1] == rp_gen((d0 * 80 + 1) as nat));
    }
    assert(tm.quints[i_s2] == mk_quint(entry4(d0), 2, 2, qdep, Dir::R)) by {
        lemma_slot_index(d0, 0, 2);
        assert(tm.quints[i_s2] == rp_gen((d0 * 80 + 2) as nat));
    }
    assert(tm.quints[i_s3] == mk_quint(entry4(d0), 3, 3, qdep, Dir::R)) by {
        lemma_slot_index(d0, 0, 3);
        assert(tm.quints[i_s3] == rp_gen((d0 * 80 + 3) as nat));
    }
    assert(tm.quints[i_s4] == mk_quint(entry4(d0), 4, 4, qdep, Dir::R)) by {
        lemma_slot_index(d0, 0, 4);
        assert(tm.quints[i_s4] == rp_gen((d0 * 80 + 4) as nat));
    }

    // ── locate the deposit quintuple at slot (d0, 1, 0), index = d0*80 + 5. ──
    let i_dep = (d0 * 80 + 5) as int;
    assert(d0 * 80 + 5 < 400) by(nonlinear_arith) requires d0 <= 4;
    assert(tm.quints[i_dep] == mk_quint(qdep, 0, d0, 5, Dir::L)) by {
        lemma_slot_index(d0, 1, 0);
        assert(tm.quints[i_dep] == rp_gen((d0 * 80 + 5) as nat));
    }

    // ── all indices are in range. ──
    assert(0 <= i_w1 < tm.quints.len() && 0 <= i_w2 < tm.quints.len()
        && 0 <= i_w3 < tm.quints.len() && 0 <= i_w4 < tm.quints.len());
    assert(0 <= i_s1 < tm.quints.len() && 0 <= i_s2 < tm.quints.len()
        && 0 <= i_s3 < tm.quints.len() && 0 <= i_s4 < tm.quints.len());
    assert(0 <= i_dep < tm.quints.len());

    // ── invoke the copy-and-park core. q_start = entry4(d0), q_deposit = qdep, q_walk = 5. ──
    lemma_rp_copy_park(tm, tail, d0, d1, entry4(d0), qdep, 5,
        i_s1, i_s2, i_s3, i_s4, i_dep, i_w1, i_w2, i_w3, i_w4);
}

// ─────────────────────────────────────────────────────────────────────────────
// Concrete validation — a standalone R-P machine over the assemble4 scaffold.
// ─────────────────────────────────────────────────────────────────────────────

/// A concrete relator-decider read-phase TM with `len + 1` windows (`len ≥ 4`): windows `0..=4` are the
/// R-P copy-and-park windows, windows `5..=len` are inert. Validates that [`rp_act`] composes with the
/// assemble4 scaffold (non-vacuity for [`lemma_rp_phase`]).
pub open spec fn psc_rp_tm(len: nat) -> Tm {
    Tm { n: 4, m: tm_mod4(len), quints: Seq::new(80 * (len + 1), |idx: int| rp_gen(idx as nat)) }
}

/// The concrete R-P machine is well-formed (discharges the [`lemma_tm_wf_n4`] hypotheses for [`rp_gen`]).
pub proof fn lemma_psc_rp_wf(len: nat)
    ensures
        tm_wf(psc_rp_tm(len)),
{
    let tm = psc_rp_tm(len);
    assert(tm.quints.len() == 80 * (len + 1));
    assert forall|idx: int| #![trigger tm.quints[idx]] 0 <= idx < 80 * (len + 1) implies
        tm.quints[idx].q == entry4((idx as nat) / 80) + ((idx as nat) % 80) / 5
        && tm.quints[idx].a == ((idx as nat) % 80) % 5 by {
        assert(tm.quints[idx] == rp_gen(idx as nat));
    }
    assert forall|idx: int| #![trigger tm.quints[idx]] 0 <= idx < 80 * (len + 1) implies
        tm.quints[idx].a2 <= 4 && tm.quints[idx].q2 < tm.m by {
        assert(tm.quints[idx] == rp_gen(idx as nat));
        lemma_idx4_decomp(idx as nat, len);   // pc ≤ len, off < 16, sym ≤ 4
        lemma_rp_act_bounded((idx as nat) / 80, ((idx as nat) % 80) / 5, ((idx as nat) % 80) % 5, len);
    }
    lemma_tm_wf_n4(tm, len);
}

/// **Concrete R-P validation.** The standalone read-phase TM parks `α` exactly as [`lemma_rp_phase`]
/// promises — confirming the substrate ↔ copy-park-core composition end-to-end.
pub proof fn lemma_psc_rp_copy_park(len: nat, tail: Seq<nat>, d0: nat, d1: nat)
    requires
        len >= 4,
        1 <= d0 <= 4,
        1 <= d1 <= 4,
        forall|k: int| 0 <= k < tail.len() ==> 1 <= #[trigger] tail[k] <= 4,
    ensures
        tm_run(psc_rp_tm(len), TmConfig { u: dpack(tail, tm_mod4(len)), v: 0, a: d1, q: entry4(d0) },
            (3 + tail.len()) as nat)
            == (TmConfig { u: 0, v: dpile(dpack(seq![d0], tm_mod4(len)), seq![d1] + tail, tm_mod4(len)),
                a: 0, q: 5 }),
{
    let tm = psc_rp_tm(len);
    lemma_psc_rp_wf(len);
    assert(tm.m == tm_mod4(len));
    assert forall|i: int| 0 <= i < 400 implies #[trigger] tm.quints[i] == rp_gen(i as nat) by {
        assert(400 <= 80 * (len + 1)) by(nonlinear_arith) requires len >= 4;
    }
    lemma_rp_phase(tm, len, tail, d0, d1);
}

} // verus!
