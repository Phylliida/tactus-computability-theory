//! # GAP-2 G2-F Route (i) brick R-AL — the n=4 uniform-window TM assembly scaffold.
//!
//! The substrate for `psc_tm(e)`, the relator-decider Turing machine. The machine works over alphabet
//! `0..4` (so the base-`m` word-number `α`'s digits `1..4` fit as tape symbols). It is the
//! alphabet-widened analog of [`crate::tm_assemble`] (the `n = 2` register-machine assembler): each
//! program position `pc ∈ [0, len]` owns a 16-state window `[entry4(pc), entry4(pc)+16)` with
//! `entry4(pc) = 5 + 16·pc`, and contributes exactly `80 = 16·5` quintuples — one per `(offset, sym)`
//! pair in `[0,16) × {0,1,2,3,4}`.
//!
//! ## First-order scaffold (no higher-order action tables)
//! A *phase* (read / generate / compare / dovetail / cleanup) builds its concrete TM by inlining its
//! own `Seq::new(80·(len+1), |idx| phase_gen(e, idx))`, where `phase_gen` puts each quintuple's q-key
//! at `entry4(pc)+off` and scanned at `sym` (the **manifest** layout). Two facts then suffice for
//! well-formedness, *independent of the action contents*:
//!   * `lemma_tm_wf_n4` — `tm_wf(tm)` from the manifest-key hypothesis (`q = entry4(pc)+off`,
//!     `a = sym`) plus per-quintuple boundedness (`a2 ≤ 4`, `q2 < m`). Determinism falls out of the
//!     manifest keys by mixed-radix index recovery ([`lemma_idx4_recover`]); it never inspects actions.
//!   * `lemma_slot_index` — the flat index `pc·80 + off·5 + sym` decodes back to `(pc, off, sym)`,
//!     so a phase can discharge the `tm.quints[i] == mk_quint(..)` precondition of a counter gadget.
//!
//! The counter gadget step-lemmas (`lemma_inc`/`lemma_dec`/`lemma_peek_gadget`/…, all requiring only
//! `tm.n >= 2`, never `n == 2`) therefore fire verbatim on any phase TM. [`lemma_assemble4_peek_demo`]
//! exercises the whole path end-to-end as a template.
//!
//! `docs/gap2-input-loader-plan.md` §5 (R-AL). Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse};
use verus_group_theory::machine_group::Dir;
use crate::tm::{Tm, Quintuple, tm_wf, quint_wf, tm_run};
use crate::tm_gadget::{mk_quint, lemma_peek_gadget};
use crate::tm_two_counter::{two_counter_config, sep};

verus! {

// ─────────────────────────────────────────────────────────────────────────────
// Layout.  n = 4 (alphabet 0,1,2,3,4).  STRIDE = 16 states per window.
// 80 = 16·5 quintuples per window.  entry4(pc) = 5 + 16·pc.
// ─────────────────────────────────────────────────────────────────────────────

/// First state of program position `pc`'s window (states are `≥ n+1 = 5`).
pub open spec fn entry4(pc: nat) -> nat { 5 + 16 * pc }

/// The TM modulus: one window past the last position, so every used state is `< m`.
/// `tm_mod4(len) = entry4(len) + 16 = 21 + 16·len`.
pub open spec fn tm_mod4(len: nat) -> nat { 21 + 16 * len }

// ─────────────────────────────────────────────────────────────────────────────
// Index arithmetic helpers (pure; reusable by every phase).
// ─────────────────────────────────────────────────────────────────────────────

/// For a valid flat index, `pc = idx/80 ≤ len`, `off = (idx%80)/5 < 16`, `sym = (idx%80)%5 ≤ 4`.
pub proof fn lemma_idx4_decomp(idx: nat, len: nat)
    requires
        idx < 80 * (len + 1),
    ensures
        idx / 80 <= len,
        (idx % 80) / 5 < 16,
        (idx % 80) % 5 <= 4,
{
    lemma_fundamental_div_mod(idx as int, 80);
    assert(idx / 80 <= len) by(nonlinear_arith)
        requires idx < 80 * (len + 1), idx == 80 * (idx / 80) + idx % 80, 0 <= idx % 80 < 80;
    lemma_fundamental_div_mod((idx % 80) as int, 5);
    assert((idx % 80) / 5 < 16) by(nonlinear_arith)
        requires idx % 80 < 80, (idx % 80) == 5 * ((idx % 80) / 5) + (idx % 80) % 5, 0 <= (idx % 80) % 5 < 5;
    assert((idx % 80) % 5 <= 4);
}

/// **Slot → index decode.** The `(pc, off, sym)` slot's flat index `pc·80 + off·5 + sym` recovers
/// `pc`, `off`, `sym` under div/mod (stride 16 > max offset 15; 5 symbols per offset). The hook a phase
/// uses to locate a gadget quintuple it placed at `(pc, off, sym)`.
pub proof fn lemma_slot_index(pc: nat, off: nat, sym: nat)
    requires
        off < 16,
        sym <= 4,
    ensures
        (pc * 80 + off * 5 + sym) / 80 == pc,
        ((pc * 80 + off * 5 + sym) % 80) / 5 == off,
        ((pc * 80 + off * 5 + sym) % 80) % 5 == sym,
{
    let idx = pc * 80 + off * 5 + sym;
    let rem = off * 5 + sym;
    assert(rem < 80) by(nonlinear_arith) requires off < 16, sym <= 4, rem == off * 5 + sym;
    lemma_fundamental_div_mod_converse(idx as int, 80, pc as int, rem as int);
    lemma_fundamental_div_mod_converse(rem as int, 5, off as int, sym as int);
}

/// **Index recovery.** If two flat indices give quintuples with equal manifest `(q, a)` then the
/// indices are equal. From `entry4(i/80)+(i%80)/5 == entry4(j/80)+(j%80)/5` (stride 16 > max offset 15)
/// the window `i/80` and offset `(i%80)/5` match; with equal scanned `(i%80)%5` the residue `i%80`
/// matches, hence `i == j`. The core of the determinism proof.
pub proof fn lemma_idx4_recover(i: nat, j: nat)
    requires
        entry4(i / 80) + (i % 80) / 5 == entry4(j / 80) + (j % 80) / 5,
        (i % 80) % 5 == (j % 80) % 5,
    ensures
        i == j,
{
    let pi = i / 80; let oi = (i % 80) / 5; let si = (i % 80) % 5;
    let pj = j / 80; let oj = (j % 80) / 5; let sj = (j % 80) % 5;
    // offsets are < 16.
    lemma_fundamental_div_mod((i % 80) as int, 5);
    lemma_fundamental_div_mod((j % 80) as int, 5);
    assert(oi < 16) by(nonlinear_arith)
        requires i % 80 < 80, (i % 80) == 5 * oi + si, 0 <= si < 5;
    assert(oj < 16) by(nonlinear_arith)
        requires j % 80 < 80, (j % 80) == 5 * oj + sj, 0 <= sj < 5;
    // entry4(pi)+oi == entry4(pj)+oj ⟹ 16·pi+oi == 16·pj+oj ⟹ pi==pj ∧ oi==oj (oi,oj < 16).
    assert(16 * pi + oi == 16 * pj + oj) by(nonlinear_arith)
        requires entry4(pi) + oi == entry4(pj) + oj, entry4(pi) == 5 + 16 * pi, entry4(pj) == 5 + 16 * pj;
    lemma_fundamental_div_mod_converse((16 * pi + oi) as int, 16, pi as int, oi as int);
    lemma_fundamental_div_mod_converse((16 * pj + oj) as int, 16, pj as int, oj as int);
    assert(pi == pj && oi == oj);
    // i%80 == 5·oi+si == 5·oj+sj == j%80; and i/80 == j/80; so i == j.
    assert(i % 80 == j % 80) by(nonlinear_arith)
        requires (i % 80) == 5 * oi + si, (j % 80) == 5 * oj + sj, oi == oj, si == sj;
    lemma_fundamental_div_mod(i as int, 80);
    lemma_fundamental_div_mod(j as int, 80);
    assert(i == j) by(nonlinear_arith)
        requires i == 80 * (i / 80) + i % 80, j == 80 * (j / 80) + j % 80, pi == pj, i % 80 == j % 80,
            pi == i / 80, pj == j / 80;
}

// ─────────────────────────────────────────────────────────────────────────────
// Generic well-formedness from the manifest layout (action-content-independent).
// ─────────────────────────────────────────────────────────────────────────────

/// **`tm` is a well-formed (deterministic) n=4 TM** given the uniform window dimensions, the manifest
/// key/scanned layout (`q = entry4(pc)+off`, `a = sym`), and per-quintuple boundedness (`a2 ≤ 4`,
/// `q2 < m`). `quint_wf` per quintuple from the manifest state/scanned + boundedness; determinism by
/// recovering the flat index from `(q, a)` ([`lemma_idx4_recover`]). A phase discharges the manifest
/// hypotheses by unfolding its own `Seq::new` generator — no higher-order action table is involved.
pub proof fn lemma_tm_wf_n4(tm: Tm, len: nat)
    requires
        tm.n == 4,
        tm.m == tm_mod4(len),
        tm.quints.len() == 80 * (len + 1),
        forall|idx: int| #![trigger tm.quints[idx]] 0 <= idx < 80 * (len + 1) ==>
            tm.quints[idx].q == entry4((idx as nat) / 80) + ((idx as nat) % 80) / 5
            && tm.quints[idx].a == ((idx as nat) % 80) % 5,
        forall|idx: int| #![trigger tm.quints[idx]] 0 <= idx < 80 * (len + 1) ==>
            tm.quints[idx].a2 <= 4 && tm.quints[idx].q2 < tm.m,
    ensures
        tm_wf(tm),
{
    reveal(tm_wf);
    let m = tm.m;
    let total = 80 * (len + 1);
    assert(m > 1) by(nonlinear_arith) requires m == 21 + 16 * len;
    assert(0 < tm.n < tm.m) by(nonlinear_arith) requires tm.n == 4, m == 21 + 16 * len, tm.m == m;

    // quint_wf for every quintuple.
    assert forall|i: int| #![trigger tm.quints[i]] 0 <= i < total implies quint_wf(tm.quints[i], 4, m) by {
        let ii = i as nat;
        lemma_idx4_decomp(ii, len);
        let pc = ii / 80;
        let off = (ii % 80) / 5;
        let sym = (ii % 80) % 5;
        // manifest: q = entry4(pc)+off ∈ [5, m), a = sym ≤ 4.
        assert(tm.quints[i].q == entry4(pc) + off);
        assert(tm.quints[i].a == sym);
        assert(entry4(pc) + off >= 5);
        assert(entry4(pc) + off < m) by(nonlinear_arith)
            requires entry4(pc) == 5 + 16 * pc, pc <= len, off < 16, m == 21 + 16 * len;
        // a2 ≤ 4 and q2 < m from the boundedness hypothesis.
    }

    // determinism: equal manifest (q,a) ⟹ equal index.
    assert forall|i: int, j: int|
        0 <= i < total && 0 <= j < total
        && #[trigger] tm.quints[i].q == #[trigger] tm.quints[j].q
        && tm.quints[i].a == tm.quints[j].a
        implies i == j
    by {
        let ii = i as nat;
        let jj = j as nat;
        // manifest keys connect .q/.a to the index arithmetic.
        assert(tm.quints[i].q == entry4(ii / 80) + (ii % 80) / 5);
        assert(tm.quints[j].q == entry4(jj / 80) + (jj % 80) / 5);
        assert(tm.quints[i].a == (ii % 80) % 5);
        assert(tm.quints[j].a == (jj % 80) % 5);
        lemma_idx4_recover(ii, jj);
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Interface validation — a counter gadget fires on a concrete n=4 phase TM.
//
// This template exercises the whole path every phase will use: a concrete generator → `lemma_tm_wf_n4`
// (tm_wf) → `lemma_slot_index` (locate the gadget quintuples) → a `tm.n >= 2`-monotone gadget lemma
// (here the bounded zero-test/peek). It confirms the substrate composes with the existing counter
// gadget library at `n = 4`.
// ─────────────────────────────────────────────────────────────────────────────

/// A one-window demo action table placing the peek gadget at window `pc = 0`: entry state `5`
/// (`off 0`), branch state `6` (`off 1`), exits `q_pos = 7` / `q_zero = 8`. Every other slot is an
/// inert dummy (write the scanned symbol back, stay in the window) — bounded for `len = 0` (`m = 21`).
pub open spec fn peek_demo_act(off: nat, sym: nat) -> (nat, nat, Dir) {
    if off == 0 && sym == 2 { (2, 6, Dir::L) }       // (q_entry=5, 2, 2, q_branch=6, L)
    else if off == 1 && sym == 1 { (1, 7, Dir::R) }  // (q_branch=6, 1, 1, q_pos=7, R)
    else if off == 1 && sym == 0 { (0, 8, Dir::R) }  // (q_branch=6, 0, 0, q_zero=8, R)
    else { (sym, 5, Dir::L) }                         // inert dummy (write sym back, stay at entry4(0)=5)
}

/// The demo generator: one window (`pc = 0`), manifest key/scanned, actions from `peek_demo_act`.
pub open spec fn peek_demo_gen(idx: nat) -> Quintuple {
    let off = (idx % 80) / 5;
    let sym = (idx % 80) % 5;
    let a = peek_demo_act(off, sym);
    mk_quint(entry4(idx / 80) + off, sym, a.0, a.1, a.2)
}

/// The demo TM: a single 80-quintuple window (`len = 0`, `m = 21`).
pub open spec fn peek_demo_tm() -> Tm {
    Tm { n: 4, m: tm_mod4(0), quints: Seq::new(80, |idx: int| peek_demo_gen(idx as nat)) }
}

/// The demo TM is well-formed (discharges the `lemma_tm_wf_n4` hypotheses for its generator).
pub proof fn lemma_peek_demo_wf()
    ensures
        tm_wf(peek_demo_tm()),
{
    let tm = peek_demo_tm();
    assert(tm.quints.len() == 80);
    assert forall|idx: int| #![trigger tm.quints[idx]] 0 <= idx < 80 implies
        tm.quints[idx].q == entry4((idx as nat) / 80) + ((idx as nat) % 80) / 5
        && tm.quints[idx].a == ((idx as nat) % 80) % 5 by {
        assert(tm.quints[idx] == peek_demo_gen(idx as nat));
    }
    assert forall|idx: int| #![trigger tm.quints[idx]] 0 <= idx < 80 implies
        tm.quints[idx].a2 <= 4 && tm.quints[idx].q2 < tm.m by {
        assert(tm.quints[idx] == peek_demo_gen(idx as nat));
        lemma_idx4_decomp(idx as nat, 0);   // pc = 0, off < 16, sym ≤ 4
        // peek_demo_act(off, sym): a2 ∈ {2,1,0,sym} ≤ 4; q2 ∈ {6,7,8,5} < 21.
    }
    lemma_tm_wf_n4(tm, 0);
}

/// **Validation.** The peek gadget fires on `peek_demo_tm()`: from the head-on-separator layout in
/// entry state `5`, two steps branch to `q_pos = 7` (counter `> 0`) or `q_zero = 8` (counter `= 0`),
/// the counters unchanged. Demonstrates the substrate ↔ gadget-library composition end-to-end.
pub proof fn lemma_assemble4_peek_demo(c1: nat, c2: nat)
    ensures
        c1 > 0 ==> tm_run(peek_demo_tm(), two_counter_config(c1, c2, 5, 21), 2)
            == two_counter_config(c1, c2, 7, 21),
        c1 == 0 ==> tm_run(peek_demo_tm(), two_counter_config(c1, c2, 5, 21), 2)
            == two_counter_config(c1, c2, 8, 21),
{
    let tm = peek_demo_tm();
    lemma_peek_demo_wf();
    assert(tm.n == 4 && tm.m == 21);
    assert(sep() == 2);
    // Locate the three peek quintuples at slots (0,0,2), (0,1,1), (0,1,0).
    lemma_slot_index(0, 0, 2);
    lemma_slot_index(0, 1, 1);
    lemma_slot_index(0, 1, 0);
    let i_entry = (0 * 80 + 0 * 5 + 2) as int;   // = 2
    let i_pos = (0 * 80 + 1 * 5 + 1) as int;     // = 6
    let i_zero = (0 * 80 + 1 * 5 + 0) as int;    // = 5
    assert(0 <= i_entry < 80 && 0 <= i_pos < 80 && 0 <= i_zero < 80);
    assert(tm.quints[i_entry] == peek_demo_gen(i_entry as nat));
    assert(tm.quints[i_pos] == peek_demo_gen(i_pos as nat));
    assert(tm.quints[i_zero] == peek_demo_gen(i_zero as nat));
    // peek_demo_gen at these slots = the gadget quintuples (entry4(0)+0=5, entry4(0)+1=6).
    assert(tm.quints[i_entry] == mk_quint(5, 2, 2, 6, Dir::L));
    assert(tm.quints[i_pos] == mk_quint(6, 1, 1, 7, Dir::R));
    assert(tm.quints[i_zero] == mk_quint(6, 0, 0, 8, Dir::R));
    lemma_peek_gadget(tm, c1, c2, 5, 6, 7, 8, i_entry, i_pos, i_zero);
}

} // verus!
