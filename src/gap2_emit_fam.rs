//! # GAP-2 G2-F Route (i) — the R-relnum-gen STEP-2 CAPSTONE: emit the full `fam_digits(a,b)`.
//!
//! Chains the two emit phases across the master-swap into a single headline:
//! ```text
//!   lemma_uinv_phase_tail   (phase 1: emit uinv_digits(b), master b+1 at gap g,
//!                            a+1 backup carried as a high tail at offset h = g+b+2)
//!     ∘ lemma_q_clean       (wipe the b+1 master; the frame-shift leaves
//!                            u == R(a+1)·m^(g+b+2) == copy_u(0, a+1, g+b+2) — phase 2's input)
//!     ∘ lemma_u_phase       (phase 2: emit u_digits(a), master a+1 at gap g' = g+b+2)
//! ```
//! Net: starting from the init tape `u == m^g·R(b+1) + m^(g+b+2)·R(a+1)`, `v == 0`, head on the pivot in
//! `entry5(pc_uinv)`, after `uinv_phase_fuel + q_clean_fuel + u_phase_fuel` steps the output holds
//! `v == dpack(fam_digits(a,b), m) = dpack(uinv_digits(b) ++ u_digits(a), m)` — exactly `relnum(a,b)`'s
//! base-m digit block (`crate::gap2_fam_digits::lemma_dds_fam_relator` /
//! `crate::gap2_rho_unshift::lemma_relnum_is_decode_digit_seq`).
//!
//! The master-swap is the dissolved `load_master` frame-shift (`docs/gap2-input-loader-plan.md` §N+13.1):
//! `q_clean`'s output IS phase 2's input with the master `a+1` sitting at its own gap `g' = g+b+2`, so
//! phase 2 just runs with `g := g'`. Everything is **position-parametric** in `g` and the backup offset, so
//! this composition is independent of the Q4 search-bank layout — it is pure EMITTER content (model-B
//! home/shuttle, already decided).
//!
//! Like [`crate::gap2_psc_rp::lemma_rp_phase`] and the phase lemmas it composes, this is GENERIC over an
//! abstract `assemble5` machine carrying the required quintuples at given window/indices; the concrete
//! disjoint-zone `psc_tm` assembly (R-enum.3) supplies them. The splice is pure STATE IDENTIFICATION via
//! [`lemma_tm_run_split`] plus the two arithmetic bridges (`copy_u`↔`m^g·repunit`, `pow_nat` addition).
//!
//! Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use crate::tm::{Tm, TmConfig, tm_wf, tm_run};
use crate::tm_gadget::mk_quint;
use crate::tm_run_lemmas::lemma_tm_run_split;
use crate::tm_assemble5::{entry5, tm_mod5};
use crate::tm_dstring::{pow_nat, dpack, lemma_pow_nat_split, lemma_dpack_empty, lemma_dpack_pop};
use crate::tm_two_counter::repunit_m;
use crate::tm_copy_refresh::{copy_u, lemma_copy_u_start};
use crate::gap2_tail_lift::add_hi;
use crate::gap2_relnum_dds::{seq_pow, lemma_seq_pow_bound};
use crate::gap2_fam_digits::{uinv_digits, u_digits, fam_digits};
use crate::gap2_emit_seq::{uinv_phase_fuel, u_phase_fuel, lemma_uinv_phase_tail, lemma_u_phase, cat_bound};
use crate::gap2_master_mgmt::{q_clean_fuel, lemma_q_clean};
use crate::gap2_emit_window::{seret1x_gen, seret3x_gen};
use crate::gap2_emit_power::pbb1x_gen;
use crate::gap2_emit_power3::pbb3x_gen;

verus! {

// ─────────────────────────────────────────────────────────────────────────────
// Digit bounds for uinv_digits(b) — needed for u_phase's `od` precondition and
// q_clean's `1 <= v0 % m <= 4`.
// ─────────────────────────────────────────────────────────────────────────────

/// Every digit of `uinv_digits(b)` lies in `1..4`. (The 8 pieces are singletons over `{1,2,3,4}` and
/// `seq_pow` blocks over `{1}`, `{3}`, `{4,1,2}`, `{4,3,2}` — all in range; `cat_bound` chains them.)
pub proof fn lemma_uinv_digits_bound(b: nat)
    ensures
        forall|k: int| 0 <= k < uinv_digits(b).len() ==> 1 <= #[trigger] uinv_digits(b)[k] <= 4,
{
    let i = (b + 1) as nat;
    let p1 = seq![4nat];
    let p2 = seq_pow(seq![4nat, 1nat, 2nat], i);
    let p3 = seq![3nat];
    let p4 = seq_pow(seq![4nat, 3nat, 2nat], i);
    let p5 = seq![2nat];
    let p6 = seq_pow(seq![1nat], i);
    let p7 = seq![4nat, 1nat, 2nat];
    let p8 = seq_pow(seq![3nat], i);

    // per-piece bounds (the seq_pow blocks; bases are concrete digit seqs in 1..4)
    lemma_seq_pow_bound(seq![4nat, 1nat, 2nat], i, 1, 4);
    lemma_seq_pow_bound(seq![4nat, 3nat, 2nat], i, 1, 4);
    lemma_seq_pow_bound(seq![1nat], i, 1, 4);
    lemma_seq_pow_bound(seq![3nat], i, 1, 4);

    // chain left-associatively, matching uinv_digits's definition
    cat_bound(p1, p2);
    cat_bound(p1 + p2, p3);
    cat_bound(p1 + p2 + p3, p4);
    cat_bound(p1 + p2 + p3 + p4, p5);
    cat_bound(p1 + p2 + p3 + p4 + p5, p6);
    cat_bound(p1 + p2 + p3 + p4 + p5 + p6, p7);
    cat_bound(p1 + p2 + p3 + p4 + p5 + p6 + p7, p8);

    let whole = p1 + p2 + p3 + p4 + p5 + p6 + p7 + p8;
    assert(uinv_digits(b) =~= whole);
    assert forall|k: int| 0 <= k < uinv_digits(b).len() implies 1 <= #[trigger] uinv_digits(b)[k] <= 4 by {
        assert(uinv_digits(b)[k] == whole[k]);
    }
}

/// `uinv_digits(b)` is nonempty and its low digit is `4` (it starts with `[4]`). Gives q_clean its
/// `1 <= v0 % m <= 4` hypothesis when `v0 == dpack(uinv_digits(b), m)`.
pub proof fn lemma_uinv_digits_low(b: nat)
    ensures
        uinv_digits(b).len() >= 1,
        uinv_digits(b)[0] == 4,
{
    let i = (b + 1) as nat;
    let p1 = seq![4nat];
    let rest = seq_pow(seq![4nat, 1nat, 2nat], i)
        + seq![3nat]
        + seq_pow(seq![4nat, 3nat, 2nat], i)
        + seq![2nat]
        + seq_pow(seq![1nat], i)
        + seq![4nat, 1nat, 2nat]
        + seq_pow(seq![3nat], i);
    assert(uinv_digits(b) =~= p1 + rest);
    assert((p1 + rest)[0] == 4);
    assert((p1 + rest).len() >= 1);
}

// ─────────────────────────────────────────────────────────────────────────────
// The STEP-2 capstone.
// ─────────────────────────────────────────────────────────────────────────────

/// **R-relnum-gen STEP-2 capstone — emit `fam_digits(a,b)`.** From the init tape
/// `u == m^g·R(b+1) + m^(g+b+2)·R(a+1)`, `v == 0`, head on the pivot in `entry5(pc_uinv)`, the emitter
/// (uinv phase ∘ master-wipe ∘ u phase) produces `v == dpack(fam_digits(a,b), m)` and leaves the head on
/// the home pivot in `qfinal`, with the `a+1` master parked at gap `g+b+2`.
///
/// Generic over the abstract `assemble5` machine carrying the uinv windows `[pc_uinv, pc_uinv+8)`, the u
/// windows `[pc_u, pc_u+8)`, and the q_clean quintuples (`q_s = qend`, `q_w`, `q_r`, `q_home = entry5(pc_u)`)
/// at the named indices.
#[verifier::rlimit(8000)]
pub proof fn lemma_emit_fam_digits(
    tm: Tm, len: nat, a: nat, b: nat, g: nat,
    pc_uinv: nat, pc_u: nat,
    qend: nat, q_w: nat, q_r: nat, qfinal: nat,
    i_seek: int, i_trans: int, i_wipe: int, i_wr: int, i_seekr: int,
    i_sb1: int, i_sb2: int, i_sb3: int, i_sb4: int,
    kf1: int, kf2: int, kf3: int, kf4: int,
)
    requires
        tm_wf(tm),
        tm.n == 5,
        tm.m == tm_mod5(len),
        pc_uinv + 7 <= len,
        pc_u + 7 <= len,
        tm.quints.len() == 288 * (len + 1),
        g >= b + 3,
        g + b >= a + 1,
        // ── uinv-phase windows [pc_uinv, pc_uinv+8) (master b+1), exit qend ──
        forall|i: int| pc_uinv * 288 <= i < pc_uinv * 288 + 288 ==> #[trigger] tm.quints[i] == seret1x_gen(4, entry5(pc_uinv + 1), i as nat),
        forall|i: int| (pc_uinv + 1) * 288 <= i < (pc_uinv + 1) * 288 + 288 ==> #[trigger] tm.quints[i] == pbb3x_gen(4, 1, 2, entry5(pc_uinv + 2), i as nat),
        forall|i: int| (pc_uinv + 2) * 288 <= i < (pc_uinv + 2) * 288 + 288 ==> #[trigger] tm.quints[i] == seret1x_gen(3, entry5(pc_uinv + 3), i as nat),
        forall|i: int| (pc_uinv + 3) * 288 <= i < (pc_uinv + 3) * 288 + 288 ==> #[trigger] tm.quints[i] == pbb3x_gen(4, 3, 2, entry5(pc_uinv + 4), i as nat),
        forall|i: int| (pc_uinv + 4) * 288 <= i < (pc_uinv + 4) * 288 + 288 ==> #[trigger] tm.quints[i] == seret1x_gen(2, entry5(pc_uinv + 5), i as nat),
        forall|i: int| (pc_uinv + 5) * 288 <= i < (pc_uinv + 5) * 288 + 288 ==> #[trigger] tm.quints[i] == pbb1x_gen(1, entry5(pc_uinv + 6), i as nat),
        forall|i: int| (pc_uinv + 6) * 288 <= i < (pc_uinv + 6) * 288 + 288 ==> #[trigger] tm.quints[i] == seret3x_gen(4, 1, 2, entry5(pc_uinv + 7), i as nat),
        forall|i: int| (pc_uinv + 7) * 288 <= i < (pc_uinv + 7) * 288 + 288 ==> #[trigger] tm.quints[i] == pbb1x_gen(3, qend, i as nat),
        // ── q_clean quintuples (q_s = qend → q_w → q_r → q_home = entry5(pc_u)) ──
        0 <= i_seek < tm.quints.len(),
        0 <= i_trans < tm.quints.len(),
        0 <= i_wipe < tm.quints.len(),
        0 <= i_wr < tm.quints.len(),
        0 <= i_seekr < tm.quints.len(),
        0 <= i_sb1 < tm.quints.len(),
        0 <= i_sb2 < tm.quints.len(),
        0 <= i_sb3 < tm.quints.len(),
        0 <= i_sb4 < tm.quints.len(),
        tm.quints[i_seek] == mk_quint(qend, 0, 0, qend, Dir::L),
        tm.quints[i_trans] == mk_quint(qend, 1, 0, q_w, Dir::L),
        tm.quints[i_wipe] == mk_quint(q_w, 1, 0, q_w, Dir::L),
        tm.quints[i_wr] == mk_quint(q_w, 0, 0, q_r, Dir::R),
        tm.quints[i_seekr] == mk_quint(q_r, 0, 0, q_r, Dir::R),
        tm.quints[i_sb1] == mk_quint(q_r, 1, 1, entry5(pc_u), Dir::L),
        tm.quints[i_sb2] == mk_quint(q_r, 2, 2, entry5(pc_u), Dir::L),
        tm.quints[i_sb3] == mk_quint(q_r, 3, 3, entry5(pc_u), Dir::L),
        tm.quints[i_sb4] == mk_quint(q_r, 4, 4, entry5(pc_u), Dir::L),
        // ── u-phase windows [pc_u, pc_u+8) (master a+1), final qfinal ──
        forall|i: int| pc_u * 288 <= i < pc_u * 288 + 288 ==> #[trigger] tm.quints[i] == pbb1x_gen(1, entry5(pc_u + 1), i as nat),
        forall|i: int| (pc_u + 1) * 288 <= i < (pc_u + 1) * 288 + 288 ==> #[trigger] tm.quints[i] == seret3x_gen(4, 3, 2, entry5(pc_u + 2), i as nat),
        forall|i: int| (pc_u + 2) * 288 <= i < (pc_u + 2) * 288 + 288 ==> #[trigger] tm.quints[i] == pbb1x_gen(3, entry5(pc_u + 3), i as nat),
        forall|i: int| (pc_u + 3) * 288 <= i < (pc_u + 3) * 288 + 288 ==> #[trigger] tm.quints[i] == seret1x_gen(4, entry5(pc_u + 4), i as nat),
        forall|i: int| (pc_u + 4) * 288 <= i < (pc_u + 4) * 288 + 288 ==> #[trigger] tm.quints[i] == pbb3x_gen(4, 1, 2, entry5(pc_u + 5), i as nat),
        forall|i: int| (pc_u + 5) * 288 <= i < (pc_u + 5) * 288 + 288 ==> #[trigger] tm.quints[i] == seret1x_gen(1, entry5(pc_u + 6), i as nat),
        forall|i: int| (pc_u + 6) * 288 <= i < (pc_u + 6) * 288 + 288 ==> #[trigger] tm.quints[i] == pbb3x_gen(4, 3, 2, entry5(pc_u + 7), i as nat),
        forall|i: int| (pc_u + 7) * 288 <= i < (pc_u + 7) * 288 + 288 ==> #[trigger] tm.quints[i] == seret1x_gen(2, qfinal, i as nat),
        0 <= kf1 < tm.quints.len(),
        0 <= kf2 < tm.quints.len(),
        0 <= kf3 < tm.quints.len(),
        0 <= kf4 < tm.quints.len(),
        tm.quints[kf1] == mk_quint(qfinal, 1, 1, qfinal, Dir::L),
        tm.quints[kf2] == mk_quint(qfinal, 2, 2, qfinal, Dir::L),
        tm.quints[kf3] == mk_quint(qfinal, 3, 3, qfinal, Dir::L),
        tm.quints[kf4] == mk_quint(qfinal, 4, 4, qfinal, Dir::L),
    ensures
        tm_run(tm,
            TmConfig {
                u: (pow_nat(tm.m, g) * repunit_m((b + 1) as nat, tm.m)
                    + pow_nat(tm.m, (g + b + 2) as nat) * repunit_m((a + 1) as nat, tm.m)) as nat,
                v: 0, a: 0, q: entry5(pc_uinv) },
            (uinv_phase_fuel((b + 1) as nat, g, 0)
                + q_clean_fuel(g, (b + 1) as nat)
                + u_phase_fuel((a + 1) as nat, (g + b + 2) as nat, uinv_digits(b).len())) as nat)
            == (TmConfig {
                u: copy_u(0, (a + 1) as nat, (g + b + 2) as nat, tm.m),
                v: dpack(fam_digits(a, b), tm.m), a: 0, q: qfinal }),
{
    let m = tm.m;
    let i_b = (b + 1) as nat;
    let i_a = (a + 1) as nat;
    let t = repunit_m(i_a, m);
    let h = (g + i_b + 1) as nat;            // = g + b + 2 (the a+1 backup offset)
    let empt = Seq::<nat>::empty();

    let pg = pow_nat(m, g);
    let ph = pow_nat(m, h);
    let pib = pow_nat(m, (i_b + 1) as nat);
    let ru = repunit_m(i_b, m);

    assert(i_b >= 1);
    assert(i_a >= 1);
    assert((i_b - 1) as nat == b);
    assert((i_a - 1) as nat == a);
    assert(h == (g + b + 2) as nat);

    // digit bounds for uinv_digits(b)
    lemma_uinv_digits_bound(b);
    lemma_uinv_digits_low(b);

    // ── pow / copy_u arithmetic facts ──
    lemma_copy_u_start(i_b, g, m);                // copy_u(0,i_b,g,m) == pg*ru
    lemma_copy_u_start(i_a, h, m);                // copy_u(0,i_a,h,m) == ph*t
    lemma_pow_nat_split(m, g, (i_b + 1) as nat);  // pow_nat(m, g+(i_b+1)) == pg*pib
    assert((g + (i_b + 1)) as nat == h);
    assert(ph == pg * pib);

    // ────────────────────────────────────────────────────────────────────
    // Phase 1: uinv_phase_tail (od = empty) — emit uinv_digits(b).
    // ────────────────────────────────────────────────────────────────────
    lemma_dpack_empty(m);                         // dpack(empty, m) == 0
    assert(empt.len() == 0);
    lemma_uinv_phase_tail(tm, len, pc_uinv, i_b, g, empt, qend, t);
    let f1 = uinv_phase_fuel(i_b, g, 0);

    // c0 = uinv input (add_hi form); c1 = uinv output (add_hi form)
    let c0 = add_hi(TmConfig { u: copy_u(0, i_b, g, m), v: dpack(empt, m), a: 0, q: entry5(pc_uinv) }, h, t, m);
    let c1 = add_hi(TmConfig { u: copy_u(0, i_b, g, m), v: dpack(empt + uinv_digits((i_b - 1) as nat), m), a: 0, q: qend }, h, t, m);
    assert(tm_run(tm, c0, f1) == c1);

    // init (explicit form) == c0
    let init = TmConfig { u: (pg * ru + ph * t) as nat, v: 0, a: 0, q: entry5(pc_uinv) };
    assert(c0.u == (pg * ru + ph * t) as nat) by(nonlinear_arith)
        requires copy_u(0, i_b, g, m) == pg * ru, c0.u == (copy_u(0, i_b, g, m) + ph * t) as nat;
    assert(c0 == init);

    // ────────────────────────────────────────────────────────────────────
    // Bridge 1: c1 == q_clean input.
    // ────────────────────────────────────────────────────────────────────
    let v_uinv = dpack(uinv_digits(b), m);
    assert(empt + uinv_digits((i_b - 1) as nat) =~= uinv_digits(b));
    // q_clean wants 1 <= v0 % m <= 4 with v0 = dpack(uinv_digits(b), m)
    assert(m > 1);
    assert(uinv_digits(b)[0] == 4 && uinv_digits(b)[0] < m);
    lemma_dpack_pop(uinv_digits(b), m);           // dpack(uinv_digits(b),m) % m == uinv_digits(b)[0] == 4
    assert(1 <= v_uinv % m <= 4);

    let qc_in = TmConfig { u: (pg * (ru + pib * t)) as nat, v: v_uinv, a: 0, q: qend };
    assert(c1.u == (pg * (ru + pib * t)) as nat) by(nonlinear_arith)
        requires copy_u(0, i_b, g, m) == pg * ru, ph == pg * pib,
            c1.u == (copy_u(0, i_b, g, m) + ph * t) as nat;
    assert(c1 == qc_in);

    // ────────────────────────────────────────────────────────────────────
    // Phase 2: q_clean — wipe the b+1 master.
    // ────────────────────────────────────────────────────────────────────
    lemma_q_clean(tm, g, i_b, t, v_uinv, qend, q_w, q_r, entry5(pc_u),
        i_seek, i_trans, i_wipe, i_wr, i_seekr, i_sb1, i_sb2, i_sb3, i_sb4);
    let f2 = q_clean_fuel(g, i_b);
    // q_clean ensures: from {u: pg*(ru + m^(i_b+1)*t), v: v_uinv, a:0, q: qend}
    //   to {u: t * m^(g+i_b+1), v: v_uinv, a:0, q: entry5(pc_u)}
    let qc_out = TmConfig { u: (t * pow_nat(m, (g + i_b + 1) as nat)) as nat, v: v_uinv, a: 0, q: entry5(pc_u) };
    assert(tm_run(tm, qc_in, f2) == qc_out);

    // ────────────────────────────────────────────────────────────────────
    // Bridge 2: qc_out == u_phase input.
    // ────────────────────────────────────────────────────────────────────
    let up_in = TmConfig { u: copy_u(0, i_a, h, m), v: v_uinv, a: 0, q: entry5(pc_u) };
    assert((g + i_b + 1) as nat == h);
    assert(qc_out.u == copy_u(0, i_a, h, m)) by(nonlinear_arith)
        requires copy_u(0, i_a, h, m) == ph * t, qc_out.u == (t * ph) as nat;
    assert(qc_out == up_in);

    // ────────────────────────────────────────────────────────────────────
    // Phase 3: u_phase — emit u_digits(a).
    // ────────────────────────────────────────────────────────────────────
    lemma_u_phase(tm, len, pc_u, i_a, h, uinv_digits(b), qfinal, kf1, kf2, kf3, kf4);
    let f3 = u_phase_fuel(i_a, h, uinv_digits(b).len());
    let up_out = TmConfig {
        u: copy_u(0, i_a, h, m),
        v: dpack(uinv_digits(b) + u_digits((i_a - 1) as nat), m), a: 0, q: qfinal };
    assert(tm_run(tm, up_in, f3) == up_out);

    // up_out's output == dpack(fam_digits(a,b), m)
    assert(uinv_digits(b) + u_digits((i_a - 1) as nat) =~= fam_digits(a, b));
    let fin = TmConfig { u: copy_u(0, i_a, h, m), v: dpack(fam_digits(a, b), m), a: 0, q: qfinal };
    assert(up_out == fin);

    // ────────────────────────────────────────────────────────────────────
    // Chain the three runs via lemma_tm_run_split.
    // ────────────────────────────────────────────────────────────────────
    lemma_tm_run_split(tm, c0, f1, f2);           // run(c0, f1+f2) == run(run(c0,f1), f2) == run(qc_in, f2) == qc_out
    lemma_tm_run_split(tm, c0, (f1 + f2) as nat, f3);  // run(c0, f1+f2+f3) == run(qc_out, f3) == run(up_in, f3) == up_out

    let total = (f1 + f2 + f3) as nat;
    assert(((f1 + f2) as nat + f3) as nat == total);
    assert(tm_run(tm, c0, total) == fin);
    assert(tm_run(tm, init, total) == fin);
}

} // verus!
