//! # GAP-2 brick G2-B — the TM → modular-machine construction (Aanderaa–Cohen Thm 2)
//!
//! Each TM quintuple `q a a2 q2 D` becomes **two** modular quadruples `(a, q, a2·m+q2, D)` and
//! `(q, a, a2·m+q2, D)` (paper p.4). Symbols (`≤ n`) and states (`≥ n+1`) are disjoint, so a first
//! quad `(a,q)` (low,high residues) and a second quad `(q',a')` (high,low) never collide; together
//! with the TM's determinism (≤1 quintuple per `(q,a)`) this makes the modular machine deterministic
//! (`mod_machine_wf`).  See `docs/gap2-register-modular-plan.md`.

use vstd::prelude::*;
use verus_group_theory::machine_group::{ModMachine, Quad, Dir, quad_wf, mod_machine_wf,
    quad_matches, quad_step, mm_yields};
use verus_group_theory::word_numbering::lemma_div_mod_step;
use crate::tm::{Tm, Quintuple, TmConfig, tm_wf, quint_wf, tm_terminal, matching_index, apply_quint,
    quint_matches, lemma_matching_index_ok, lemma_nonterminal_residues};

verus! {

/// First modular quadruple of a quintuple: residues `(scanned, state)`.
pub open spec fn quint_first(qt: Quintuple, m: nat) -> Quad {
    Quad { a: qt.a, b: qt.q, c: qt.a2 * m + qt.q2, dir: qt.dir }
}

/// Second modular quadruple of a quintuple: residues `(state, scanned)`.
pub open spec fn quint_second(qt: Quintuple, m: nat) -> Quad {
    Quad { a: qt.q, b: qt.a, c: qt.a2 * m + qt.q2, dir: qt.dir }
}

/// The two quadruples a quintuple contributes.
pub open spec fn quint_to_quads(qt: Quintuple, m: nat) -> Seq<Quad> {
    seq![quint_first(qt, m), quint_second(qt, m)]
}

/// Flatten the per-quintuple quadruple pairs into the modular machine's quad list.
pub open spec fn quads_of(quints: Seq<Quintuple>, m: nat) -> Seq<Quad>
    decreases quints.len(),
{
    if quints.len() == 0 {
        Seq::empty()
    } else {
        quint_to_quads(quints[0], m) + quads_of(quints.drop_first(), m)
    }
}

/// The modular machine simulating TM `tm`.
pub open spec fn tm_to_modmachine(tm: Tm) -> ModMachine {
    ModMachine { m: tm.m, n: tm.n, quads: quads_of(tm.quints, tm.m) }
}

// ─────────────────────────────────────────────────────────────────────────────
// Indexing: quad `2p` is the first quad of quintuple `p`, quad `2p+1` the second.
// ─────────────────────────────────────────────────────────────────────────────

/// `quads_of` has length `2·#quints`, and index `2p`/`2p+1` is the first/second quad of quintuple `p`.
pub proof fn lemma_quads_of(quints: Seq<Quintuple>, m: nat)
    ensures
        quads_of(quints, m).len() == 2 * quints.len(),
        forall|p: int| #![trigger quints[p]] 0 <= p < quints.len() ==>
            quads_of(quints, m)[2 * p] == quint_first(quints[p], m)
            && quads_of(quints, m)[2 * p + 1] == quint_second(quints[p], m),
    decreases quints.len(),
{
    if quints.len() == 0 {
    } else {
        let head = quint_to_quads(quints[0], m);
        let tail = quads_of(quints.drop_first(), m);
        lemma_quads_of(quints.drop_first(), m);
        assert(quads_of(quints, m) =~= head + tail);
        assert(head.len() == 2);
        assert(quads_of(quints, m).len() == 2 * quints.len());
        assert forall|p: int| #![trigger quints[p]] 0 <= p < quints.len() implies
            quads_of(quints, m)[2 * p] == quint_first(quints[p], m)
            && quads_of(quints, m)[2 * p + 1] == quint_second(quints[p], m)
        by {
            if p == 0 {
                assert(quads_of(quints, m)[0] == head[0]);
                assert(quads_of(quints, m)[1] == head[1]);
            } else {
                // index lands in the tail: 2p, 2p+1 ≥ 2, subtract head.len()==2.
                assert(quads_of(quints, m)[2 * p] == tail[2 * p - 2]);
                assert(quads_of(quints, m)[2 * p + 1] == tail[2 * p - 1]);
                assert(quints[p] == quints.drop_first()[p - 1]);
                assert(tail[2 * (p - 1)] == quint_first(quints.drop_first()[p - 1], m));
                assert(tail[2 * (p - 1) + 1] == quint_second(quints.drop_first()[p - 1], m));
                assert(2 * (p - 1) == 2 * p - 2);
            }
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Well-formedness of the modular machine (the determinism proof).
// ─────────────────────────────────────────────────────────────────────────────

/// The modular machine built from a well-formed TM is a well-formed modular machine — in particular
/// **deterministic**: distinct quadruples never share a residue pair.
pub proof fn lemma_tm_modmachine_wf(tm: Tm)
    requires
        tm_wf(tm),
    ensures
        mod_machine_wf(tm_to_modmachine(tm)),
{
    reveal(tm_wf);
    let mm = tm_to_modmachine(tm);
    let m = tm.m;
    let n = tm.n;
    let qs = tm.quints;
    lemma_quads_of(qs, m);
    assert(mm.quads.len() == 2 * qs.len());

    // m > 1 and 0 < n < m.
    assert(mm.m > 1 && 0 < mm.n < mm.m);

    // quad_wf for every quad.
    assert forall|i: int| 0 <= i < mm.quads.len() implies quad_wf(#[trigger] mm.quads[i], mm.m) by {
        let p = i / 2;
        assert(0 <= p < qs.len()) by { lemma_index_half(i, qs.len()); }
        assert(quint_wf(qs[p], n, m));
        // c = a2*m + q2 < m*m  (since a2 ≤ n ≤ m-1, q2 < m).
        assert(qs[p].a2 * m + qs[p].q2 < m * m) by {
            assert(qs[p].a2 <= n && n < m && qs[p].q2 < m);
            lemma_c_bound(qs[p].a2, qs[p].q2, n, m);
        }
        if i % 2 == 0 {
            assert(i == 2 * p);
            assert(mm.quads[i] == quint_first(qs[p], m));
        } else {
            assert(i == 2 * p + 1);
            assert(mm.quads[i] == quint_second(qs[p], m));
        }
    }

    // determinism: distinct quads never share a residue pair.
    assert forall|i: int, j: int|
        0 <= i < mm.quads.len() && 0 <= j < mm.quads.len() && i != j
        && #[trigger] mm.quads[i].a == #[trigger] mm.quads[j].a
        && mm.quads[i].b == mm.quads[j].b
        implies i == j
    by {
        let pi = i / 2;
        let pj = j / 2;
        lemma_index_half(i, qs.len());
        lemma_index_half(j, qs.len());
        assert(quint_wf(qs[pi], n, m) && quint_wf(qs[pj], n, m));
        // resolve each quad to first/second by parity.
        if i % 2 == 0 { assert(i == 2 * pi); assert(mm.quads[i] == quint_first(qs[pi], m)); }
        else { assert(i == 2 * pi + 1); assert(mm.quads[i] == quint_second(qs[pi], m)); }
        if j % 2 == 0 { assert(j == 2 * pj); assert(mm.quads[j] == quint_first(qs[pj], m)); }
        else { assert(j == 2 * pj + 1); assert(mm.quads[j] == quint_second(qs[pj], m)); }
        // residue analysis: first quad has a ≤ n, b ≥ n+1; second has a ≥ n+1, b ≤ n.
        if i % 2 == 0 && j % 2 == 0 {
            // both first: (a,q) residues ⟹ same quintuple by TM determinism.
            assert(qs[pi].a == qs[pj].a && qs[pi].q == qs[pj].q);
            assert(pi == pj);
            assert(i == j);
        } else if i % 2 == 1 && j % 2 == 1 {
            // both second: (q,a) residues ⟹ same quintuple.
            assert(qs[pi].q == qs[pj].q && qs[pi].a == qs[pj].a);
            assert(pi == pj);
            assert(i == j);
        } else if i % 2 == 0 && j % 2 == 1 {
            // first.a = qs[pi].a ≤ n; second.a = qs[pj].q ≥ n+1 — cannot be equal.
            assert(qs[pi].a == qs[pj].q);
            assert(qs[pi].a <= n && qs[pj].q >= n + 1);
            assert(false);
        } else {
            // i odd, j even: symmetric.
            assert(qs[pi].q == qs[pj].a);
            assert(qs[pi].q >= n + 1 && qs[pj].a <= n);
            assert(false);
        }
    }
}

/// `c = a2·m + q2 < m²` when `a2 ≤ n < m` and `q2 < m`.
pub proof fn lemma_c_bound(a2: nat, q2: nat, n: nat, m: nat)
    requires
        a2 <= n,
        n < m,
        q2 < m,
    ensures
        a2 * m + q2 < m * m,
{
    assert(a2 <= m - 1);
    assert(a2 * m <= (m - 1) * m) by (nonlinear_arith)
        requires a2 <= m - 1;
    assert((m - 1) * m == m * m - m) by (nonlinear_arith);
    assert(a2 * m + q2 <= m * m - m + q2);
    assert(q2 < m);
}

/// `0 ≤ i < 2·len ⟹ 0 ≤ i/2 < len`.
pub proof fn lemma_index_half(i: int, len: nat)
    requires
        0 <= i < 2 * len,
    ensures
        0 <= i / 2 < len,
{
}

// ─────────────────────────────────────────────────────────────────────────────
// G2-C — the encoding and the per-step simulation (the arithmetic heart).
// ─────────────────────────────────────────────────────────────────────────────

/// Pair-encoding 1 of a config: `(u·m + scanned, v·m + state)`.
pub open spec fn rep1(c: TmConfig, m: nat) -> (nat, nat) {
    (c.u * m + c.a, c.v * m + c.q)
}

/// Pair-encoding 2 of a config: `(u·m + state, v·m + scanned)`. The two reps alternate as the head
/// moves (R lands on rep2 of the next config, L on rep1).
pub open spec fn rep2(c: TmConfig, m: nat) -> (nat, nat) {
    (c.u * m + c.q, c.v * m + c.a)
}

/// The modular-machine target pair of one step (paper p.3): `(u·m²+a2·m+q2, v)` for R,
/// `(u, v·m²+a2·m+q2)` for L.
pub open spec fn sim_target(qt: Quintuple, c: TmConfig, m: nat) -> (nat, nat) {
    match qt.dir {
        Dir::R => (c.u * m * m + qt.a2 * m + qt.q2, c.v),
        Dir::L => (c.u, c.v * m * m + qt.a2 * m + qt.q2),
    }
}

/// The next config's rep that `sim_target` equals: rep2 of `apply_quint` for R, rep1 for L.
pub open spec fn rep_next(qt: Quintuple, c: TmConfig, m: nat) -> (nat, nat) {
    match qt.dir {
        Dir::R => rep2(apply_quint(qt, c, m), m),
        Dir::L => rep1(apply_quint(qt, c, m), m),
    }
}

/// **The per-step simulation.** For a non-terminal config `c` with matching quintuple `qt`, both
/// pair-encodings of `c` yield (in one modular step) the `sim_target` pair, which equals the
/// appropriate rep of the next config `apply_quint(qt, c, m) = tm_step(c)`.
pub proof fn lemma_sim_step(tm: Tm, c: TmConfig)
    requires
        tm_wf(tm),
        !tm_terminal(tm, c),
    ensures
        ({
            let mm = tm_to_modmachine(tm);
            let m = tm.m;
            let qt = tm.quints[matching_index(tm, c)];
            let tgt = sim_target(qt, c, m);
            &&& mm_yields(mm, rep1(c, m).0, rep1(c, m).1, tgt.0, tgt.1)
            &&& mm_yields(mm, rep2(c, m).0, rep2(c, m).1, tgt.0, tgt.1)
            &&& tgt == rep_next(qt, c, m)
        }),
{
    reveal(tm_wf);
    let mm = tm_to_modmachine(tm);
    let m = tm.m;
    let p = matching_index(tm, c);
    let qt = tm.quints[p];
    lemma_matching_index_ok(tm, c);          // 0 ≤ p < len, qt matches c
    lemma_nonterminal_residues(tm, c);       // c.a ≤ n < m, n+1 ≤ c.q < m
    assert(qt.q == c.q && qt.a == c.a);
    assert(c.a < m && c.q < m);
    lemma_quads_of(tm.quints, m);
    let len = tm.quints.len();
    assert(0 <= p < len);
    // the two firing quads sit at 2p (first) and 2p+1 (second).
    assert(mm.quads.len() == 2 * len);
    assert(mm.quads[2 * p] == quint_first(qt, m));
    assert(mm.quads[2 * p + 1] == quint_second(qt, m));
    assert(0 <= 2 * p < mm.quads.len() && 0 <= 2 * p + 1 < mm.quads.len());

    // residue/division facts for the four (u or v) × (a or q) packings.
    lemma_div_mod_step(c.u, m, c.a);   // (c.u*m+c.a)/m == c.u, %m == c.a
    lemma_div_mod_step(c.v, m, c.q);   // (c.v*m+c.q)/m == c.v, %m == c.q
    lemma_div_mod_step(c.u, m, c.q);   // for rep2.0
    lemma_div_mod_step(c.v, m, c.a);   // for rep2.1
    // quad_step packs as `(x/m)*(m*m)`; sim_target writes `x*m*m` — reconcile the association.
    assert(c.u * (m * m) == c.u * m * m) by (nonlinear_arith);
    assert(c.v * (m * m) == c.v * m * m) by (nonlinear_arith);

    let tgt = sim_target(qt, c, m);
    let c2 = apply_quint(qt, c, m);

    match qt.dir {
        Dir::R => {
            // first quad fires from rep1; second from rep2; both → (c.u*m²+a2*m+q2, c.v).
            let fq = quint_first(qt, m);
            let sq = quint_second(qt, m);
            assert(quad_matches(fq, m, rep1(c, m).0, rep1(c, m).1));   // residues (c.a, c.q)
            assert(quad_matches(sq, m, rep2(c, m).0, rep2(c, m).1));   // residues (c.q, c.a)
            assert(quad_step(fq, m, rep1(c, m).0, rep1(c, m).1) == tgt);
            assert(quad_step(sq, m, rep2(c, m).0, rep2(c, m).1) == tgt);
            assert(mm_yields(mm, rep1(c, m).0, rep1(c, m).1, tgt.0, tgt.1)) by {
                assert(quad_matches(mm.quads[2 * p], m, rep1(c, m).0, rep1(c, m).1)
                    && quad_step(mm.quads[2 * p], m, rep1(c, m).0, rep1(c, m).1) == (tgt.0, tgt.1));
            }
            assert(mm_yields(mm, rep2(c, m).0, rep2(c, m).1, tgt.0, tgt.1)) by {
                assert(quad_matches(mm.quads[2 * p + 1], m, rep2(c, m).0, rep2(c, m).1)
                    && quad_step(mm.quads[2 * p + 1], m, rep2(c, m).0, rep2(c, m).1) == (tgt.0, tgt.1));
            }
            // tgt == rep2(c2): c2 = (c.u*m+a2, c.v/m, c.v%m, q2).
            lemma_div_mod_id_local(c.v, m);   // (c.v/m)*m + c.v%m == c.v
            assert((c.u * m + qt.a2) * m + qt.q2 == c.u * m * m + qt.a2 * m + qt.q2) by (nonlinear_arith);
            assert(tgt == rep2(c2, m));
            assert(tgt == rep_next(qt, c, m));
        },
        Dir::L => {
            let fq = quint_first(qt, m);
            let sq = quint_second(qt, m);
            assert(quad_matches(fq, m, rep1(c, m).0, rep1(c, m).1));
            assert(quad_matches(sq, m, rep2(c, m).0, rep2(c, m).1));
            assert(quad_step(fq, m, rep1(c, m).0, rep1(c, m).1) == tgt);
            assert(quad_step(sq, m, rep2(c, m).0, rep2(c, m).1) == tgt);
            assert(mm_yields(mm, rep1(c, m).0, rep1(c, m).1, tgt.0, tgt.1)) by {
                assert(quad_matches(mm.quads[2 * p], m, rep1(c, m).0, rep1(c, m).1)
                    && quad_step(mm.quads[2 * p], m, rep1(c, m).0, rep1(c, m).1) == (tgt.0, tgt.1));
            }
            assert(mm_yields(mm, rep2(c, m).0, rep2(c, m).1, tgt.0, tgt.1)) by {
                assert(quad_matches(mm.quads[2 * p + 1], m, rep2(c, m).0, rep2(c, m).1)
                    && quad_step(mm.quads[2 * p + 1], m, rep2(c, m).0, rep2(c, m).1) == (tgt.0, tgt.1));
            }
            // tgt == rep1(c2): c2 = (c.u/m, c.v*m+a2, c.u%m, q2).
            lemma_div_mod_id_local(c.u, m);   // (c.u/m)*m + c.u%m == c.u
            assert((c.v * m + qt.a2) * m + qt.q2 == c.v * m * m + qt.a2 * m + qt.q2) by (nonlinear_arith);
            assert(tgt == rep1(c2, m));
            assert(tgt == rep_next(qt, c, m));
        },
    }
}

/// `x == (x/m)·m + x%m` (the fundamental div/mod identity, local wrapper over the group-theory lemma).
pub proof fn lemma_div_mod_id_local(x: nat, m: nat)
    requires
        m > 0,
    ensures
        (x / m) * m + x % m == x,
{
    verus_group_theory::machine_group::lemma_div_mod_id(x, m);
}

} // verus!
