//! # GAP-2 G2-F Route (i) brick R-cmp (B-cmp.8) — the compare-DECIDES assembly.
//!
//! Glues the verified compare bricks into the end-to-end decision over the **parked entry** interface
//! ([`crate::tm_cmp_decide::lemma_cmp_bootstrap`]'s requires). This file builds the **ACCEPT** direction:
//! when the relocated output equals the parked α (both reversed digit lists, equal length, all matched),
//! the comparator reaches `q_accept`.
//!
//! The chain is a pure composition of existing lemmas, glued by [`lemma_tm_run_split`]:
//!
//! ```text
//!   parked entry ──bootstrap(8)──▶ INV(1)  ──loop(cmp_loop_fuel)──▶ INV(L-1)  ──accept_decide──▶ q_accept
//! ```
//!
//! **The bridge.** [`lemma_cmp_bootstrap`] lands a SPECIFIC config; the loop expects
//! [`crate::tm_cmp_loop::cmp_inv_config`] form. The recognition: the bootstrap exit IS
//! `cmp_inv_config(qw, [α[0]], α[1..], suf'=5, g=2, out_above, m)` — gap `g=2` (the original boundary `0`
//! PLUS the just-consumed `α[0]` cell), restored prefix `[α[0]]`, the marker on `α[1]`. The arithmetic:
//! `pile_zeros(out_rest, 1, m) == pile_zeros(cmp_out_pregap, 2, m) / m` iff `cmp_out_pregap == out_rest`.
//!
//! For output `==` α (the accept case) the parked layout collapses to `u == v == dpack(α) + m^L·5`
//! (output and α coincide; each carries the far `5` sentinel at the top).
//!
//! Fully verified, no verifier escape hatches.

use vstd::prelude::*;
use verus_group_theory::machine_group::Dir;
use crate::tm::{Tm, TmConfig, tm_wf, tm_run};
use crate::tm_gadget::mk_quint;
use crate::tm_dstring::{dpack, pow_nat, lemma_dpack_pop, lemma_dpack_push, lemma_dpack_empty,
    lemma_pow_nat_unfold, lemma_dpack_append};
use crate::tm_copy_refresh::lemma_pow_nat_add;
use crate::tm_skip_blank::pile_zeros;
use crate::tm_cmp_loop::{cmp_inv_config, cmp_above, cmp_marker, cmp_out_pregap, cmp_loop_fuel,
    cmp_quints_present, has_quint, extract_quint, lemma_cmp_loop};
use crate::tm_cmp_decide::{lemma_cmp_bootstrap, lemma_cmp_accept_decide, lemma_cmp_toolong_round};
use crate::tm_run_lemmas::lemma_tm_run_split;

verus! {

/// The α value strictly ABOVE position `k` (the suffix `α[k+1..]` packed low-first, then the far `5`
/// sentinel): `dpack(α[k+1..]) + m^{|α|-1-k}·5`. This is the `suf` the compare invariant carries when the
/// marker hides `α[k]` (`cmp_marker([α[k]], alpha_tail_above(α,k), m)` is the marker word at `INV(k)`).
pub open spec fn alpha_tail_above(alpha: Seq<nat>, k: nat, m: nat) -> nat {
    dpack(alpha.subrange((k + 1) as int, alpha.len() as int), m)
        + pow_nat(m, (alpha.len() - 1 - k) as nat) * 5
}

/// **Bridge suffix identity.** `cmp_above(α[1..p+1], alpha_tail_above(α, p)) == alpha_tail_above(α, 1)` —
/// the bootstrap's `suf` (the α value above `α[1]`) is recovered from the loop-list `α[1..p]` and the
/// `INV(p)`-suffix `alpha_tail_above(α, p)`. The split `α[2..L] = α[2..p+1] ++ α[p+1..L]` (`lemma_dpack_append`)
/// plus `m^{p-1}·m^{L-1-p} = m^{L-2}` (`lemma_pow_nat_add`).
pub proof fn lemma_bridge_suf(alpha: Seq<nat>, p: nat, m: nat)
    requires
        m > 5,
        alpha.len() >= 2,
        1 <= p <= alpha.len() - 1,
        forall|k: int| 0 <= k < alpha.len() ==> 1 <= #[trigger] alpha[k] <= 4,
    ensures
        cmp_above(alpha.subrange(1, (p + 1) as int), alpha_tail_above(alpha, p, m), m)
            == alpha_tail_above(alpha, 1, m),
{
    let big_l = alpha.len();
    let ds = alpha.subrange(1, (p + 1) as int);                // length p
    let suf_p = alpha_tail_above(alpha, p, m);
    assert(ds.len() == p);
    // ds.drop_first() == α[2..p+1]  (length p-1).
    let lo = alpha.subrange(2, (p + 1) as int);
    assert(ds.drop_first() =~= lo) by {
        assert forall|i: int| #![auto] 0 <= i < p - 1 implies ds.drop_first()[i] == lo[i] by {
            assert(ds.drop_first()[i] == ds[i + 1]);
        }
    }
    let hi = alpha.subrange((p + 1) as int, big_l as int);     // α[p+1..L]
    // α[2..L] == α[2..p+1] ++ α[p+1..L].
    assert(alpha.subrange(2, big_l as int) =~= lo + hi) by {
        assert((lo + hi).len() == big_l - 2);
        assert forall|i: int| #![auto] 0 <= i < big_l - 2 implies alpha.subrange(2, big_l as int)[i] == (lo + hi)[i] by {
            if i < p - 1 { assert((lo + hi)[i] == lo[i]); } else { assert((lo + hi)[i] == hi[i - (p - 1)]); }
        }
    }
    lemma_dpack_append(lo, hi, m);                             // dpack(α[2..L]) == dpack(lo) + m^{p-1}·dpack(hi)
    assert(lo.len() == p - 1);
    lemma_pow_nat_add(m, (p - 1) as nat, (big_l - 1 - p) as nat);   // m^{L-2} == m^{p-1}·m^{L-1-p}
    assert(((p - 1) + (big_l - 1 - p)) as nat == (big_l - 2) as nat);
    // cmp_above(ds, suf_p) == dpack(lo) + m^{p-1}·suf_p.
    assert((ds.len() - 1) as nat == (p - 1) as nat);
    assert(cmp_above(ds, suf_p, m) == dpack(lo, m) + pow_nat(m, (p - 1) as nat) * suf_p);
    assert(cmp_above(ds, suf_p, m) == alpha_tail_above(alpha, 1, m)) by(nonlinear_arith)
        requires
            cmp_above(ds, suf_p, m) == dpack(lo, m) + pow_nat(m, (p - 1) as nat) * suf_p,
            suf_p == dpack(hi, m) + pow_nat(m, (big_l - 1 - p) as nat) * 5,
            dpack(alpha.subrange(2, big_l as int), m) == dpack(lo, m) + pow_nat(m, (p - 1) as nat) * dpack(hi, m),
            pow_nat(m, (big_l - 2) as nat) == pow_nat(m, (p - 1) as nat) * pow_nat(m, (big_l - 1 - p) as nat),
            alpha_tail_above(alpha, 1, m) == dpack(alpha.subrange(2, big_l as int), m) + pow_nat(m, (big_l - 2) as nat) * 5;
}

/// The total fuel of the accept-decision chain over an α of length `L`: bootstrap `8` + the matched loop
/// (`L-2` rounds from `INV(1)`) + the final accept decision (`2·(L-1) + 3·L + 6`).
pub open spec fn cmp_accept_fuel(big_l: nat) -> nat {
    (8 + cmp_loop_fuel(1, 2, (big_l - 2) as nat) + (2 * (big_l - 1) + 3 * big_l + 6)) as nat
}

/// **B-cmp.8 — the ACCEPT decision, end-to-end.** From the parked entry for an α `==` output
/// (`u == v == dpack(α) + m^L·5`, head on the boundary `0`, state `q_start`), the comparator runs the
/// bootstrap, the `L-2` matched rounds, and the final accept decision, reaching `q_accept`. The
/// quintuple availability is the value-indexed [`cmp_quints_present`] for every value (covers bootstrap +
/// loop + the match-round-end's compare/return/marker), the two bootstrap PLACEMENT quintuples, and the
/// five α-exhaust VERIFY quintuples (`q_verify_end`/`q_verify_cmp`/`q_accept`). Requires `n ≥ 5`,
/// `|α| ≥ 2`, all α digits `1..4`.
pub proof fn lemma_cmp_decides_accept(
    tm: Tm,
    qw: spec_fn(nat) -> nat, qc: spec_fn(nat) -> nat, qb: spec_fn(nat) -> nat, qr: nat,
    q_start: nat, q_read_boot: nat, q_verify_end: nat, q_verify_cmp: nat, q_accept: nat,
    alpha: Seq<nat>,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        alpha.len() >= 2,
        forall|k: int| 0 <= k < alpha.len() ==> 1 <= #[trigger] alpha[k] <= 4,
        forall|V: nat| #![trigger cmp_quints_present(tm, qw, qc, qb, qr, V)]
            1 <= V <= 4 ==> cmp_quints_present(tm, qw, qc, qb, qr, V),
        has_quint(tm, mk_quint(q_start, 0, 0, q_read_boot, Dir::R)),
        has_quint(tm, mk_quint(q_read_boot, alpha[0], 5, qw(alpha[0]), Dir::L)),
        has_quint(tm, mk_quint(qr, 5, 5, q_verify_end, Dir::L)),
        has_quint(tm, mk_quint(q_verify_end, 1, 1, q_verify_end, Dir::L)),
        has_quint(tm, mk_quint(q_verify_end, 2, 2, q_verify_end, Dir::L)),
        has_quint(tm, mk_quint(q_verify_end, 3, 3, q_verify_end, Dir::L)),
        has_quint(tm, mk_quint(q_verify_end, 4, 4, q_verify_end, Dir::L)),
        has_quint(tm, mk_quint(q_verify_end, 0, 0, q_verify_cmp, Dir::L)),
        has_quint(tm, mk_quint(q_verify_cmp, 0, 0, q_verify_cmp, Dir::L)),
        has_quint(tm, mk_quint(q_verify_cmp, 5, 5, q_accept, Dir::R)),
    ensures
        tm_run(tm,
            TmConfig {
                u: dpack(alpha, tm.m) + pow_nat(tm.m, alpha.len()) * 5,
                v: dpack(alpha, tm.m) + pow_nat(tm.m, alpha.len()) * 5,
                a: 0,
                q: q_start,
            },
            cmp_accept_fuel(alpha.len())).q == q_accept,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let big_l = alpha.len();
    let a0 = alpha[0];
    let s = alpha[1];
    assert(1 <= a0 <= 4);
    assert(1 <= s <= 4);

    // ── digit-list helpers.
    let ds = alpha.subrange(1, big_l as int);                  // [α[1], …, α[L-1]]  (length L-1)
    assert(ds.len() == big_l - 1);
    assert(ds[0] == alpha[1]);
    assert forall|k: int| 0 <= k < ds.len() implies 1 <= #[trigger] ds[k] <= 4 by {
        assert(ds[k] == alpha[k + 1]);
    }
    let out_above = (alpha[(big_l - 1) as int] + m * 5) as nat;
    let suf = cmp_above(ds, 5, m);

    // ── the parked entry config.
    let pu = (dpack(alpha, m) + pow_nat(m, big_l) * 5) as nat;
    let c0 = TmConfig { u: pu, v: pu, a: 0, q: q_start };

    // ── decompose dpack(alpha) and pow_nat for the bootstrap fields.
    lemma_dpack_pop(alpha, m);                                  // dpack(alpha)%m == a0, /m == dpack(drop_first)
    let af = alpha.drop_first();
    assert(af.len() == big_l - 1);
    assert(af[0] == s);
    assert(dpack(alpha, m) == a0 + m * dpack(af, m));
    lemma_pow_nat_unfold(m, big_l);                             // m^L == m·m^{L-1}
    let out_rest = (dpack(af, m) + pow_nat(m, (big_l - 1) as nat) * 5) as nat;
    assert(pu == a0 + m * out_rest) by(nonlinear_arith)
        requires
            pu == dpack(alpha, m) + pow_nat(m, big_l) * 5,
            dpack(alpha, m) == a0 + m * dpack(af, m),
            pow_nat(m, big_l) == m * pow_nat(m, (big_l - 1) as nat),
            out_rest == dpack(af, m) + pow_nat(m, (big_l - 1) as nat) * 5;

    // v_above (= out_rest) decomposed as m·suf + s.
    lemma_dpack_pop(af, m);                                     // dpack(af)%m == s, /m == dpack(af.drop_first)
    let aff = af.drop_first();
    assert(aff.len() == big_l - 2);
    assert(dpack(af, m) == s + m * dpack(aff, m));
    // ds.drop_first() == aff (both == alpha[2..]).
    assert(ds.drop_first() =~= aff) by {
        assert(ds.drop_first().len() == big_l - 2);
        assert(aff.len() == big_l - 2);
        assert forall|i: int| #![auto] 0 <= i < big_l - 2 implies ds.drop_first()[i] == aff[i] by {
            assert(ds.drop_first()[i] == ds[i + 1]);
            assert(ds[i + 1] == alpha[i + 2]);
            assert(aff[i] == af[i + 1]);
            assert(af[i + 1] == alpha[i + 2]);
        }
    }
    // suf == dpack(aff) + m^{L-2}·5  (cmp_above unfold).
    lemma_pow_nat_unfold(m, (big_l - 1) as nat);               // m^{L-1} == m·m^{L-2}
    assert((ds.len() - 1) as nat == (big_l - 2) as nat);
    assert(suf == dpack(aff, m) + pow_nat(m, (big_l - 2) as nat) * 5);
    let v_above = (m * suf + s) as nat;
    assert(out_rest == v_above) by(nonlinear_arith)
        requires
            out_rest == dpack(af, m) + pow_nat(m, (big_l - 1) as nat) * 5,
            dpack(af, m) == s + m * dpack(aff, m),
            pow_nat(m, (big_l - 1) as nat) == m * pow_nat(m, (big_l - 2) as nat),
            suf == dpack(aff, m) + pow_nat(m, (big_l - 2) as nat) * 5,
            v_above == m * suf + s;
    assert(pu == a0 + m * v_above);

    // ── extract the bootstrap quintuple indices (a0-family + s-family + 2 placement).
    assert(cmp_quints_present(tm, qw, qc, qb, qr, a0));
    assert(cmp_quints_present(tm, qw, qc, qb, qr, s));
    let i0 = extract_quint(tm, mk_quint(q_start, 0, 0, q_read_boot, Dir::R));
    let im = extract_quint(tm, mk_quint(q_read_boot, a0, 5, qw(a0), Dir::L));
    let ib = extract_quint(tm, mk_quint(qw(a0), 0, 0, qc(a0), Dir::L));
    let ic = extract_quint(tm, mk_quint(qc(a0), 0, 0, qc(a0), Dir::L));
    let jc = extract_quint(tm, mk_quint(qc(a0), a0, 0, qb(a0), Dir::R));
    let js = extract_quint(tm, mk_quint(qb(a0), 0, 0, qb(a0), Dir::R));
    let j  = extract_quint(tm, mk_quint(qb(a0), 5, a0, qr, Dir::R));
    let jr = extract_quint(tm, mk_quint(qr, s, 5, qw(s), Dir::L));
    let l1 = extract_quint(tm, mk_quint(qw(s), 1, 1, qw(s), Dir::L));
    let l2 = extract_quint(tm, mk_quint(qw(s), 2, 2, qw(s), Dir::L));
    let l3 = extract_quint(tm, mk_quint(qw(s), 3, 3, qw(s), Dir::L));
    let l4 = extract_quint(tm, mk_quint(qw(s), 4, 4, qw(s), Dir::L));

    // ── run the bootstrap: parked → INV(1).
    lemma_cmp_bootstrap(tm, c0, q_start, q_read_boot, qw(a0), qc(a0), qb(a0), qr, qw(s),
        a0, s, suf, v_above, out_rest, i0, im, ib, ic, jc, js, j, jr, l1, l2, l3, l4);
    let c_inv1 = TmConfig {
        u: pile_zeros(out_rest, 1, m),
        v: dpack(seq![a0], m) + pow_nat(m, 1) * (m * suf + 5),
        a: 0,
        q: qw(s),
    };
    assert(tm_run(tm, c0, 8) == c_inv1);

    // ── bridge: c_inv1 == cmp_inv_config(qw, [a0], ds, 5, 2, out_above, m).
    let inv1 = cmp_inv_config(qw, seq![a0], ds, 5, 2, out_above, m);
    // output side: cmp_out_pregap(ds, out_above) == out_rest.
    assert(cmp_out_pregap(ds, out_above, m) == out_rest) by {
        lemma_bridge_out_pregap(alpha, out_above, out_rest, m);
    }
    assert(pile_zeros(out_rest, 0, m) == out_rest);
    assert(pile_zeros(out_rest, 1, m) == pile_zeros(out_rest, 0, m) * m);   // g=1 unfold
    assert(pile_zeros(out_rest, 2, m) == pile_zeros(out_rest, 1, m) * m);   // g=2 unfold
    assert(pile_zeros(out_rest, 1, m) == out_rest * m);
    assert(pile_zeros(out_rest, 2, m) == out_rest * m * m) by(nonlinear_arith)
        requires pile_zeros(out_rest, 2, m) == (out_rest * m) * m;
    assert((out_rest * m * m) / m == out_rest * m) by(nonlinear_arith) requires m > 1;
    assert((out_rest * m * m) % m == 0) by(nonlinear_arith) requires m > 1;
    assert(inv1.u == pile_zeros(out_rest, 1, m));
    assert(inv1.a == 0);
    // marker side: cmp_marker(ds, 5) == m·suf + 5; pre == [a0] (both sides share pow_nat(m,1)).
    assert(cmp_marker(ds, 5, m) == m * suf + 5);
    assert(dpack(seq![a0], m) == a0) by { lemma_dpack_singleton_local(a0, m); }
    assert((seq![a0]).len() == 1);
    assert(inv1.v == dpack(seq![a0], m) + pow_nat(m, (seq![a0]).len()) * cmp_marker(ds, 5, m));
    assert(c_inv1.v == dpack(seq![a0], m) + pow_nat(m, 1) * (m * suf + 5));
    assert(inv1.v == c_inv1.v);
    assert(inv1.q == qw(ds[0]));
    assert(ds[0] == s);
    assert(c_inv1 == inv1);

    // ── run the matched loop: INV(1) → INV(L-1).
    assert forall|k: int| 0 <= k < (seq![a0]).len() implies 1 <= #[trigger] (seq![a0])[k] <= 4 by { }
    lemma_cmp_loop(tm, inv1, qw, qc, qb, qr, seq![a0], ds, 5, 2, out_above);
    let blk = seq![a0] + ds.subrange(0, (ds.len() - 1) as int);
    let ds_last = ds.subrange((ds.len() - 1) as int, ds.len() as int);
    let g_final = (2 + (ds.len() - 1)) as nat;                  // == L
    let inv_last = cmp_inv_config(qw, blk, ds_last, 5, g_final, out_above, m);
    assert(tm_run(tm, inv1, cmp_loop_fuel(1, 2, (ds.len() - 1) as nat)) == inv_last);
    assert(g_final == big_l);

    // ── recognize inv_last as the accept_decide entry.
    let vk = alpha[(big_l - 1) as int];
    assert(1 <= vk <= 4);
    // blk == alpha.subrange(0, L-1).
    assert(blk =~= alpha.subrange(0, (big_l - 1) as int)) by {
        lemma_bridge_blk(alpha, m);
    }
    let blk2 = alpha.subrange(0, (big_l - 1) as int);
    assert(blk2.len() == big_l - 1);
    assert(blk2.len() >= 1);
    assert forall|k: int| 0 <= k < blk2.len() implies 1 <= #[trigger] blk2[k] <= 4 by {
        assert(blk2[k] == alpha[k]);
    }
    // ds_last == [vk].
    assert(ds_last =~= seq![vk]) by {
        assert(ds_last.len() == 1);
        assert(ds_last[0] == ds[(ds.len() - 1) as int]);
        assert(ds[(ds.len() - 1) as int] == alpha[(big_l - 1) as int]);
    }
    // cmp_marker([vk], 5) == m·5 + 5 = w; whi == 5.
    let w = (m * 5 + 5) as nat;
    assert(cmp_above(seq![vk], 5, m) == 5) by {
        assert((seq![vk]).drop_first() =~= Seq::<nat>::empty());
        lemma_dpack_empty(m);
        assert(((seq![vk]).len() - 1) as nat == 0nat);
        assert(pow_nat(m, 0) == 1);
    }
    assert(cmp_marker(seq![vk], 5, m) == w);

    // accept_decide's entry config fields (with blk2, w, whi=5, g=L, out_above=vk+m·5).
    assert(((seq![vk]).len() - 1) as int == 0int);
    assert((seq![vk]).subrange(0, ((seq![vk]).len() - 1) as int) =~= Seq::<nat>::empty());
    lemma_dpack_empty(m);
    assert(dpack((seq![vk]).subrange(0, ((seq![vk]).len() - 1) as int), m) == 0);
    assert(((seq![vk]).len() - 1) as nat == 0nat);
    assert(pow_nat(m, 0) == 1);
    assert(pow_nat(m, ((seq![vk]).len() - 1) as nat) == 1);
    assert(cmp_out_pregap(seq![vk], out_above, m)
        == dpack((seq![vk]).subrange(0, ((seq![vk]).len() - 1) as int), m)
           + pow_nat(m, ((seq![vk]).len() - 1) as nat) * out_above);   // def unfold
    assert(cmp_out_pregap(seq![vk], out_above, m) == out_above) by(nonlinear_arith)
        requires
            cmp_out_pregap(seq![vk], out_above, m)
                == dpack((seq![vk]).subrange(0, ((seq![vk]).len() - 1) as int), m)
                   + pow_nat(m, ((seq![vk]).len() - 1) as nat) * out_above,
            dpack((seq![vk]).subrange(0, ((seq![vk]).len() - 1) as int), m) == 0,
            pow_nat(m, ((seq![vk]).len() - 1) as nat) == 1;
    assert(cmp_out_pregap(seq![vk], out_above, m) == vk + m * 5);

    // extract accept_decide indices (vk-family from cmp_quints_present + the 7 verify quints).
    assert(cmp_quints_present(tm, qw, qc, qb, qr, vk));
    let aib = extract_quint(tm, mk_quint(qw(vk), 0, 0, qc(vk), Dir::L));
    let aic = extract_quint(tm, mk_quint(qc(vk), 0, 0, qc(vk), Dir::L));
    let ajc = extract_quint(tm, mk_quint(qc(vk), vk, 0, qb(vk), Dir::R));
    let ajs = extract_quint(tm, mk_quint(qb(vk), 0, 0, qb(vk), Dir::R));
    let ai1 = extract_quint(tm, mk_quint(qb(vk), 1, 1, qb(vk), Dir::R));
    let ai2 = extract_quint(tm, mk_quint(qb(vk), 2, 2, qb(vk), Dir::R));
    let ai3 = extract_quint(tm, mk_quint(qb(vk), 3, 3, qb(vk), Dir::R));
    let ai4 = extract_quint(tm, mk_quint(qb(vk), 4, 4, qb(vk), Dir::R));
    let aj  = extract_quint(tm, mk_quint(qb(vk), 5, vk, qr, Dir::R));
    let aje = extract_quint(tm, mk_quint(qr, 5, 5, q_verify_end, Dir::L));
    let al1 = extract_quint(tm, mk_quint(q_verify_end, 1, 1, q_verify_end, Dir::L));
    let al2 = extract_quint(tm, mk_quint(q_verify_end, 2, 2, q_verify_end, Dir::L));
    let al3 = extract_quint(tm, mk_quint(q_verify_end, 3, 3, q_verify_end, Dir::L));
    let al4 = extract_quint(tm, mk_quint(q_verify_end, 4, 4, q_verify_end, Dir::L));
    let aibv = extract_quint(tm, mk_quint(q_verify_end, 0, 0, q_verify_cmp, Dir::L));
    let aicv = extract_quint(tm, mk_quint(q_verify_cmp, 0, 0, q_verify_cmp, Dir::L));
    let aja = extract_quint(tm, mk_quint(q_verify_cmp, 5, 5, q_accept, Dir::R));

    lemma_cmp_accept_decide(tm, inv_last, qw(vk), qc(vk), qb(vk), qr,
        q_verify_end, q_verify_cmp, q_accept, blk2, w, 5, vk, big_l,
        aib, aic, ajc, ajs, ai1, ai2, ai3, ai4, aj, aje,
        al1, al2, al3, al4, aibv, aicv, aja);
    let f3 = (2 * blk2.len() + 3 * big_l + 6) as nat;
    assert(tm_run(tm, inv_last, f3).q == q_accept);

    // ── compose the three runs.
    let f2 = cmp_loop_fuel(1, 2, (ds.len() - 1) as nat);
    lemma_tm_run_split(tm, c0, 8, f2);
    assert(tm_run(tm, c0, (8 + f2) as nat) == inv_last);
    lemma_tm_run_split(tm, c0, (8 + f2) as nat, f3);
    assert(cmp_accept_fuel(big_l) == (8 + f2 + f3) as nat);
    assert(tm_run(tm, c0, cmp_accept_fuel(big_l)) == tm_run(tm, inv_last, f3));
}

/// **B-cmp.8 — reach `INV(p)` (the reusable bootstrap+loop core).** From the parked entry whose output's
/// low `p` digits match `α[0..p-1]` (`u == dpack(α[0..p]) + m^p·out_tail`, the remaining output `out_tail`
/// — divergent/sentinel — above) and whose α side is the full reversed α with the far `5` sentinel
/// (`v == dpack(α) + m^L·5`), the comparator runs the bootstrap and the `p-1` matched rounds, landing at
/// `INV(p)`: marker hiding `α[p]`, restored prefix `α[0..p-1]`, gap `g = p+1`, output frontier
/// `= out_tail % m`. The α tail above the marker is [`alpha_tail_above`]`(α, p)`. Every decision terminal
/// (mismatch / too-short / too-long / accept) consumes this `INV(p)` and reads only `out_tail`. Requires
/// `n ≥ 5`, `|α| ≥ 2`, `1 ≤ p ≤ |α|-1`, all α digits `1..4`.
pub proof fn lemma_cmp_reach_inv_p(
    tm: Tm,
    qw: spec_fn(nat) -> nat, qc: spec_fn(nat) -> nat, qb: spec_fn(nat) -> nat, qr: nat,
    q_start: nat, q_read_boot: nat,
    alpha: Seq<nat>, p: nat, out_tail: nat,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        alpha.len() >= 2,
        1 <= p <= alpha.len() - 1,
        forall|k: int| 0 <= k < alpha.len() ==> 1 <= #[trigger] alpha[k] <= 4,
        forall|V: nat| #![trigger cmp_quints_present(tm, qw, qc, qb, qr, V)]
            1 <= V <= 4 ==> cmp_quints_present(tm, qw, qc, qb, qr, V),
        has_quint(tm, mk_quint(q_start, 0, 0, q_read_boot, Dir::R)),
        has_quint(tm, mk_quint(q_read_boot, alpha[0], 5, qw(alpha[0]), Dir::L)),
    ensures
        tm_run(tm,
            TmConfig {
                u: dpack(alpha.subrange(0, p as int), tm.m) + pow_nat(tm.m, p) * out_tail,
                v: dpack(alpha, tm.m) + pow_nat(tm.m, alpha.len()) * 5,
                a: 0,
                q: q_start,
            },
            (8 + cmp_loop_fuel(1, 2, (p - 1) as nat)) as nat)
            == cmp_inv_config(qw, alpha.subrange(0, p as int), alpha.subrange(p as int, (p + 1) as int),
                alpha_tail_above(alpha, p, tm.m), (p + 1) as nat, out_tail, tm.m),
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let big_l = alpha.len();
    let a0 = alpha[0];
    let s = alpha[1];
    assert(1 <= a0 <= 4);
    assert(1 <= s <= 4);
    let ds = alpha.subrange(1, (p + 1) as int);                 // [α[1], …, α[p]]  (length p)
    assert(ds.len() == p);
    assert(ds[0] == alpha[1]);
    assert forall|k: int| 0 <= k < ds.len() implies 1 <= #[trigger] ds[k] <= 4 by { assert(ds[k] == alpha[k + 1]); }
    let suf_p = alpha_tail_above(alpha, p, m);
    let suf_boot = alpha_tail_above(alpha, 1, m);
    let out_rest = (dpack(alpha.subrange(1, p as int), m) + pow_nat(m, (p - 1) as nat) * out_tail) as nat;

    let pu = (dpack(alpha.subrange(0, p as int), m) + pow_nat(m, p) * out_tail) as nat;
    let pv = (dpack(alpha, m) + pow_nat(m, big_l) * 5) as nat;
    let c0 = TmConfig { u: pu, v: pv, a: 0, q: q_start };

    // ── parked u == a0 + m·out_rest.
    let pre_p = alpha.subrange(0, p as int);
    assert(pre_p[0] == a0);
    lemma_dpack_pop(pre_p, m);                                  // dpack(pre_p)%m == a0, /m == dpack(drop_first)
    assert(pre_p.drop_first() =~= alpha.subrange(1, p as int)) by {
        assert forall|i: int| #![auto] 0 <= i < p - 1 implies pre_p.drop_first()[i] == alpha.subrange(1, p as int)[i] by {
            assert(pre_p.drop_first()[i] == pre_p[i + 1]);
        }
    }
    assert(dpack(pre_p, m) == a0 + m * dpack(alpha.subrange(1, p as int), m));
    lemma_pow_nat_unfold(m, p);                                 // m^p == m·m^{p-1}
    assert(pu == a0 + m * out_rest) by(nonlinear_arith)
        requires
            pu == dpack(pre_p, m) + pow_nat(m, p) * out_tail,
            dpack(pre_p, m) == a0 + m * dpack(alpha.subrange(1, p as int), m),
            pow_nat(m, p) == m * pow_nat(m, (p - 1) as nat),
            out_rest == dpack(alpha.subrange(1, p as int), m) + pow_nat(m, (p - 1) as nat) * out_tail;

    // ── parked v == a0 + m·(m·suf_boot + s).
    lemma_dpack_pop(alpha, m);
    let af = alpha.drop_first();
    assert(af[0] == s);
    lemma_dpack_pop(af, m);
    let aff = af.drop_first();
    assert(aff =~= alpha.subrange(2, big_l as int)) by {
        assert forall|i: int| #![auto] 0 <= i < big_l - 2 implies aff[i] == alpha.subrange(2, big_l as int)[i] by {
            assert(aff[i] == af[i + 1]);
            assert(af[i + 1] == alpha[i + 2]);
        }
    }
    assert(dpack(alpha, m) == a0 + m * dpack(af, m));
    assert(dpack(af, m) == s + m * dpack(aff, m));
    lemma_pow_nat_add(m, 2, (big_l - 2) as nat);               // m^L == m^2·m^{L-2}
    assert((2 + (big_l - 2)) as nat == big_l);
    assert(pow_nat(m, 2) == m * m) by { lemma_pow_nat_unfold(m, 2); lemma_pow_nat_unfold(m, 1); assert(pow_nat(m, 0) == 1); }
    let v_above = (m * suf_boot + s) as nat;
    assert(suf_boot == dpack(alpha.subrange(2, big_l as int), m) + pow_nat(m, (big_l - 2) as nat) * 5);
    assert(pv == a0 + m * v_above) by(nonlinear_arith)
        requires
            pv == dpack(alpha, m) + pow_nat(m, big_l) * 5,
            dpack(alpha, m) == a0 + m * dpack(af, m),
            dpack(af, m) == s + m * dpack(aff, m),
            dpack(aff, m) == dpack(alpha.subrange(2, big_l as int), m),
            pow_nat(m, big_l) == pow_nat(m, 2) * pow_nat(m, (big_l - 2) as nat),
            pow_nat(m, 2) == m * m,
            suf_boot == dpack(alpha.subrange(2, big_l as int), m) + pow_nat(m, (big_l - 2) as nat) * 5,
            v_above == m * suf_boot + s;

    // ── bootstrap suf == cmp_above(ds, suf_p) == suf_boot.
    lemma_bridge_suf(alpha, p, m);
    assert(cmp_above(ds, suf_p, m) == suf_boot);

    // ── extract bootstrap indices + run bootstrap.
    assert(cmp_quints_present(tm, qw, qc, qb, qr, a0));
    assert(cmp_quints_present(tm, qw, qc, qb, qr, s));
    let i0 = extract_quint(tm, mk_quint(q_start, 0, 0, q_read_boot, Dir::R));
    let im = extract_quint(tm, mk_quint(q_read_boot, a0, 5, qw(a0), Dir::L));
    let ib = extract_quint(tm, mk_quint(qw(a0), 0, 0, qc(a0), Dir::L));
    let ic = extract_quint(tm, mk_quint(qc(a0), 0, 0, qc(a0), Dir::L));
    let jc = extract_quint(tm, mk_quint(qc(a0), a0, 0, qb(a0), Dir::R));
    let js = extract_quint(tm, mk_quint(qb(a0), 0, 0, qb(a0), Dir::R));
    let j  = extract_quint(tm, mk_quint(qb(a0), 5, a0, qr, Dir::R));
    let jr = extract_quint(tm, mk_quint(qr, s, 5, qw(s), Dir::L));
    let l1 = extract_quint(tm, mk_quint(qw(s), 1, 1, qw(s), Dir::L));
    let l2 = extract_quint(tm, mk_quint(qw(s), 2, 2, qw(s), Dir::L));
    let l3 = extract_quint(tm, mk_quint(qw(s), 3, 3, qw(s), Dir::L));
    let l4 = extract_quint(tm, mk_quint(qw(s), 4, 4, qw(s), Dir::L));
    lemma_cmp_bootstrap(tm, c0, q_start, q_read_boot, qw(a0), qc(a0), qb(a0), qr, qw(s),
        a0, s, suf_boot, v_above, out_rest, i0, im, ib, ic, jc, js, j, jr, l1, l2, l3, l4);
    let c_inv1 = TmConfig {
        u: pile_zeros(out_rest, 1, m),
        v: dpack(seq![a0], m) + pow_nat(m, 1) * (m * suf_boot + 5),
        a: 0,
        q: qw(s),
    };
    assert(tm_run(tm, c0, 8) == c_inv1);

    // ── bridge: c_inv1 == cmp_inv_config(qw, [a0], ds, suf_p, 2, out_tail, m).
    let inv1 = cmp_inv_config(qw, seq![a0], ds, suf_p, 2, out_tail, m);
    // u side.
    assert(ds.subrange(0, (ds.len() - 1) as int) =~= alpha.subrange(1, p as int)) by {
        assert forall|i: int| #![auto] 0 <= i < p - 1 implies ds.subrange(0, (ds.len() - 1) as int)[i] == alpha.subrange(1, p as int)[i] by {
            assert(ds.subrange(0, (ds.len() - 1) as int)[i] == ds[i]);
            assert(ds[i] == alpha[i + 1]);
        }
    }
    assert((ds.len() - 1) as nat == (p - 1) as nat);
    assert(cmp_out_pregap(ds, out_tail, m) == out_rest);
    assert(pile_zeros(out_rest, 0, m) == out_rest);
    assert(pile_zeros(out_rest, 1, m) == pile_zeros(out_rest, 0, m) * m);
    assert(pile_zeros(out_rest, 2, m) == pile_zeros(out_rest, 1, m) * m);
    assert(pile_zeros(out_rest, 1, m) == out_rest * m);
    assert(pile_zeros(out_rest, 2, m) == out_rest * m * m) by(nonlinear_arith)
        requires pile_zeros(out_rest, 2, m) == (out_rest * m) * m;
    assert((out_rest * m * m) / m == out_rest * m) by(nonlinear_arith) requires m > 1;
    assert((out_rest * m * m) % m == 0) by(nonlinear_arith) requires m > 1;
    assert(inv1.u == pile_zeros(out_rest, 1, m));
    assert(inv1.a == 0);
    // v side.
    assert(cmp_marker(ds, suf_p, m) == m * suf_boot + 5);
    assert(dpack(seq![a0], m) == a0) by { lemma_dpack_singleton_local(a0, m); }
    assert((seq![a0]).len() == 1);
    assert(inv1.v == dpack(seq![a0], m) + pow_nat(m, (seq![a0]).len()) * cmp_marker(ds, suf_p, m));
    assert(c_inv1.v == dpack(seq![a0], m) + pow_nat(m, 1) * (m * suf_boot + 5));
    assert(inv1.v == c_inv1.v);
    assert(inv1.q == qw(ds[0]));
    assert(ds[0] == s);
    assert(c_inv1 == inv1);

    // ── run the matched loop: INV(1) → INV(p).
    assert forall|k: int| 0 <= k < (seq![a0]).len() implies 1 <= #[trigger] (seq![a0])[k] <= 4 by { }
    lemma_cmp_loop(tm, inv1, qw, qc, qb, qr, seq![a0], ds, suf_p, 2, out_tail);
    let blk = seq![a0] + ds.subrange(0, (ds.len() - 1) as int);
    let ds_last = ds.subrange((ds.len() - 1) as int, ds.len() as int);
    let inv_p = cmp_inv_config(qw, blk, ds_last, suf_p, (2 + (ds.len() - 1)) as nat, out_tail, m);
    assert(tm_run(tm, inv1, cmp_loop_fuel(1, 2, (ds.len() - 1) as nat)) == inv_p);

    // ── recognize inv_p as the ensures config.
    assert(blk =~= alpha.subrange(0, p as int)) by {
        assert(blk.len() == p);
        assert forall|i: int| #![auto] 0 <= i < p implies blk[i] == alpha.subrange(0, p as int)[i] by {
            if i == 0 { assert(blk[0] == a0); }
            else { assert(blk[i] == ds.subrange(0, (ds.len() - 1) as int)[i - 1]); assert(ds.subrange(0, (ds.len() - 1) as int)[i - 1] == ds[i - 1]); assert(ds[i - 1] == alpha[i]); }
        }
    }
    assert(ds_last =~= alpha.subrange(p as int, (p + 1) as int)) by {
        assert(ds_last.len() == 1);
        assert(ds_last[0] == ds[(ds.len() - 1) as int]);
        assert(ds[(ds.len() - 1) as int] == alpha[p as int]);
        assert(alpha.subrange(p as int, (p + 1) as int)[0] == alpha[p as int]);
    }
    assert((2 + (ds.len() - 1)) as nat == (p + 1) as nat);
    assert(tm_run(tm, inv1, cmp_loop_fuel(1, 2, (p - 1) as nat)) == inv_p);

    // ── compose bootstrap (8) + loop.
    lemma_tm_run_split(tm, c0, 8, cmp_loop_fuel(1, 2, (p - 1) as nat));
    assert((8 + cmp_loop_fuel(1, 2, (p - 1) as nat)) as nat == (8 + cmp_loop_fuel(1, 2, (p - 1) as nat)) as nat);
}

/// **B-cmp.8 — the MISMATCH decision, end-to-end.** From the parked entry whose output diverges from α at
/// position `p` (the low `p` digits match, then `out_tail = d_o + m·out_rest2` with `d_o = output[p] ∈ 1..4`
/// but `d_o ≠ α[p]`), the comparator reaches `INV(p)` ([`lemma_cmp_reach_inv_p`]) then the gap-cross reads
/// `d_o` and the mismatch quintuple fires → `q_reject`. Requires `n ≥ 5`, `|α| ≥ 2`, `1 ≤ p ≤ |α|-1`.
pub proof fn lemma_cmp_decides_mismatch(
    tm: Tm,
    qw: spec_fn(nat) -> nat, qc: spec_fn(nat) -> nat, qb: spec_fn(nat) -> nat, qr: nat,
    q_start: nat, q_read_boot: nat, q_reject: nat,
    alpha: Seq<nat>, p: nat, d_o: nat, out_rest2: nat,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        alpha.len() >= 2,
        1 <= p <= alpha.len() - 1,
        forall|k: int| 0 <= k < alpha.len() ==> 1 <= #[trigger] alpha[k] <= 4,
        1 <= d_o <= 4,
        d_o != alpha[p as int],
        forall|V: nat| #![trigger cmp_quints_present(tm, qw, qc, qb, qr, V)]
            1 <= V <= 4 ==> cmp_quints_present(tm, qw, qc, qb, qr, V),
        has_quint(tm, mk_quint(q_start, 0, 0, q_read_boot, Dir::R)),
        has_quint(tm, mk_quint(q_read_boot, alpha[0], 5, qw(alpha[0]), Dir::L)),
        has_quint(tm, mk_quint(qc(alpha[p as int]), d_o, d_o, q_reject, Dir::R)),
    ensures
        tm_run(tm,
            TmConfig {
                u: dpack(alpha.subrange(0, p as int), tm.m) + pow_nat(tm.m, p) * (d_o + tm.m * out_rest2),
                v: dpack(alpha, tm.m) + pow_nat(tm.m, alpha.len()) * 5,
                a: 0,
                q: q_start,
            },
            (8 + cmp_loop_fuel(1, 2, (p - 1) as nat) + (p + 2)) as nat).q == q_reject,
{
    reveal(tm_wf);
    let m = tm.m;
    let out_tail = (d_o + m * out_rest2) as nat;
    let vk = alpha[p as int];
    let c0 = TmConfig {
        u: dpack(alpha.subrange(0, p as int), m) + pow_nat(m, p) * out_tail,
        v: dpack(alpha, m) + pow_nat(m, alpha.len()) * 5,
        a: 0,
        q: q_start,
    };
    lemma_cmp_reach_inv_p(tm, qw, qc, qb, qr, q_start, q_read_boot, alpha, p, out_tail);
    let inv_p = cmp_inv_config(qw, alpha.subrange(0, p as int), alpha.subrange(p as int, (p + 1) as int),
        alpha_tail_above(alpha, p, m), (p + 1) as nat, out_tail, m);
    assert(tm_run(tm, c0, (8 + cmp_loop_fuel(1, 2, (p - 1) as nat)) as nat) == inv_p);

    // inv_p.a/.u are the pile_zeros(out_tail, p+1) form mismatch_round wants.
    lemma_singleton_out_pregap(alpha, p, out_tail, m);
    assert(inv_p.a == pile_zeros(d_o + m * out_rest2, (p + 1) as nat, m) % m);
    assert(inv_p.u == pile_zeros(d_o + m * out_rest2, (p + 1) as nat, m) / m);
    assert(inv_p.q == qw(vk));

    // extract the two cmp quints + the mismatch quint, fire mismatch_round.
    assert(cmp_quints_present(tm, qw, qc, qb, qr, vk));
    let ib = extract_quint(tm, mk_quint(qw(vk), 0, 0, qc(vk), Dir::L));
    let ic = extract_quint(tm, mk_quint(qc(vk), 0, 0, qc(vk), Dir::L));
    let jm = extract_quint(tm, mk_quint(qc(vk), d_o, d_o, q_reject, Dir::R));
    crate::tm_cmp_decide::lemma_cmp_mismatch_round(tm, inv_p, qw(vk), qc(vk), q_reject,
        (p + 1) as nat, d_o, out_rest2, ib, ic, jm);
    assert(tm_run(tm, inv_p, (p + 2) as nat).q == q_reject);

    lemma_tm_run_split(tm, c0, (8 + cmp_loop_fuel(1, 2, (p - 1) as nat)) as nat, (p + 2) as nat);
}

/// **B-cmp.8 — the TOO-SHORT decision, end-to-end.** The output is a proper prefix of α: it exhausts at
/// position `p` (`out_tail = 5`, the output far sentinel) while α still has `α[p]` pending. The comparator
/// reaches `INV(p)`, the gap-cross reads the output sentinel `5`, and the too-short quintuple fires →
/// `q_reject`. Requires `n ≥ 5`, `|α| ≥ 2`, `1 ≤ p ≤ |α|-1`.
pub proof fn lemma_cmp_decides_tooshort(
    tm: Tm,
    qw: spec_fn(nat) -> nat, qc: spec_fn(nat) -> nat, qb: spec_fn(nat) -> nat, qr: nat,
    q_start: nat, q_read_boot: nat, q_reject: nat,
    alpha: Seq<nat>, p: nat,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        alpha.len() >= 2,
        1 <= p <= alpha.len() - 1,
        forall|k: int| 0 <= k < alpha.len() ==> 1 <= #[trigger] alpha[k] <= 4,
        forall|V: nat| #![trigger cmp_quints_present(tm, qw, qc, qb, qr, V)]
            1 <= V <= 4 ==> cmp_quints_present(tm, qw, qc, qb, qr, V),
        has_quint(tm, mk_quint(q_start, 0, 0, q_read_boot, Dir::R)),
        has_quint(tm, mk_quint(q_read_boot, alpha[0], 5, qw(alpha[0]), Dir::L)),
        has_quint(tm, mk_quint(qc(alpha[p as int]), 5, 5, q_reject, Dir::R)),
    ensures
        tm_run(tm,
            TmConfig {
                u: dpack(alpha.subrange(0, p as int), tm.m) + pow_nat(tm.m, p) * 5,
                v: dpack(alpha, tm.m) + pow_nat(tm.m, alpha.len()) * 5,
                a: 0,
                q: q_start,
            },
            (8 + cmp_loop_fuel(1, 2, (p - 1) as nat) + (p + 2)) as nat).q == q_reject,
{
    reveal(tm_wf);
    let m = tm.m;
    let vk = alpha[p as int];
    let c0 = TmConfig {
        u: dpack(alpha.subrange(0, p as int), m) + pow_nat(m, p) * 5,
        v: dpack(alpha, m) + pow_nat(m, alpha.len()) * 5,
        a: 0,
        q: q_start,
    };
    lemma_cmp_reach_inv_p(tm, qw, qc, qb, qr, q_start, q_read_boot, alpha, p, 5);
    let inv_p = cmp_inv_config(qw, alpha.subrange(0, p as int), alpha.subrange(p as int, (p + 1) as int),
        alpha_tail_above(alpha, p, m), (p + 1) as nat, 5, m);
    assert(tm_run(tm, c0, (8 + cmp_loop_fuel(1, 2, (p - 1) as nat)) as nat) == inv_p);

    lemma_singleton_out_pregap(alpha, p, 5, m);
    assert(5nat == 5 + m * 0) by(nonlinear_arith);
    assert(inv_p.a == pile_zeros(5 + m * 0, (p + 1) as nat, m) % m);
    assert(inv_p.u == pile_zeros(5 + m * 0, (p + 1) as nat, m) / m);
    assert(inv_p.q == qw(vk));

    assert(cmp_quints_present(tm, qw, qc, qb, qr, vk));
    let ib = extract_quint(tm, mk_quint(qw(vk), 0, 0, qc(vk), Dir::L));
    let ic = extract_quint(tm, mk_quint(qc(vk), 0, 0, qc(vk), Dir::L));
    let jt = extract_quint(tm, mk_quint(qc(vk), 5, 5, q_reject, Dir::R));
    crate::tm_cmp_decide::lemma_cmp_tooshort_round(tm, inv_p, qw(vk), qc(vk), q_reject,
        (p + 1) as nat, 0, ib, ic, jt);
    assert(tm_run(tm, inv_p, (p + 2) as nat).q == q_reject);

    lemma_tm_run_split(tm, c0, (8 + cmp_loop_fuel(1, 2, (p - 1) as nat)) as nat, (p + 2) as nat);
}

/// **B-cmp.8 — the TOO-LONG decision, end-to-end.** α is a proper prefix of the output: the last α digit
/// `α[L-1] == vk` matches the output digit at position `L-1`, but the output CONTINUES with another digit
/// `d_o2 ∈ 1..4` (`out_tail = vk + m·(d_o2 + m·out_rest2)`). The comparator reaches `INV(L-1)`
/// ([`lemma_cmp_reach_inv_p`] at `p = L-1`, where `alpha_tail_above(α, L-1) == 5`), matches `vk`, switches to
/// `q_verify_end`, and the verify gap-cross reads the surviving output digit `d_o2` → `q_reject`
/// ([`lemma_cmp_toolong_round`]). Requires `n ≥ 5`, `|α| ≥ 2`.
pub proof fn lemma_cmp_decides_toolong(
    tm: Tm,
    qw: spec_fn(nat) -> nat, qc: spec_fn(nat) -> nat, qb: spec_fn(nat) -> nat, qr: nat,
    q_start: nat, q_read_boot: nat, q_verify_end: nat, q_verify_cmp: nat, q_reject: nat,
    alpha: Seq<nat>, d_o2: nat, out_rest2: nat,
)
    requires
        tm_wf(tm),
        tm.n >= 5,
        alpha.len() >= 2,
        forall|k: int| 0 <= k < alpha.len() ==> 1 <= #[trigger] alpha[k] <= 4,
        1 <= d_o2 <= 4,
        forall|V: nat| #![trigger cmp_quints_present(tm, qw, qc, qb, qr, V)]
            1 <= V <= 4 ==> cmp_quints_present(tm, qw, qc, qb, qr, V),
        has_quint(tm, mk_quint(q_start, 0, 0, q_read_boot, Dir::R)),
        has_quint(tm, mk_quint(q_read_boot, alpha[0], 5, qw(alpha[0]), Dir::L)),
        has_quint(tm, mk_quint(qr, 5, 5, q_verify_end, Dir::L)),
        has_quint(tm, mk_quint(q_verify_end, 1, 1, q_verify_end, Dir::L)),
        has_quint(tm, mk_quint(q_verify_end, 2, 2, q_verify_end, Dir::L)),
        has_quint(tm, mk_quint(q_verify_end, 3, 3, q_verify_end, Dir::L)),
        has_quint(tm, mk_quint(q_verify_end, 4, 4, q_verify_end, Dir::L)),
        has_quint(tm, mk_quint(q_verify_end, 0, 0, q_verify_cmp, Dir::L)),
        has_quint(tm, mk_quint(q_verify_cmp, 0, 0, q_verify_cmp, Dir::L)),
        has_quint(tm, mk_quint(q_verify_cmp, d_o2, d_o2, q_reject, Dir::R)),
    ensures
        tm_run(tm,
            TmConfig {
                u: dpack(alpha.subrange(0, (alpha.len() - 1) as int), tm.m)
                    + pow_nat(tm.m, (alpha.len() - 1) as nat) * (alpha[(alpha.len() - 1) as int] + tm.m * (d_o2 + tm.m * out_rest2)),
                v: dpack(alpha, tm.m) + pow_nat(tm.m, alpha.len()) * 5,
                a: 0,
                q: q_start,
            },
            (8 + cmp_loop_fuel(1, 2, (alpha.len() - 2) as nat) + (2 * (alpha.len() - 1) + 3 * alpha.len() + 6)) as nat).q == q_reject,
{
    reveal(tm_wf);
    let m = tm.m;
    assert(m > 5);
    let big_l = alpha.len();
    let p = (big_l - 1) as nat;
    let vk = alpha[(big_l - 1) as int];
    assert(1 <= vk <= 4);
    let out_tail = (vk + m * (d_o2 + m * out_rest2)) as nat;
    let c0 = TmConfig {
        u: dpack(alpha.subrange(0, p as int), m) + pow_nat(m, p) * out_tail,
        v: dpack(alpha, m) + pow_nat(m, big_l) * 5,
        a: 0,
        q: q_start,
    };
    lemma_cmp_reach_inv_p(tm, qw, qc, qb, qr, q_start, q_read_boot, alpha, p, out_tail);
    let suf_p = alpha_tail_above(alpha, p, m);
    let inv_p = cmp_inv_config(qw, alpha.subrange(0, p as int), alpha.subrange(p as int, (p + 1) as int),
        suf_p, (p + 1) as nat, out_tail, m);
    assert(tm_run(tm, c0, (8 + cmp_loop_fuel(1, 2, (p - 1) as nat)) as nat) == inv_p);

    // suf_p == 5  (p = L-1: α[L..] empty, m^0·5).
    assert(suf_p == 5) by {
        assert(alpha.subrange((p + 1) as int, big_l as int) =~= Seq::<nat>::empty());
        lemma_dpack_empty(m);
        assert((big_l - 1 - p) as nat == 0nat);
        assert(pow_nat(m, 0) == 1);
    }
    // recognize inv_p as toolong_round's entry: blk = α[0..L-1], ds_last = [vk], w = m·5+5, whi=5.
    let blk = alpha.subrange(0, p as int);
    assert(blk.len() == big_l - 1);
    assert(blk.len() >= 1);
    assert forall|k: int| 0 <= k < blk.len() implies 1 <= #[trigger] blk[k] <= 4 by { assert(blk[k] == alpha[k]); }
    let w = (m * 5 + 5) as nat;
    assert(alpha.subrange(p as int, (p + 1) as int) =~= seq![vk]) by {
        assert(alpha.subrange(p as int, (p + 1) as int).len() == 1);
        assert(alpha.subrange(p as int, (p + 1) as int)[0] == vk);
    }
    assert(cmp_above(seq![vk], 5, m) == 5) by {
        assert((seq![vk]).drop_first() =~= Seq::<nat>::empty());
        lemma_dpack_empty(m);
        assert(((seq![vk]).len() - 1) as nat == 0nat);
        assert(pow_nat(m, 0) == 1);
    }
    assert(cmp_marker(seq![vk], 5, m) == w);
    lemma_singleton_out_pregap(alpha, p, out_tail, m);
    assert(inv_p.a == pile_zeros(vk + m * (d_o2 + m * out_rest2), (p + 1) as nat, m) % m);
    assert(inv_p.u == pile_zeros(vk + m * (d_o2 + m * out_rest2), (p + 1) as nat, m) / m);
    assert(inv_p.v == dpack(blk, m) + pow_nat(m, blk.len()) * w);
    assert(inv_p.q == qw(vk));

    // extract quints + fire toolong_round.
    assert(cmp_quints_present(tm, qw, qc, qb, qr, vk));
    let ib = extract_quint(tm, mk_quint(qw(vk), 0, 0, qc(vk), Dir::L));
    let ic = extract_quint(tm, mk_quint(qc(vk), 0, 0, qc(vk), Dir::L));
    let jc = extract_quint(tm, mk_quint(qc(vk), vk, 0, qb(vk), Dir::R));
    let js = extract_quint(tm, mk_quint(qb(vk), 0, 0, qb(vk), Dir::R));
    let i1 = extract_quint(tm, mk_quint(qb(vk), 1, 1, qb(vk), Dir::R));
    let i2 = extract_quint(tm, mk_quint(qb(vk), 2, 2, qb(vk), Dir::R));
    let i3 = extract_quint(tm, mk_quint(qb(vk), 3, 3, qb(vk), Dir::R));
    let i4 = extract_quint(tm, mk_quint(qb(vk), 4, 4, qb(vk), Dir::R));
    let jj = extract_quint(tm, mk_quint(qb(vk), 5, vk, qr, Dir::R));
    let je = extract_quint(tm, mk_quint(qr, 5, 5, q_verify_end, Dir::L));
    let l1 = extract_quint(tm, mk_quint(q_verify_end, 1, 1, q_verify_end, Dir::L));
    let l2 = extract_quint(tm, mk_quint(q_verify_end, 2, 2, q_verify_end, Dir::L));
    let l3 = extract_quint(tm, mk_quint(q_verify_end, 3, 3, q_verify_end, Dir::L));
    let l4 = extract_quint(tm, mk_quint(q_verify_end, 4, 4, q_verify_end, Dir::L));
    let ibv = extract_quint(tm, mk_quint(q_verify_end, 0, 0, q_verify_cmp, Dir::L));
    let icv = extract_quint(tm, mk_quint(q_verify_cmp, 0, 0, q_verify_cmp, Dir::L));
    let jl = extract_quint(tm, mk_quint(q_verify_cmp, d_o2, d_o2, q_reject, Dir::R));
    lemma_cmp_toolong_round(tm, inv_p, qw(vk), qc(vk), qb(vk), qr, q_verify_end, q_verify_cmp, q_reject,
        blk, w, 5, vk, (p + 1) as nat, d_o2, out_rest2,
        ib, ic, jc, js, i1, i2, i3, i4, jj, je, l1, l2, l3, l4, ibv, icv, jl);
    let f3 = (2 * blk.len() + 3 * (p + 1) + 6) as nat;
    assert(tm_run(tm, inv_p, f3).q == q_reject);

    lemma_tm_run_split(tm, c0, (8 + cmp_loop_fuel(1, 2, (p - 1) as nat)) as nat, f3);
    assert((8 + cmp_loop_fuel(1, 2, (p - 1) as nat) + f3) as nat
        == (8 + cmp_loop_fuel(1, 2, (big_l - 2) as nat) + (2 * (big_l - 1) + 3 * big_l + 6)) as nat);
}

/// Helper: `cmp_out_pregap([α[p]], out_tail) == out_tail` (singleton) — so `INV(p)`'s output side is
/// `pile_zeros(out_tail, p+1)`, the form the gap-cross decision lemmas read.
pub proof fn lemma_singleton_out_pregap(alpha: Seq<nat>, p: nat, out_tail: nat, m: nat)
    requires
        m > 1,
        p < alpha.len(),
    ensures
        cmp_out_pregap(alpha.subrange(p as int, (p + 1) as int), out_tail, m) == out_tail,
{
    let ds1 = alpha.subrange(p as int, (p + 1) as int);
    assert(ds1.len() == 1);
    assert(ds1.subrange(0, (ds1.len() - 1) as int) =~= Seq::<nat>::empty());
    lemma_dpack_empty(m);
    assert(dpack(ds1.subrange(0, (ds1.len() - 1) as int), m) == 0);
    assert((ds1.len() - 1) as nat == 0nat);
    assert(pow_nat(m, 0) == 1);
    assert(cmp_out_pregap(ds1, out_tail, m)
        == dpack(ds1.subrange(0, (ds1.len() - 1) as int), m) + pow_nat(m, (ds1.len() - 1) as nat) * out_tail);
    assert(cmp_out_pregap(ds1, out_tail, m) == out_tail) by(nonlinear_arith)
        requires
            cmp_out_pregap(ds1, out_tail, m)
                == dpack(ds1.subrange(0, (ds1.len() - 1) as int), m) + pow_nat(m, (ds1.len() - 1) as nat) * out_tail,
            dpack(ds1.subrange(0, (ds1.len() - 1) as int), m) == 0,
            pow_nat(m, (ds1.len() - 1) as nat) == 1;

}

// ─────────────────────────────────────────────────────────────────────────────
// Bridge helpers (kept small to avoid trigger pollution in the main assembly).
// ─────────────────────────────────────────────────────────────────────────────

/// `dpack([x]) == x` (singleton).
pub proof fn lemma_dpack_singleton_local(x: nat, m: nat)
    ensures
        dpack(seq![x], m) == x,
{
    lemma_dpack_push(x, Seq::<nat>::empty(), m);
    lemma_dpack_empty(m);
    assert(seq![x] + Seq::<nat>::empty() =~= seq![x]);
    assert(x + m * 0 == x) by(nonlinear_arith);
}

/// **Bridge output identity.** `cmp_out_pregap(α[1..], α[L-1]+m·5, m) == dpack(α[1..]) + m^{L-1}·5`
/// (`== out_rest`): the matched output pre-gap (digits `α[1..L-2]` then `out_above = α[L-1]+m·5`) repacks
/// to the full reversed-output tail `α[1..L-1]` with the far `5` sentinel above.
pub proof fn lemma_bridge_out_pregap(alpha: Seq<nat>, out_above: nat, out_rest: nat, m: nat)
    requires
        m > 5,
        alpha.len() >= 2,
        forall|k: int| 0 <= k < alpha.len() ==> 1 <= #[trigger] alpha[k] <= 4,
        out_above == alpha[(alpha.len() - 1) as int] + m * 5,
        out_rest == dpack(alpha.drop_first(), m) + pow_nat(m, (alpha.len() - 1) as nat) * 5,
    ensures
        cmp_out_pregap(alpha.subrange(1, alpha.len() as int), out_above, m) == out_rest,
{
    let big_l = alpha.len();
    let ds = alpha.subrange(1, big_l as int);
    assert(ds.len() == big_l - 1);
    // ds.subrange(0, L-2) == alpha[1..L-1]; matches dpack(α[1..L-1]) less the last digit.
    let t = ds.subrange(0, (ds.len() - 1) as int);              // α[1..L-2]
    assert(t.len() == big_l - 2);
    assert(t =~= alpha.subrange(1, (big_l - 1) as int)) by {
        assert forall|i: int| 0 <= i < big_l - 2 implies t[i] == alpha.subrange(1, (big_l - 1) as int)[i] by {
            assert(t[i] == ds[i]);
            assert(ds[i] == alpha[i + 1]);
            assert(alpha.subrange(1, (big_l - 1) as int)[i] == alpha[i + 1]);
        }
    }
    // dpack(α[1..L-1]) == dpack(α[1..L-2]) + m^{L-2}·α[L-1]   (peel the high digit).
    let af = alpha.drop_first();                                // α[1..L-1]  (length L-1)
    assert(af.len() == big_l - 1);
    assert(af.subrange(0, (big_l - 2) as int) =~= t) by {
        assert forall|i: int| 0 <= i < big_l - 2 implies af.subrange(0, (big_l - 2) as int)[i] == t[i] by {
            assert(af.subrange(0, (big_l - 2) as int)[i] == af[i]);
            assert(af[i] == alpha[i + 1]);
            assert(t[i] == alpha[i + 1]);
        }
    }
    assert(af[(big_l - 2) as int] == alpha[(big_l - 1) as int]);
    assert forall|i: int| 0 <= i < af.len() implies #[trigger] af[i] < m by { assert(af[i] == alpha[i + 1]); }
    lemma_dpack_high_peel(af, m);                               // dpack(af) == dpack(af[0..n-1]) + m^{n-1}·af[n-1]
    assert((af.len() - 1) as nat == (big_l - 2) as nat);
    // dpack(af) == dpack(t) + m^{L-2}·α[L-1]  (high peel + the =~= identities).
    assert(dpack(af.subrange(0, (af.len() - 1) as int), m) == dpack(t, m));
    assert(dpack(af, m) == dpack(t, m) + pow_nat(m, (big_l - 2) as nat) * alpha[(big_l - 1) as int]);
    lemma_pow_nat_unfold(m, (big_l - 1) as nat);               // m^{L-1} == m·m^{L-2}
    // cmp_out_pregap(ds, out_above) == dpack(t) + m^{L-2}·out_above.
    assert((ds.len() - 1) as nat == (big_l - 2) as nat);
    assert(cmp_out_pregap(ds, out_above, m) == dpack(t, m) + pow_nat(m, (big_l - 2) as nat) * out_above);
    assert(cmp_out_pregap(ds, out_above, m) == out_rest) by(nonlinear_arith)
        requires
            cmp_out_pregap(ds, out_above, m) == dpack(t, m) + pow_nat(m, (big_l - 2) as nat) * out_above,
            out_above == alpha[(big_l - 1) as int] + m * 5,
            dpack(af, m) == dpack(t, m) + pow_nat(m, (big_l - 2) as nat) * alpha[(big_l - 1) as int],
            pow_nat(m, (big_l - 1) as nat) == m * pow_nat(m, (big_l - 2) as nat),
            out_rest == dpack(af, m) + pow_nat(m, (big_l - 1) as nat) * 5;
}

/// `[α[0]] + α[1..L-1] == α[0..L-1]` (re-attach the head onto the matched-prefix tail).
pub proof fn lemma_bridge_blk(alpha: Seq<nat>, m: nat)
    requires
        alpha.len() >= 2,
    ensures
        seq![alpha[0]] + alpha.subrange(1, alpha.len() as int).subrange(0, (alpha.len() - 2) as int)
            =~= alpha.subrange(0, (alpha.len() - 1) as int),
{
    let big_l = alpha.len();
    let ds = alpha.subrange(1, big_l as int);
    let inner = ds.subrange(0, (big_l - 2) as int);
    let lhs = seq![alpha[0]] + inner;
    let rhs = alpha.subrange(0, (big_l - 1) as int);
    assert(lhs.len() == big_l - 1);
    assert(rhs.len() == big_l - 1);
    assert forall|i: int| 0 <= i < big_l - 1 implies lhs[i] == rhs[i] by {
        if i == 0 {
            assert(lhs[0] == alpha[0]);
            assert(rhs[0] == alpha[0]);
        } else {
            assert(lhs[i] == inner[i - 1]);
            assert(inner[i - 1] == ds[i - 1]);
            assert(ds[i - 1] == alpha[i]);
            assert(rhs[i] == alpha[i]);
        }
    }
}

/// **High-digit peel of `dpack`.** `dpack(s) == dpack(s[0..n-1]) + m^{n-1}·s[n-1]` for `s.len() == n ≥ 1`.
pub proof fn lemma_dpack_high_peel(s: Seq<nat>, m: nat)
    requires
        m > 1,
        s.len() >= 1,
        forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] < m,
    ensures
        dpack(s, m) == dpack(s.subrange(0, (s.len() - 1) as int), m)
            + pow_nat(m, (s.len() - 1) as nat) * s[(s.len() - 1) as int],
    decreases s.len(),
{
    let n = s.len();
    if n == 1 {
        assert((s.len() - 1) as int == 0int);
        assert(s.subrange(0, (s.len() - 1) as int) =~= Seq::<nat>::empty());
        lemma_dpack_empty(m);
        assert(dpack(s.subrange(0, (s.len() - 1) as int), m) == 0);
        assert((s.len() - 1) as nat == 0nat);
        assert(pow_nat(m, 0) == 1);
        assert(pow_nat(m, (s.len() - 1) as nat) == 1);
        assert(dpack(s, m) == s[0]) by { lemma_dpack_singleton_local(s[0], m); assert(s =~= seq![s[0]]); }
        // postcondition: dpack(s) == 0 + 1·s[n-1] == s[0].
        assert(s[(s.len() - 1) as int] == s[0]);
    } else {
        // peel the low digit, recurse on the tail.
        lemma_dpack_pop(s, m);                                  // dpack(s) == s[0] + m·dpack(s.drop_first())
        let r = s.drop_first();
        assert(r.len() == n - 1);
        assert forall|i: int| 0 <= i < r.len() implies #[trigger] r[i] < m by { assert(r[i] == s[i + 1]); }
        lemma_dpack_high_peel(r, m);                            // dpack(r) == dpack(r[0..n-2]) + m^{n-2}·r[n-2]
        assert(r[(r.len() - 1) as int] == s[(n - 1) as int]);
        // s.subrange(0, n-1) == [s[0]] + r.subrange(0, n-2).
        let sl = s.subrange(0, (n - 1) as int);
        assert(sl =~= seq![s[0]] + r.subrange(0, (r.len() - 1) as int)) by {
            assert forall|i: int| 0 <= i < n - 1 implies
                sl[i] == (seq![s[0]] + r.subrange(0, (r.len() - 1) as int))[i] by {
                if i == 0 {
                    assert(sl[0] == s[0]);
                } else {
                    assert(sl[i] == s[i]);
                    assert((seq![s[0]] + r.subrange(0, (r.len() - 1) as int))[i] == r.subrange(0, (r.len() - 1) as int)[i - 1]);
                    assert(r.subrange(0, (r.len() - 1) as int)[i - 1] == r[i - 1]);
                    assert(r[i - 1] == s[i]);
                }
            }
        }
        assert(sl[0] == s[0]);
        lemma_dpack_pop(sl, m);                                 // dpack(sl) == s[0] + m·dpack(r.subrange(0,n-2))
        assert(sl.drop_first() =~= r.subrange(0, (r.len() - 1) as int));
        lemma_pow_nat_unfold(m, (n - 1) as nat);               // m^{n-1} == m·m^{n-2}
        assert((n - 2) as nat == (r.len() - 1) as nat);
        assert(dpack(s, m) == dpack(sl, m) + pow_nat(m, (n - 1) as nat) * s[(n - 1) as int])
            by(nonlinear_arith)
            requires
                dpack(s, m) == s[0] + m * dpack(r, m),
                dpack(r, m) == dpack(r.subrange(0, (r.len() - 1) as int), m)
                    + pow_nat(m, (r.len() - 1) as nat) * s[(n - 1) as int],
                dpack(sl, m) == s[0] + m * dpack(r.subrange(0, (r.len() - 1) as int), m),
                pow_nat(m, (n - 1) as nat) == m * pow_nat(m, (r.len() - 1) as nat);
    }
}

} // verus!
