# GAP-2 G2-F — the input-loader / relator-decider plan (discharge `ceer_realizes`)

*Live design doc for the FINAL GAP-2 brick: building the modular machine `mm` so that
`(α,0) ∈ H₀(mm) ⟺ α is the word-number of a declared family relator`, which discharges
`ceer_realizes` (`ceer_relator_match.rs:81`) and lets `ceer_fp_conditional` drop
`axiom_ceer_fp_embedding` (`ceer_benign.rs:67`). Co-designed with Danielle (port 8051), 2026-06-26.*

---

## 0. Where we are

`lemma_rm_k_halts_iff_mm_in_H0` (`godel_modular.rs`) is done: for any `machine_wf` RM(k) and
`config_wf` config `c_k`,

```
  (∃f. run_halts(rm_k, c_k, f))  ⟺  mm_in_H0(tm_to_modmachine(rm_to_tm(rm_k_to_rm2(rm_k))),
                                              rep1(ctm, tm.m).0, rep1(ctm, tm.m).1)
```

`lemma_search_rm_halts_iff` (`search_rm_outer.rs:643`) is done:
`halts(search_rm(e), pair(a,b)) ⟺ declared_equiv(e,a,b)`.

The conditional chain `lemma_ceer_word_problem_in_h3` (`ceer_fp_conditional.rs`) stands, gated only on
`ceer_realizes`. Layer 1 + Layer 2 (the Higman embedding `C ↪ H₃`, faithful + sound for the printable
`h3_pres`) are machine-checked.

## 1. The crux (why this is the Big Brick, not wiring)

The Cohen consumer is hardcoded to the **`(α,0)` input convention**:
`is_S_canonical(mm,n,m)(w) = ∃α. numbers_word(n,m,α) ∧ mm_in_H0(mm,α,0) ∧ w==w_c(c_base(nk),n,m,α)`,
and `s_realizes` / the whole `cohen_cs5_recog.rs` faithfulness engine derive **`(α,0) ∈ H₀`** from the
group structure (recognition peels `p`, hits `lemma_theorem1`: `[k,t(α,0)]=1 ⟺ (α,0)∈H₀`). So:

- **β=0 is load-bearing**, not a knob. `is_S` *must* stay keyed on `(α,0)∈H₀` (the recognition's output).
  Re-keying it (Route B) is either unsound or relocates to the identical loader bridge
  `(α,0)∈H₀ ⟺ rep1(ctm_α)∈H₀`. No convention shim exists.
- **α is exponential in (a,b).** `miller_collapse_word(j)` has length Θ(j) (it is
  `t·(b⁻¹)ⁱ·a·(b)ⁱ·t⁻¹·a⁻ⁱ·b⁻¹·aⁱ`, `i=j+1`, `b=tat⁻¹`), so `g_a g_b⁻¹` collapses to a {a,t}-word of
  length L=Θ(a+b), and its word-number α has L base-m digits ⟹ α ∈ [m^{L-1}, m^L). Recovering (a,b)
  from α is a base-m digit traversal — a **mandatory variable-length loop**, never a constant shim.
- **`quint_wf` forbids state-0 firing.** `quint_wf` requires `n+1 ≤ qt.q < m` for every quintuple's
  current state. This is exactly what keeps `tm_origin()=(0,0,0,0)` (state 0) terminal — load-bearing
  for the whole H₀ reduction (`lemma_origin_tm_terminal`). Consequence: **no `tm_wf` TM can take a step
  from a state-0 config.** A config `(α,0)` has β-residue 0 = state 0, so it is terminal in *any*
  `tm_to_modmachine(tm)`. Hence the `(α,0)→running` transition cannot come from a TM; it must be **raw
  modular-machine quads with `b=0`**.

So discharging `ceer_realizes` genuinely requires the Aanderaa–Cohen "input-loading" content. The
existing RM→TM→ModMachine pipeline only gives the rep1-form *run* half (states ≥ n+1).

## 2. The architecture — minimal ignition + a parser/search/cleanup TM

The (α,0)→running transition needs raw `b=0` quads, but it can be **minimal**: a fixed handful of
**ignition quads** that take one residue step out of `b=0` into a real running state, after which a
normal `tm_wf` TM does all the work.

```
  mm = ignition_quads  ++  tm_to_modmachine(psc_tm(e))
```

### 2.1 Ignition (the only raw modmachine quads)

The origin `(0,0)` has α-residue 0. A valid nonzero word-number α has lowest digit
`α mod m ∈ 1..2n_word = 1..4` (from `numbers_word`). So an ignition quad keyed on residue `(i, 0)` for
`i ∈ {1,2,3,4}` **fires on `(α,0)` but never on the origin** — `mm_terminal(mm,0,0)` is preserved.

One **L-direction** ignition quad per digit `i`:
`quad_step(L, (i,0)) = (α/m, (0/m)·m² + c_i) = (α/m, c_i)`. Pick `c_i = q_startᵢ`, a running start
state (≥ n+1) that remembers the consumed digit `i`. After ignition the config is `(α/m, q_startᵢ)`,
which is exactly `rep1(c1)` of the TM config
`c1 = { u: α/m², v: 0, a: (α/m) mod m, q: q_startᵢ }` — a normal running config scanning α's 2nd digit,
left tape = the rest of α, right tape empty. (4 ignition quads total. Determinism: their `b=0` never
collides with TM-sim quads, whose `b=q ≥ n+1`.)

### 2.2 `psc_tm(e)` — the parser/search/cleanup TM (`tm_wf`, the bulk)

A fresh `tm_wf` TM with **alphabet `n ≥ 4`** (to hold the four c-block relator letters as tape symbols)
and **modulus `m` = the word-numbering modulus** (so the machine reads α's digits in the right base;
see §3). From `c1` it:

- **(P) Parse.** Read α's base-m digits off the left tape (the ρ-relabeled c-block image of
  `collapse(g_a g_b⁻¹) = t⁻ᵃ a tᵃ · t⁻ᵇ a⁻¹ tᵇ`), recover `(a,b)` by counting the `t`-run lengths,
  and **reject** any α not of declared-relator shape (a non-relator α must lead to a non-origin
  terminal / non-halting, i.e. `(α,0) ∉ H₀`). Output `(a,b)` in the format the search phase consumes.
- **(S) Search.** Run the `search_rm(e)` dovetail on `(a,b)` — halts iff `declared_equiv(e,a,b)`.
- **(C) Cleanup.** On halt, empty both tapes and land on `tm_origin() = (0,0,0,0)`.

Headline target:
`tm_halts_at(psc_tm(e), c1_for_α, tm_origin()) ⟺ α is the word-number of a declared family relator`,
chained through ignition to `mm_in_H0(mm, α, 0) ⟺ α declared word-number`.

## 3. Modulus & alphabet reconciliation

- `ceer_realizes(e, mm, m)` exposes `m` (the word-numbering modulus, `2·2 < m`) and `mm` (machine,
  `mm.m` = machine modulus). For `mm_in_H0(mm, α, 0)` to read α's word-number digits correctly we need
  **`mm.m = m`** (machine modulus = word-numbering modulus). `m` is a free parameter in `ceer_realizes`,
  so we **choose** it = `psc_tm(e).m`.
- Word-number digits ∈ 1..4 ⟹ scanned symbol up to 4 ⟹ **`psc_tm(e).n ≥ 4`** (`tm_config_wf` wants
  `c.a ≤ n`, `digits_le(u,m,n)`). `tm_wf` needs `0 < n < m`, so pick `m > n` (e.g. `m = ` the natural
  `tm_mod`-style value of `psc_tm`, which is ≫ n).
- The 2-counter search gadgets use symbols {0,1,2}; with `n ≥ 4` they remain valid (symbols ≤ n). Must
  confirm the gadget lemmas are **alphabet-monotone** (parametric in `n`, not pinned to n=2) — see §6.

## 4. Wiring to `ceer_realizes` (after the machine is built)

1. **`config_encode`/`rm_modulus`/`ceer_to_modmachine`** in `modular_reduction.rs` get the real bodies:
   `ceer_to_modmachine(e) = mk_mm(ignition_quads, tm_to_modmachine(psc_tm(e)))`; `enc(a,b) =` the
   word-number `decode_word(cb_of(mm),2,m,ρ(family relator for (a,b)))`; `rm_modulus`/`m = psc_tm(e).m`.
2. **`lemma_ceer_modmachine_wf`** — `mod_machine_wf(mm)`: TM-sim part via `lemma_tm_modmachine_wf`, plus
   the 4 ignition quads (wf: `i<m`, `0<m`, `c_i<m²`; determinism vs TM-sim by disjoint `b`).
3. **The machine-content lemma** `mm_in_H0(mm, α, 0) ⟺ α is a declared relator word-number`:
   - ignition one-step `(α,0) → rep1(c1)` (manual, 4 cases);
   - a **frame/extension lemma**: ignition quads never fire on TM-sim configs (`b=q≥n+1≠0`), so the
     combined `mm` and `tm_to_modmachine(psc_tm(e))` agree on the TM-sim trajectory ⟹ transport
     `lemma_tm_h0_iff` to the combined machine;
   - `psc_tm(e)` halts-iff (P∘S∘C correctness) ∘ `lemma_search_rm_halts_iff`.
4. **Bridge to the family-relator form** (the existing `ceer_realizes` FWD/BWD over
   `decode_word(cb,2,m,ρ(r))`): a declared family relator `r` ↔ a declared pair `(a,b)` ↔ its
   word-number α_r; "α is a declared relator word-number" ⟺ "∃ family relator r, α=α_r". Uses the GAP-1
   word-numbering decode bridge (B1, already proven: `lemma_decode_section`,
   `lemma_relabel_image_c_alphabet`). FWD = §2's machine accepts α_r; BWD = exactness of the parser
   (only declared-relator-shaped α land in H₀).
5. Drop `axiom_ceer_fp_embedding`: feed `ceer_realizes` into `lemma_ceer_word_problem_in_h3` to build the
   explicit `(p=h3_pres, emb)`; rewrite `lemma_ceer_embeds_in_fp_group_main` to use it.

## 5. Brick sequence (proposed)

- **B-IG** — ignition quads + `mk_mm` constructor + `mod_machine_wf` (the 4-quad determinism/frame).
- **B-FR** — the frame/extension lemma (machine-extension preserves the no-`b=0` trajectory; transport
  `lemma_tm_h0_iff`). *Generic, reusable; build early to de-risk.*
- **B-AL** — alphabet-monotone gadget audit / re-parametrize `rm_to_tm` + gadgets to `n ≥ 4`
  (or a thin n-generic wrapper). *Gating for P and S.*
- **B-P** — the parser TM: base-m relator-word digits → `(a,b)`, with the reject branch. The genuinely
  new sub-machine. Sub-bricks: digit-classifier, t-run counter (→ a, b), shape-validator/reject.
- **B-S** — the search phase: re-realize `search_rm(e)` (or `rm_to_tm` of it) in the `n≥4`, `m=psc.m`
  TM, fed the parser's `(a,b)` output. Reuse `lemma_search_rm_halts_iff` for the semantics.
- **B-C** — cleanup to origin (mirror `tm_cleanup.rs`).
- **B-PSC** — assemble P∘S∘C into `psc_tm(e)` + the halts-iff (mirror `tm_run_sim.rs`).
- **B-MC** — the machine-content lemma (§4.3): ignition ∘ frame ∘ `lemma_tm_h0_iff` ∘ B-PSC.
- **B-W** — the family-relator bridge (§4.4) + fill `modular_reduction.rs` + drop the axiom (§4.5).

## 6. Open sub-design questions (for Danielle before / during coding)

1. **Ignition as raw quads — OK?** Your D1 "go" assumed a clean AC-convention TM, which `quint_wf`
   forbids. The minimal-ignition design (4 raw `b=0` quads + a normal TM) is the smallest faithful
   residue-arithmetic footprint. Confirm this shape.
2. **Parser-on-tape vs decode-in-RM.** The parser must read α-as-tape (base-m digits) — it cannot be an
   ordinary `rm_to_tm`(RM) because RM input is unary-repunit, not base-m tape digits. So B-P is a
   genuinely new TM. Alternative: a *modmachine* loader loop that base-m→unary converts α before the
   existing `rm_to_tm` search — but that's MORE residue arithmetic. Lean: B-P (TM parser). Confirm.
3. **Alphabet genericity (B-AL).** Are `tm_inc/tm_dec/tm_walk/...` lemmas parametric in `n`, or pinned
   to n=2 (`rm_to_tm` sets `n:2` literally)? If pinned, B-AL is a re-parametrization pass (mechanical
   but broad). Worth auditing the cost before committing.
4. **Reject-branch semantics.** A non-relator-shaped α must give `(α,0) ∉ H₀` (non-origin terminal or
   non-halting). Cleanest: the parser detects malformed structure and enters a non-origin self-loop /
   dead state. Confirm this is acceptable (it must never accidentally reach origin).

## 7. What's reusable vs new

- **Reusable:** `tm.rs`/`tm_modular.rs`/`tm_h0*.rs` framework; `lemma_tm_h0_iff` (generic over `tm_wf`);
  `lemma_tm_modmachine_wf`; `search_rm` + `lemma_search_rm_halts_iff` (logic/semantics);
  `tm_cleanup.rs` pattern; the GAP-1 decode bridge (`lemma_decode_section`,
  `lemma_relabel_image_c_alphabet`); the conditional chain `lemma_ceer_word_problem_in_h3`.
- **New:** ignition quads + `mk_mm`; the frame/extension lemma; the alphabet-≥4 gadget layer; the
  base-m relator-word parser TM (with reject); the `psc_tm` assembly; the machine-content + family
  bridge.

---

*Status: PLAN — awaiting Danielle's confirm on §6 before coding. The conditional chain already stands;
this brick removes the last axiom.*
