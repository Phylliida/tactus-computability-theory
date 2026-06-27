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

### 2.2 `psc_tm(e)` — the read/search/cleanup TM (`tm_wf`, the bulk)

**Design decision (Danielle, 2026-06-26): GENERATE-AND-COMPARE, not parse-and-extract.** Parsing the
Miller collapse image `collapse(g_a g_b⁻¹)` off the tape (counting nested `b=tat⁻¹` blocks to recover
`a,b`, finding the `g_a | g_b⁻¹` boundary, + a reject branch for non-relator α) is a heavy structural
parser with a large verify burden. Instead the machine only ever uses the **forward** map
`relnum(a,b) := word-number of ρ(collapse(g_a g_b⁻¹))` (a fixed, primitive-recursive computation) and
*compares*. This deletes the reject branch entirely: a non-relator α simply never matches any candidate,
so the machine diverges — which is exactly "α ∉ H₀". This mirrors a CEER's natural semantics (halt iff
in the set; permitted to diverge otherwise) and reuses the existing `search_rm` dovetail skeleton.

A fresh `tm_wf` TM with **alphabet `n ≥ 4`** (to hold the four c-block relator letters as tape symbols)
and **modulus `m` = the word-numbering modulus** (so the machine reads α's digits in the right base;
see §3). From `c1` it:

- **(P) Read.** A simple base-`m` *read loop* (NOT a structural parser): fold α's tape digits back into
  a register value `R_α`. Reuses counter arithmetic (×m + digit). [Option (i), Danielle's pick — keeps
  the heavy lifting in the RM domain; avoids per-candidate tape rescans.]
- **(S) Search (generate-and-compare).** Dovetail over stages `s`: run `enumerator(s)` → `(a,b)` (if it
  halts); compute `relnum(a,b)`; halt iff `relnum(a,b) == R_α`. Halts iff `α` is the word-number of a
  declared family relator. Reuses the `search_rm(e)` dovetail structure with the predicate
  `declared_match(s, ·)` swapped for `relnum(declared_pair(s)) == R_α`. `relnum` is a forward
  primitive-recursive sub-machine (fixed-count collapse loops `a+1`/`b+1` + base-`m` digit-pack).
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

- **B-AL** ✅ **DONE (audit)** — the tm gadget lemmas (`lemma_inc`/`lemma_dec`/`lemma_walk`/…) require
  only `tm.n >= 2` and take quint *indices* as parameters, so they are **alphabet-monotone** and reuse
  verbatim at `n ≥ 4`. Only `rm_to_tm`'s assembly hardcodes `n:2` (`tm_assemble.rs:268`); a fresh
  `n≥4` assembly will reuse the gadget lemmas. So B-AL is a re-assembly, *not* a gadget rewrite.
- **B-FR** ✅ **DONE (`gap2_ignition.rs`, part of 12/0).** The frame/extension lemmas: appending
  ignition quads (`b=0, a≠0`) is inert on the running region (`β%m ≠ 0`). `mm_extend`,
  `lemma_yields_mono`, `lemma_mm_extend_reaches_mono`, `lemma_combined_yields_eq` (the two machines
  yield identically off `β%m=0`), `lemma_mm_extend_terminal` (origin stays terminal), `lemma_origin_
  reaches_zero`, and the headline `lemma_frame_reaches` (combined→base reachability under the running-
  region invariant). Crate 650/0.
- **B-IG** ✅ **DONE (`gap2_ignition.rs`, part of 12/0).** Concrete ignition: `ignition_quad(i,qs)` =
  `{a:i,b:0,c:qs,dir:L}`; `ignition_quads(ndig,start)` (one per digit `1..=ndig`).
  `lemma_ignition_quads_shape` (feeds B-FR), `lemma_ignition_yields` (`(α,0) → (α/m, start(α%m)) =
  rep1(c1)` for `1 ≤ α%m ≤ ndig`), `lemma_mm_extend_wf` (combined `mod_machine_wf` given base wf +
  `start(i)<m` + `ndig<m` + base quads carry `b≠0`). **The ignition layer is COMPLETE.** Crate 654/0.
- **B-P** — the **read loop** (generate-and-compare design, §2.2): fold α's base-m tape digits into a
  register value `R_α`. A simple read loop, NOT a structural parser (the parse-and-extract route with
  its reject branch is RETIRED per Danielle). *Couples with the ignition handoff states `start(i)` =
  the read loop's per-digit entry states (B-IG left `start` abstract for exactly this).* Needs the new
  `n≥4` TM assembly scaffolding first (B-AL re-assembly). **← next.**
- **B-relnum (spec target)** ✅ **DONE (`gap2_relnum.rs`, 2026-06-26, crate 661/0).** `relnum(e,mm,m,a,b)`
  = `decode_word(cb,2,m, ρ(fam_relator(a,b)))`, with `fam_relator(a,b)` the canonical collapsed family
  relator (Miller collapse of `[Gen(a),Inv(b)]` at the minimal slice). The **family-relator ↔
  declared-pair set-equality** is proven both ways: `lemma_fam_relator_from_dbar` (a nonempty
  `dbar_union_pred(ceer_decls_fam(e),·)` relator comes from a declared pair) + `lemma_dbar_from_declared`
  (every declared pair contributes its `fam_relator`), sharing `lemma_dbar_slice_is_fam_relator`
  (slice-independence of the collapse). The *forward RM sub-machine* half of B-relnum (computing relnum
  in-machine) is MACHINE work, still open — gated on the architecture call below.
- **B-W (assembly half)** ✅ **DONE (`gap2_relnum.rs`, 2026-06-26).** `lemma_ceer_realizes_from_machine`
  discharges `ceer_realizes` from the **abstract machine contract** `mm_decides_relnum(e,mm,m)` (FWD: a
  declared pair `(a,b)` ⟹ `relnum(a,b)∈H₀`; BWD: a nonzero word-number in `H₀` is some declared pair's
  `relnum`). The `ceer_realizes` BWD `r≠ε` clause is free (`α≠0` ⟹ `decode_word(cb,2,m,ρ(ε))=0≠α`, via
  `lemma_rho_empty`). **This isolates the ENTIRE remaining GAP-2 obligation to building a machine
  satisfying `mm_decides_relnum` — architecture-independent (TM read-loop OR modmachine prefix).**
- **B-S** — the dovetail search (generate-and-compare): reuse the `search_rm(e)` skeleton with predicate
  `relnum(declared_pair(s)) == R_α` in place of `declared_match`. Halts iff α is a declared relator
  word-number. No reject branch (non-relator ⟹ diverges).
- **B-C** — cleanup to origin (mirror `tm_cleanup.rs`).
- **B-PSC** — assemble P∘S∘C into `psc_tm(e)` + the halts-iff (mirror `tm_run_sim.rs`).
- **B-MC** — the machine-content lemma (§4.3): `lemma_ignition_yields` (1 step) ∘ `lemma_frame_reaches`
  + `lemma_mm_extend_reaches_mono` (both H0 directions) ∘ `lemma_tm_h0_iff` (on `psc_tm`) ∘ B-PSC.
  The B-FR/B-IG interface is built precisely to make this a splice. **Now retargets `mm_decides_relnum`
  (B-W's contract), not `ceer_realizes` directly.**
- **B-W (machine wiring)** — fill `modular_reduction.rs` placeholders with the real machine + prove
  `mm_decides_relnum` (B-MC ∘ B-PSC ∘ B-S ∘ B-relnum-submachine) + drop the axiom via
  `lemma_ceer_word_problem_in_h3` (§4.5). The assembly bridge (above) is already done.

> **✅ ARCHITECTURE RESOLVED (2026-06-26, port 8051): ROUTE (i)** — a bespoke **n≥4 `tm_wf` TM**
> `psc_tm(e)`, base-m native. Route (ii) (modmachine prefix → n=2 pipeline) was rejected after a code
> dive surfaced two facts that killed its "verbatim reuse" premise:
>
> - **FACT 1 (ignition is already route-(i)-shaped).** `lemma_ignition_yields` steps
>   `(α,0) → (α/m, start(i))`, and `rep1`'s definition confirms `(α/m, start(i)) = rep1(c1)` with
>   `c1 = {u: α/m², v: 0, a: (α/m)%m, q: start(i)}` — a TM config **scanning α's base-m digits**, α's
>   higher digits on the left tape. The scanned symbol `(α/m)%m ∈ 1..4` (from `numbers_word`), so the
>   consumer needs **n ≥ 4**. The built ignition lands exactly in a route-(i) reading config, bridged
>   by the GENERIC `lemma_tm_h0_iff(tm, ctm)`. There is no RM-initial-config landing spot (c1's scanned
>   symbol is a generic digit, not `sep()=2` + a start state).
> - **FACT 2 (the n=2 pipeline input is a 2^α blow-up).** `rm2_config_enc(instrs, c_k).registers[0] =
>   godel_encode(c_k.registers) = 2^α` for input α; then `rm_config_enc = two_counter_config(2^α, 0, …)`
>   with `u = repunit_m(2^α, m)` — a tape of **2^α ones**. So feeding α into `rm_to_tm(search_rm)`
>   "verbatim" needs the read loop to build `repunit_m(2^α, m)`: an **exponential** raw-quad expansion,
>   not a simple `R←R·m+d` fold. Route (ii)'s cost premise ("reuse n=2 stack verbatim, cost = prefix
>   residue arithmetic") is false — the prefix is itself a 2^α dragon.
>
> **The deeper point:** α and `relnum(a,b)` are BOTH base-m word-numbers (`relnum` IS the base-m number
> whose digits are the collapsed relator's symbols). Comparing them is natural in base-m (digit-by-digit)
> and unnatural through a unary/Gödel bottleneck. The problem is base-m-native; an n≥4 TM fits it; the
> n=2 unary pipeline is what creates the expansion dragon.
>
> **Alphabet-monotone audit — CONFIRMED.** Every TM gadget lemma (`lemma_inc`/`lemma_dec`/
> `lemma_peek_gadget`/`lemma_bounce_*`/`lemma_*_right`/walk) requires `tm_wf(tm)` **+ `tm.n >= 2`**
> (never `n == 2`), taking quint indices as params. The n≥4 assembly REUSES them — only new content is
> read gadgets distinguishing digit-symbols 3,4. Only `rm_to_tm` (tm_assemble.rs:265) hardcodes `n:2`;
> the n≥4 re-assembly is "widen the pipe", not a gadget rewrite.

### Route (i) brick plan (the build)

`mm = ignition_quads ++ tm_to_modmachine(psc_tm(e))`, `psc_tm(e)` a single **n≥4 `tm_wf` TM**:

- **R-AL — the n≥4 assembly foundation.** An n≥4 analog of `rm_to_tm`'s `Tm` constructor (or a
  parametric `n`); prove `tm_wf` and the per-gadget step lemmas go through at `n=4` by reusing the
  alphabet-monotone gadget lemmas. **← first brick (smallest, unblocks everything).**
- **R-P — the read phase.** From `c1` (scanning α's digits), consume α's base-m digits off the left
  tape. New read/peek gadgets distinguish symbols `1..4`. (Design sub-choice: keep α as base-m digits
  on a dedicated tape region for digit-by-digit compare — do NOT fold into a unary counter, which
  reintroduces the expansion. Stay base-m native.)
- **R-relnum-gen — generate relnum(a,b)'s base-m digits.** For an enumerated declared `(a,b)`, emit the
  digits of `relnum(a,b)` = the symbols of the collapsed Miller relator `ρ(collapse(g_a g_b⁻¹))`
  (length Θ(a+b); `t·(b⁻¹)ⁱ·a·(b)ⁱ·t⁻¹·a⁻ⁱ·b⁻¹·aⁱ`, `i=j+1`, `b=tat⁻¹`). Loop control via counters
  (symbols 1,2). Follow the collapse definition exactly — do not reinvent.
- **R-cmp — digit-by-digit base-m compare** of the generated relnum digits against α's stored digits.
- **R-S — the dovetail search.** Enumerate stages `s`, `(a,b)=declared_pair(e,s)`, run R-relnum-gen +
  R-cmp, halt iff match. Mirror the `search_rm(e)` dovetail STRUCTURE (re-expressed as n≥4 TM gadgets).
- **R-C — cleanup to origin** (mirror `tm_cleanup.rs`).
- **R-MC — the machine-content lemma**: `lemma_ignition_yields` (1 step) ∘ `lemma_frame_reaches` ∘
  `lemma_tm_h0_iff(psc_tm)` ∘ R-S halts-iff ⟹ `mm_decides_relnum`. Then `lemma_ceer_realizes_from_machine`.

Build with Shepherdson–Sturgis (`ComputabilityOfRecursiveFunctions.pdf`, crate root) compositional
style; reuse `multi_output_machine`/`multi_output_primitives` for any RM-core. B-relnum-spec/B-W-assembly
(`gap2_relnum.rs`) and the ignition layer (`gap2_ignition.rs`) STAND (machine-independent / done).

### AC-grounded design (Aanderaa–Cohen, *Modular Machines I*, 1980, pp. 3–4)

Read from the source PDF (`tactus-group-theory/[…] WORD -- Aanderaa, Stål […].pdf`, text-extractable
via `nix-shell -p poppler-utils`). The paper pins the input/output/H₀ conventions — **follow them, do
not reinvent**:

- **Input function** `iM(r) = (Σ bᵢmⁱ, n+1)` where `r = Σ bᵢnⁱ`, digits `bᵢ ∈ 1..n` (**bijective
  base-n**, no zero digit). So a number's bijective-base-n digits become α's base-m digits; the machine
  **starts in state n+1** scanning the low digit `b₀`, higher digits on the left tape `u`, right tape
  `v=0`. This is `rep1` of `{u: r's higher digits, v:0, a: b₀, q: n+1}`. (Our ignition lands one digit
  further in — `c1` scans `b₁`, with `b₀` in `start(i)` — an equivalent running config.)
- **It is a STANDARD single-tape TM** computing directly on the base-m input. The "two stacks" `u,v` are
  just left/right of the head — there is no 2-stack-cramming puzzle, no register-fold, no unary/Gödel
  expansion. Unbounded dovetail counters (`s,a,b,i`) are ordinary tape regions; finite control is `q`.
- **Output/halt convention**: `fT(r)=s` if T started in state `n+1` on the input halts with output `s`;
  "we may modify T so that whenever it halts the scanned square is blank." For a **decider** (char.
  function of an r.e. set), T **halts-on-blank iff input ∈ S** — exactly our generate-and-compare.
- **H₀ realization** (p.4): for any r.e. `S`, a TM `T` halting-on-blank iff input ∈ S gives
  `H₀(tm_to_modmachine(T))` realizing `S`. Here `S = { relnum(a,b) : (a,b) declared }`; psc_tm is that
  decider. Bridges to `mm_decides_relnum` via the generic `lemma_tm_h0_iff` + ignition `(α,0)→(α,n+1)`.

**Consequence for the build**: psc_tm is a *standard TM program* (input on tape + scratch regions +
finite control), so the existing gadget library (peek/inc/dec/walk/bounce, all `tm.n>=2`-monotone) and
the `search_rm` dovetail TEMPLATE apply directly. The single deep brick is **R-relnum-gen**: emit the
collapsed Miller relator `ρ(fam_relator(a,b))`'s symbols as base-m digits and prove they equal
`decode_word(cb,2,m,ρ(fam_relator(a,b)))` — the group-theory↔machine bridge. Everything else
(read/compare/dovetail/cleanup) is standard TM gadget work over the AC tape model. **Modulus/alphabet
(§3)**: choose `n ≥ 4` (digits `1..4`) and `m = psc_tm`'s modulus `= the word-numbering modulus`.

### R-relnum-gen — the explicit digit pattern (de-risked: it is a structured emitter, not an opaque bridge)

`fam_relator(a,b) = apply_embedding(miller_collapse_emb(rel_slice(a,b),0,1), [Gen(a),Inv(b)]) = u_a · u_b⁻¹`,
where (`miller_collapse.rs`) `u_j = miller_collapse_word(j,0,1)` over `{a=Gen(0), t=Gen(1)}`, `i=j+1`:
```
  u_j = t · b⁻ⁱ · a · bⁱ · t⁻¹ · a⁻ⁱ · b⁻¹ · aⁱ ,   b = t a t⁻¹  (substituted mechanically)
      = t · (t a⁻¹ t⁻¹)ⁱ · a · (t a t⁻¹)ⁱ · t⁻¹ · (a⁻¹)ⁱ · (t a⁻¹ t⁻¹) · (a)ⁱ
```
ρ shifts `a=Gen(0)→Gen(cb)`, `t=Gen(1)→Gen(cb+1)` (c-block). `decode_word`'s `alphabet_letter` inverse
maps the c-block symbols to digits: **`a→1, t→2, a⁻¹→3, t⁻¹→4`** (Gen(cb+k)→k+1, Inv(cb+k)→n+k+1, n=2).
So the digit sequence of `u_j` is the regular pattern (exponent `i=j+1`):
```
  digits(u_j) = [2] · (2 3 4)ⁱ · [1] · (2 1 4)ⁱ · [4] · (3)ⁱ · [2 3 4] · (1)ⁱ
```
and `relnum(a,b)` digits = `digits(u_a) ++ digits(u_b⁻¹)`  (with `iₐ=a+1`, `i_b=b+1`; `u_b⁻¹` =
`inverse_word(u_b)` = reverse + Gen↔Inv, i.e. its digit string reversed with `1↔3, 2↔4`).

**This makes R-relnum-gen a TWO-COUNTER structured emitter** (counters `iₐ, i_b`; nested loops emitting
the fixed blocks `(234)`,`(214)`,`(3)`,`(1)` etc.), NOT an opaque proof bridge. The correctness proof =
a digit-correspondence induction against the *explicit* `miller_collapse_word` + the existing
`decode_word`/`apply_embedding`/`lemma_emb_slice_independent` lemmas. ⚠ Confirm `decode_word`'s digit
ORDER (low-first vs high-first) and `inverse_word`'s exact digit transform before fixing the emit order
(the comparison just needs psc_tm to emit in `decode_word`'s canonical order to match α).

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

*Status (2026-06-26): SPEC BACKBONE + IGNITION BUILT. B-FR/B-IG (ignition, `gap2_ignition.rs`) +
B-relnum-spec/B-W-assembly (`gap2_relnum.rs`) DONE; crate 661/0. The whole remaining obligation is now
ONE spec: a machine satisfying `mm_decides_relnum`. Gated on the §5 architecture re-decision (TM
read-loop vs modmachine prefix). The conditional chain already stands; this brick removes the last axiom.*
