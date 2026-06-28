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

- **R-AL — the n≥4 assembly foundation.** ✅ **DONE (`tm_assemble4.rs`, 17/0; full crate 678/0).** The
  n=4 uniform-window scaffold: `entry4(pc)=5+16·pc`, `tm_mod4(len)=21+16·len`, `80=16·5`
  quintuples/window. **FIRST-ORDER scaffold** (a bare `spec fn` won't coerce to `FnSpec`, and
  closure-identity bites — so NO higher-order action table): `lemma_tm_wf_n4` proves `tm_wf` from the
  *manifest-key* hypothesis (`q=entry4(pc)+off`, `a=sym`) + per-quintuple boundedness (`a2≤4`,`q2<m`),
  with determinism by mixed-radix index recovery (`lemma_idx4_recover`), action-content-independent.
  `lemma_slot_index`/`lemma_idx4_decomp` locate/decode a `(pc,off,sym)` slot. `lemma_assemble4_peek_demo`
  validates the whole path: the existing `tm.n>=2`-monotone peek gadget fires verbatim on a concrete n=4
  TM. **Each phase inlines `Seq::new(80·(len+1),|idx| phase_gen(e,idx))` and discharges the manifest +
  boundedness hypotheses — no higher-order passing.** This is the template R-P/R-cmp/R-S/R-C reuse.
- **R-P — the read phase.** From `c1` (scanning α's digits), consume α's base-m digits off the left
  tape. New read/peek gadgets distinguish symbols `1..4`. (Design sub-choice: keep α as base-m digits
  on a dedicated tape region for digit-by-digit compare — do NOT fold into a unary counter, which
  reintroduces the expansion. Stay base-m native.)

  **✅ TAPE LAYOUT DECIDED (2026-06-26, port 8051): OPTION (B) — canonicalize.** Ignition leaves α split
  across `state(digit0)/a(digit1)/u(digits2+)`, head mid-α, `v` empty — awkward for compare. So R-P's
  first job is a **copy-and-park** gadget: walk α's digits into a clean contiguous sentinel-bounded
  block, freeing the other side as workspace. Target layout (head shuttles):
  `[repunit counters | relnum-scratch] | Sentinel | α-copy | Sentinel`. This turns R-cmp from
  "state-encoded vs tape-encoded" into a simple **ping-pong** "tape-string vs tape-string" compare —
  the only way to keep R-cmp proofs tractable (avoids carrying remaining-α-digits in the state).
  **Counters: reuse the existing repunit/2-counter gadget layout** (`tm_two_counter`, parked in the
  workspace with distinct markers `S1|111|S2|11|…`) — the dovetail `s,(a,b),i` are poly-bounded, so the
  unary space overhead is negligible vs. base-m carry-logic complexity, and the inc/dec/peek lemmas are
  trivial to discharge. Only α and `relnum` stay base-m (length Θ(a+b)). R-P terminates with the head at
  the leftmost sentinel of the α-block.

  **✅ R-P FOUNDATION DONE — the digit-string algebra (`tm_dstring.rs`, 14/0)** + **the digit-walk
  gadgets (`tm_dwalk.rs`, 6/0; crate 699/0).** The symbol-agnostic analog of `repunit_m`:
  `dpack(ds, m) = ds[0] + m·ds[1] + …` packs a digit `Seq<nat>` low-first; `dpile(v, blk, m)` = `v`
  after a walk peels `blk` onto it; with `pow_nat` + `lemma_dpack_pop`/`_push`/`_digits_le`/
  `_low_nonzero`/`_append`. The gadgets: `lemma_dwalk_left` (the n=4 analog of `lemma_walk_left_inner` —
  quintuples `(q_walk, s, s, q_walk, L)` for each digit symbol `s ∈ {1,2,3,4}` walk the head left over a
  `dpack` block of nonzero digits onto `v` reversed, `blk.len()` steps, landing `(0, dpile(c.v,blk), 0,
  q_walk)` at the blank turnaround) + `lemma_dwalk_right` (the `u↔v, L↔R` mirror, for R-cmp ping-pong).

  **⚠ SYMBOL-SPACE NOTE (for the copy-and-park assembly).** At n=4 the alphabet is `{0=blank, 1,2,3,4}`
  — all five symbols are spoken for (`0` blank, `1..4` digits), so there is **no free sentinel symbol**.
  But α's digits are all NONZERO (1..4), so **blanks (0) delimit regions** and the head's STATE tracks
  which region it is in. The counter `sep()=2` and α-digit-`2` coexist only because the counter region
  and α-block are **blank-separated** (a walk stops at the blank before crossing); the head crosses a
  blank gap only via a deliberate `(q, 0, …)` turnaround quint. Target layout
  `[counter blocks] 0 [relnum-scratch] 0 [α-block] 0`. (If region navigation proves hairy, n=5 with a
  dedicated sentinel symbol `5` is the fallback — gadgets are alphabet-monotone, assemble4 generalizes.)

  **NEXT = the R-P copy-and-park ASSEMBLY.** ✅ CONCRETE ALGORITHM WORKED OUT (2026-06-26): from the
  ignition output `c1 = {u: dpack([d2,d3,…]), v: 0, a: d1, q: start(d0)}` (digit0 in the state, head at
  d1) —
    1. **`start(i)` step** (scanning d1): write `a2=d1`, move **R** → pushes d1 onto u, pops the empty v;
       result `u' = u·m + d1 = dpack([d1,d2,…])`, scanned `= 0`, state → `deposit(i)`. (Preserves d1 by
       writing it back; uses the move to re-pack d1 into u in order.)
    2. **`deposit(i)` step** (scanning the blank 0): write `a2 = i = d0`, move **L** → pushes d0 onto the
       empty v, pops u's low digit; result `v' = dpack([d0])`, scanned `= d1`, `u = dpack([d2,…])`, state
       → `q_walk`. (Deposits the state-held d0 onto v.)
    3. **`lemma_dwalk_left`** over `blk = [d1,d2,…,d_{L-1}]` → pushes them onto v atop d0; result
       `v = dpile(dpack([d0]), blk)`, `u = 0`, scanned `= 0`, head on the left blank.
  **Net:** α's digit sequence is parked **reversed** in v (high digit lowest: reading v low→high gives
  `d_{L-1}…d1 d0`), with u freed as workspace and the head on a blank boundary. R-cmp then compares this
  reversed α-block against relnum generated/compared in the same reversed order (or applies one more
  reversal via `lemma_dwalk_right`).

  **✅ COPY-AND-PARK CORE DONE (`tm_rp.rs`, 7/0; crate 706/0).** `lemma_rp_entry` (the 2-step handshake)
  + `lemma_rp_copy_park` (entry ∘ `lemma_dwalk_left` over `[d1]+tail`, `3+tail.len()` steps to
  `{u:0, v: dpile(dpack([d0]), [d1]+tail), a:0, q:q_walk}`). Both are **generic over an abstract `tm`**
  carrying the 5 handshake + 4 walk quintuples at given indices — the eventual `psc_act` window supplies
  them via `lemma_slot_index`. This PINS `start(d0) := the start-handshake state` (the abstract param in
  B-IG `ignition_quads(ndig, start)`).

  **✅ R-P PSC_ACT WINDOW ASSEMBLY DONE (`gap2_psc_rp.rs`, 11/0; crate 717/0).** `rp_act` = the R-P
  action table over windows `0..=4` (window 0 = walk, `q_walk=entry4(0)=5`; windows `1..=4` = per-digit,
  `q_start(d0)=entry4(d0)`, `q_deposit(d0)=entry4(d0)+1`). `lemma_rp_phase(tm, len, tail, d0, d1)` is the
  reusable splice: any `tm_wf` n=4 assemble4 machine whose first five windows carry `rp_gen` (`i<400`)
  parks α via `lemma_rp_copy_park`. **PINS the ignition handoff: `rp_start(d0) = entry4(d0)`** — verified
  to match `rep1(c1)=(α/m, entry4(d0))` (the modular ignition output). Concrete validation
  `psc_rp_tm(len)` + `lemma_psc_rp_wf` + `lemma_psc_rp_copy_park`. **Still TODO for the full machine:**
  retarget the `(q_walk,0)` blank-turnaround (placeholder `→0`) to the R-S entry; thread `tm_config_wf`
  (via `lemma_dpack_digits_le`) for `lemma_tm_h0_iff`; the **single-digit-α** divergence branch
  (`d1==0` after the start R-move — a 1-digit word-number is never a `relnum`, so non-accept is correct).
- **R-relnum-gen — generate relnum(a,b)'s base-m digits.** For an enumerated declared `(a,b)`, emit the
  digits of `relnum(a,b)` = the symbols of the collapsed Miller relator `ρ(collapse(g_a g_b⁻¹))`
  (length Θ(a+b); `t·(b⁻¹)ⁱ·a·(b)ⁱ·t⁻¹·a⁻ⁱ·b⁻¹·aⁱ`, `i=j+1`, `b=tat⁻¹`). Loop control via counters
  (symbols 1,2). Follow the collapse definition exactly — do not reinvent.

  **✅ R-relnum-gen SPEC FOUNDATION DONE (`gap2_relnum_digits.rs` + `gap2_rho_unshift.rs`; crate 732/0).**
  The emitter's target is now an explicit `dpack` of digits, with ρ eliminated:
    - **`gap2_relnum_digits.rs`** — `decode_digit_seq(c,n,w)` = the low-first digit block of a word's
      word-number (= the REVERSED letter-digits, since `decode_word` folds the LAST symbol as the LOWEST
      digit). `lemma_decode_word_is_dpack`: `decode_word(c,n,m,w) == dpack(decode_digit_seq(c,n,w), m)`
      (the digit-ORDER linchpin — resolves the plan's ⚠). `lemma_decode_word_concat`:
      `decode_word(w1+w2) == decode_word(w1)·m^|w2| + decode_word(w2)` (Horner split — the tool to break
      `fam_relator` into `u_a · u_b⁻¹` and each `u_j` into its 8 pieces). `_len`/`_bound` (digits `1..2n`,
      fit the n=4 tape).
    - **`gap2_rho_unshift.rs`** — `lemma_decode_rho_unshift`: `decode_word(off,n,m, ρ(w)) ==
      decode_word(0,n,m, w)` for `word_valid(w, p1.num_generators)` — **ρ (the c-block relabel) is
      invisible to the word-number** because `letter_digit(cb,2,·)` un-shifts the `+cb`.
      `lemma_fam_relator_word_valid` (`word_valid(fam_relator(a,b), 2)`). `lemma_relnum_no_rho`:
      `relnum == decode_word(0,2,m, fam_relator(a,b))`.
    - **CAPSTONE `lemma_relnum_is_decode_digit_seq`:** `relnum(e,mm,m,a,b) ==
      dpack(decode_digit_seq(0, 2, fam_relator(a,b)), m)`. **This is the single fact the emitter and the
      compare prove against.** `fam_relator(a,b) = u_a · inverse_word(u_b)`, `u_j =
      miller_collapse_word(j,0,1)`, digits over `{a=Gen0→1, t=Gen1→2, a⁻¹→3, t⁻¹→4}` = `letter_digit(0,2,·)`.

  **✅ STEP 1 — THE EXPLICIT DIGIT PATTERN — DONE (crate 759/0).** `decode_digit_seq(0,2, fam_relator(a,b))`
  is now an explicit `seq_pow`/singleton block concatenation. Design fork RESOLVED with Danielle: **(B)
  digit-seq framing** (decouple the eventual emitter's Production proof `tape == digit blocks` from the
  Evaluation proof `dpack == value`) + **structural 8-piece rewrite** of `inverse_word(u_b)` (not a general
  `decode_word∘inverse_word` lemma). The bricks:
    - **`gap2_relnum_digits.rs`** (added) — `lemma_decode_word_word_power`: the geometric closed form
      `decode_word(word_power(w,k)) == decode_word(w)·repunit_m(k, m^|w|)` (the `(234)ⁱ`/`(214)ⁱ` block
      value), via `lemma_word_power_snoc` onto the low-end repunit recurrence (no power-of-power lemma).
    - **`gap2_relnum_dds.rs`** (new) — the digit-seq structural algebra (Production side): `seq_pow<A>`,
      `lemma_dds_concat` (the REVERSAL law `dds(w1++w2)=dds(w2)++dds(w1)`), `lemma_dds_singleton`,
      `lemma_dds_word_power` (`=seq_pow(dds(w),k)`), `lemma_dds_symbol_power`.
    - **`gap2_inverse.rs`** (new) — `inverse_word` block laws: `inverse_word(symbol_power(s,k))=
      symbol_power(s⁻¹,k)`, `inverse_word(word_power(w,k))=word_power(inverse_word(w),k)`.
    - **`gap2_fam_split.rs`** (new) — `lemma_fam_relator_split` (`fam_relator = u_a ++ inverse_word(u_b)`
      via apply_embedding peel) + the 3-letter b/b⁻¹ inverses + `lemma_inverse_collapse_word`
      (`inverse_word(u_b) = a⁻ⁱ·b·aⁱ·t·binv^i·a⁻¹·b^i·t⁻¹`, the explicit 8 pieces).
    - **`gap2_fam_digits.rs`** (new) — the headline `lemma_dds_fam_relator`:
      `decode_digit_seq(0,2,fam_relator(a,b)) == fam_digits(a,b) = uinv_digits(b) ++ u_digits(a)`, with
      `u_digits(j) = (1)ⁱ·[4,3,2]·(3)ⁱ·[4]·(412)ⁱ·[1]·(432)ⁱ·[2]` (i=j+1, low-first/reversed) and
      `uinv_digits(b) = [4]·(412)ⁱ·[3]·(432)ⁱ·[2]·(1)ⁱ·[4,1,2]·(3)ⁱ`. **These `seq_pow` blocks are the
      exact tape sequence the emitter lays down, one loop iteration per block.**

  **NEXT for R-relnum-gen — STEP 2, the two-counter emitter** (counters `iₐ=a+1`, `i_b=b+1`; nested loops
  emitting the `fam_digits` blocks), proved to produce `fam_digits(a,b)` on tape — over the n=4 assemble4
  scaffold (template: `gap2_psc_rp.rs` / `tm_assemble4::lemma_assemble4_peek_demo`). The spec target is now
  PINNED (`fam_digits`/`lemma_dds_fam_relator`); the Evaluation side reuses `lemma_relnum_is_decode_digit_seq`
  + `lemma_dpack_*` to turn the produced digits into the `relnum` value.

  **✅ STEP 2 ARCHITECTURE DECIDED (2026-06-26, port 8051): MODEL (B) HOME/SHUTTLE.** The tension: the
  emitter has THREE logical regions (masters `iₐ`, `i_b`; an active loop temp; the growing output) but
  Minsky pair form has only TWO stacks `u,v`, and an L-move emitting onto `v` POPS `u`. The clean
  "consume-the-counter-while-piling" trick (model A) only works for 1-digit blocks (emit==decrement
  coincide) and cannot preserve masters across the 16 blocks. **Decision: the AC standard single-tape
  discipline.** Fixed tape layout, head shuttles:
  ```
    [iₐ ones] 0 [i_b ones] 0 [output digits] 0 [blanks]
                            ↑ HOME PIVOT (the 0 before output)
  ```
  Per-block iteration for `(blk)ⁱ` (block now lives in the STATE-transition graph, not in tape ticks — the
  multi-digit cost is shifted to state space, masters stay put on the left, never popped):
    1. **Peek/dec the master** at home (left into `i_b`/`iₐ`), confirm `> 0`.
    2. **Rightward surge** to the frontier: skip the output non-destructively (write-back, `a2=scanned`).
    3. **Sequential write**: a state cycle `e0→e1→…→e0`, each writes one digit of `blk`, moves R.
    4. **Home return**: move L over the output back to the home pivot.
    5. Loop until the master is exhausted.
  **The safe write-back traversals ALREADY EXIST** — `tm_dwalk::lemma_dwalk_right` (surge to frontier,
  block `v→u` via `dpile(c.u,blk)`) and `lemma_dwalk_left` (return home, block `u→v`) write back the
  scanned symbol (`a2=s`), so they are exactly the non-destructive shuttles. New STEP-2 bricks: the
  frontier block-emit (a state-cycle of 1-step `(e_k,0,blk[k],e_{k+1},R)` writes onto `u` over the frontier
  blanks), the dec-master-in-layout-and-return-home gadget, and the per-block loop (growing-output
  induction). Model (A) ABANDONED.

  **✅ STEP 2 brick 1 DONE (`tm_emit.rs`, crate 766/0).** The symbol-power emit loop
  `lemma_emit_symbol_power_inner`: the loop quintuple `(q_emit,1,s,q_emit,L)` consumes a `repunit_m(i)` and
  piles `i` copies of `s` onto `v` (`pile_sym`, the symbol-generalized `pile_ones`). `lemma_pile_sym_shift`
  + `lemma_pile_sym_is_dpile` bridge the accumulator to `dpile(·, seq_pow([s],i))` — the digit-seq algebra
  form, so an emitted run composes with the explicit `fam_digits` decomposition. (NOTE: written before the
  model-B decision; the `pile_sym`/`dpile` output-accounting algebra is reused under model B, even though
  model B's per-block loop is the home/shuttle one, not this direct-consume loop.)
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

*Status (2026-06-26, session N+2): SPEC BACKBONE + IGNITION + R-AL + R-P PRIMITIVE LAYER + R-P ASSEMBLY +
R-relnum-gen SPEC FOUNDATION + **R-relnum-gen STEP 1 (THE EXPLICIT DIGIT PATTERN)** BUILT; crate 759/0.
B-FR/B-IG (`gap2_ignition.rs`) + B-relnum-spec/B-W-assembly (`gap2_relnum.rs`) + R-AL (`tm_assemble4.rs`)
+ R-P primitives (`tm_dstring.rs`/`tm_dwalk.rs`/`tm_rp.rs`) + R-P assembly (`gap2_psc_rp.rs`) + R-relnum
spec foundation (`gap2_relnum_digits.rs`/`gap2_rho_unshift.rs`) DONE [prior sessions].

**THIS SESSION — R-relnum-gen STEP 1 COMPLETE (the explicit digit pattern):** design fork RESOLVED with
Danielle = **(B) digit-seq framing** (decouple Production `tape==blocks` from Evaluation `dpack==value`) +
**8-piece inverse rewrite**. Bricks: `lemma_decode_word_word_power` (geometric closed form, in
`gap2_relnum_digits.rs`); `gap2_relnum_dds.rs` (the dds REVERSAL algebra `dds(w1++w2)=dds(w2)++dds(w1)`,
`seq_pow`, dds-of-word_power/symbol_power/singleton); `gap2_inverse.rs` (inverse_word block laws);
`gap2_fam_split.rs` (`fam_relator = u_a ++ inverse_word(u_b)` + the explicit `inverse_word(u_b)` 8-piece);
`gap2_fam_digits.rs` (**headline `lemma_dds_fam_relator`**: `decode_digit_seq(0,2,fam_relator(a,b)) ==
fam_digits(a,b) = uinv_digits(b) ++ u_digits(a)`, an explicit `seq_pow`/singleton block concatenation).

The whole remaining obligation is ONE spec: a machine satisfying `mm_decides_relnum`, built as Route (i) —
a bespoke n=4 `tm_wf` TM `psc_tm(e)` over the assemble4 scaffold. The emitter's spec target is now FULLY
EXPLICIT (`fam_digits`). NEXT (deep brick, multi-session): (2) **the two-counter emitter** (R-relnum-gen)
proved to PRODUCE `fam_digits(a,b)` on tape, one loop iteration per `seq_pow` block, over the assemble4
scaffold (template `gap2_psc_rp.rs`); then (3) R-cmp / R-S / R-C / R-MC. Also TODO on R-P assembly:
retarget the `(q_walk,0)` turnaround to R-S entry, thread `tm_config_wf`, the single-digit-α divergence
branch. The conditional chain already stands; this brick removes the last axiom.*

---

*Status (2026-06-26, session N+3): R-relnum-gen STEP 2 KICKOFF — architecture fork RESOLVED + first two
emit bricks BUILT; crate 771/0.*

**THIS SESSION:**
- **MODEL (B) HOME/SHUTTLE decided with Danielle (port 8051)** — see the "✅ STEP 2 ARCHITECTURE DECIDED"
  block in §5 (R-P/R-relnum-gen). Tape `[iₐ]0[i_b]0[output]0[blanks]`, head shuttles, masters never
  popped; per-block iter = peek/dec master at home, surge right to frontier, sequential write, return
  home. Model A (consume-counter-while-piling) ABANDONED (can't preserve masters across blocks).
- **`tm_emit.rs` (766/0)** — `lemma_emit_symbol_power_inner` (model-A symbol-power loop;
  `pile_sym`/`lemma_pile_sym_shift`/`lemma_pile_sym_is_dpile`). Written pre-decision; the
  `pile_sym`/`dpile` output-accounting ALGEBRA is reused under B even though B's per-block loop is the
  shuttle one, not this direct-consume loop.
- **`tm_shuttle.rs` (771/0)** — the "sequential write" step. `lemma_emit_one_frontier` (1-step R-move
  writing a digit onto `u` over the frontier blank, `v==0`) + `lemma_emit_block1_frontier` /
  `lemma_emit_block3_frontier` (→ `dpile(c.u, blk)`, the only `fam_digits` block sizes).
- **KEY REUSE FINDING:** the safe write-back traversals model B needs ALREADY EXIST —
  `tm_dwalk::lemma_dwalk_right` (surge to frontier: block `v→u` via `dpile(c.u,blk)`, stops at the blank)
  and `lemma_dwalk_left` (return home: block `u→v`, stops at the blank). They write back the scanned
  symbol (`a2=s`), so they are the non-destructive shuttles.

**THIS SESSION (N+3) BUILT (crate 760/0 → 783/0):** model-B fork resolved (above); `tm_emit.rs`
(symbol-power emit + pile_sym/dpile algebra, 766/0); `tm_shuttle.rs` (frontier block-emit, 771/0);
`tm_dec_master.rs`: `lemma_walk_left_prefix` (generalized walk-left over a repunit prefix with preserved
high tail `w`, 774/0) + `lemma_walk_back_prefix` (the back-direction twin, 776/0) + **`lemma_dec_temp`**
(the full master-decrement at home, 783/0): `{dec_u(temp,w), output, 0, q_home}` →`2·temp+2`→
`{dec_u(temp−1, m·w), output, 0, q_back}`, `dec_u(temp,w,m)=repunit(temp)+m^temp·w`. Found: the safe-walk
shuttles already exist (`dwalk_left`/`dwalk_right`); the gap-growth pitfall ⟹ the `[master]0[temp]0[output]`
per-power-block layout, gap absorbed into `w ← m·w`.

**NEXT (the per-block integration — start here):** the **per-block ITERATION** lemma (home→home, one
`(blk)` emitted + temp decremented), composing two home→home halves:
  (a) **surge+emit+return** (output → output++blk): from home, move R off pivot → `dwalk_right` over
      output to frontier → `emit_block{1,3}_frontier` → move L onto blk → `dwalk_left` back to pivot.
      ⚠ During the surge the output moves `v→u` (head pushes it onto `u` atop the pivot-0); the masters
      `[temp][master]` sit DEEPER in `u` and are untouched. Track the `dpile`/`dpack` ordering — the block
      lands reversed via `dpile`; reconcile vs `fam_digits`' low-first order (may need the return as
      `dwalk_left` then a re-pass, or emit in the matching order).
  (b) **`lemma_dec_temp`** (temp → temp−1) — DONE, drops straight in (home→home, output preserved).
Then the per-block **LOOP** (induct on temp: `i` iters ⟹ output gains `seq_pow(blk,i)` via `pile_sym`/
`dpile` accounting, temp→0, `w` grows ×m per step). Then the **copy-refresh** gadget (rebuild temp from a
preserved master before each of a phase's 4 power-blocks). Then **16-block sequencing** (== `fam_digits`,
via `lemma_dds_fam_relator`/`lemma_relnum_is_fam_digits`). Then `psc_act` window assembly + R-cmp/R-S/R-C/
R-MC/B-W.

**NEXT (model-B per-block loop — the substantial remaining STEP-2 work):**
1. **`home_config(iₐ, i_b, output, m)` spec** — the layout config: `a=0` (home pivot, the 0 before
   output), `u = [i_b ones] 0 [iₐ ones]` (low=i_b inner one), `v = [output digits] 0 [blanks]` (low=output
   first digit; trailing 0s vanish under `dpack` so `v == dpack(output)`).
2. **`dec_master` gadget** — decrement `i_b` (or `iₐ`) and return to the home pivot. MIRROR `lemma_dec`
   but with `iₐ` present as extra HIGH content in `u` beyond the `i_b/iₐ` separator 0. Erase the OUTER
   `i_b` one (walk left to the `i_b/iₐ` sep 0, erase-turnaround, walk back) so `i_b` stays adjacent to the
   pivot — NO gap growth (the gap-at-pivot approach is wrong; outer-erase is the lemma_dec discipline).
   Pivot MUST stay `0` (dwalk stops at 0; a sep=2 pivot would be walked over since digit 2 ∈ fam_digits).
   **The subtlety (worked out, not yet coded):** lemma_dec starts head-on-sep (`a=2`); dec_master starts
   head-on-pivot (`a=0`). So step 1 "peel pivot" is `(q_home, 0, 0, q_walk, L)` — moving L pushes the pivot
   0 onto `v` (`v1 = dpack(output)·m`, low digit 0) and exposes `i_b`'s inner one. Then walk-left over
   `i_b`'s ones piles them onto `v1` ON TOP of the output (temporarily!), landing on the `i_b/iₐ` sep 0 —
   here `u` is NOT 0 (it's `repunit(iₐ)`), unlike lemma_dec where `u==0` at the blank; the erase-turnaround
   `(q_walk, 0, 0, q_disc, R)` fires on `a=0` regardless of `u`. The walk-BACK-right is the inverse: it
   pops the pile off `v`, RESTORING the output exactly, and lands head on `v1`'s low cell = the pivot `0`.
   Net: output unchanged, `i_b → i_b−1`, head home. ⚠ The three `a=0` roles (home pivot, `i_b/iₐ` sep,
   far blank) are disambiguated by STATE (`q_home`/`q_walk`/`q_disc`), never by the scanned symbol.
   ⚠ Decrementing `iₐ` (the OTHER, farther master) needs walking PAST `i_b` first — so likely keep `i_b`
   as the inner/active master for `u_digits`'s exponent and `iₐ`... reconsider order: maybe lay
   `[i_active]0[i_other]0[output]` and rebuild `i_active` per fresh block from a preserved `i_other` copy,
   OR process all of `u_digits` (exponent `a+1`) with `iₐ` inner, then all of `uinv_digits` (exponent
   `b+1`) — revisit which master is inner when sequencing the 16 blocks (step 5).
   ⚠⚠⚠ **REFINED LAYOUT (found this session, supersedes the naive `[iₐ]0[i_b]0[output]` above):** decrementing
   one master with the OTHER master sitting as high content in `u` causes **GAP GROWTH** — the erase + discard
   steps each push a `0` onto `u` above the high content (in `lemma_dec` `u==0` there so it's harmless; here
   the high master accretes a leading `0` per dec). So DON'T keep both masters live and dec one "through" the
   other. Instead, per POWER-BLOCK `(blk)ⁱ` the live layout is **`[master]0[temp]0[output]0[blanks]`**: `temp`
   (inner, adjacent to the pivot) is a fresh DECREMENTING COPY of the master; `master` is PRESERVED (it is the
   high tail `w` that `lemma_walk_left_prefix` leaves intact while dec'ing `temp`). Before each power-block,
   REFRESH `temp` from `master` via a copy gadget (walk master's ones onto temp + restore, a 3rd gadget to
   build). Exponent reuse across a phase's 4 power-blocks ⟹ master must survive ⟹ the copy. Singletons
   between power-blocks emit with no counter (direct `emit_block1`-style, `u`-side untouched if head is parked
   right). The two phases (`uinv_digits(b)` exponent `b+1`, then `u_digits(a)` exponent `a+1`) run
   SEQUENTIALLY — only ONE master alive at a time — re-init the master between phases. This keeps it to 3
   regions max and makes `lemma_walk_left_prefix` exactly the dec-temp walk (`w` = master content, `w%m==0`).
   ⚠ **OLD SUB-GADGET FRAMING (still the mechanism, master plays the "high tail" role):** `dec_temp` CANNOT reuse
   `tm_walk::lemma_walk_left_inner` directly — that lemma requires `c.u == repunit_m(j0)` and concludes
   `u == 0` (it assumes the rest of the left tape is blank). In the home layout `u` has `iₐ`'s content
   (`repunit(iₐ)`) beyond the `i_b/iₐ` separator, so walking `i_b`'s ones must STOP at that separator 0 and
   LEAVE `iₐ` intact (`u == W` where `W = m·repunit(iₐ)`, `W%m==0`). So FIRST build a **generalized
   walk-left** `lemma_walk_left_prefix`: from `u == repunit(j0) + m^(j0)·W` with `W%m==0`, the `(q,1,1,q,L)`
   loop fires `j0+1`(?) times piling `j0` ones onto `v` and landing on the separator-0 (`a==0`, `u==W/m`...
   recheck the exact count/landing). lemma_walk_back_inner is already generic in the under-pile `w` so the
   walk-BACK reuses verbatim (`w = dpack(output)·m`). This generalized walk-left is the first concrete
   thing to build next session (small, mirrors lemma_walk_left_inner with a high-content tail).
3. **per-block-iteration lemma** — from `home_config`, ONE iter: move R off pivot → `dwalk_right` over
   output to frontier → `emit_block{1,3}` → move L onto block → `dwalk_left` back to pivot → `dec_master`.
   Net: output ← `output ++ blk` (or the dpile-reversed form — TRACK the order vs `fam_digits` low-first),
   `i_b ← i_b - 1`. Bounded composition (no cross-iter induction yet).
4. **per-block LOOP lemma** — induct on the master counter: `i` iters emit `seq_pow(blk, i)` onto output,
   master → 0. Growing-output invariant. Use `pile_sym`/`dpile` accounting (the reused tm_emit algebra).
5. **16-block sequencing** — chain the per-block loops for `uinv_digits(b) ++ u_digits(a)` (8 blocks each;
   masters iₐ=a+1, i_b=b+1; singletons via `emit_block1`-style direct writes between power-blocks). Prove
   the produced output `== fam_digits(a,b)` (compose with `lemma_dds_fam_relator`/`lemma_relnum_is_fam_digits`).
6. Then the `psc_act` window assembly (template `gap2_psc_rp.rs`), then R-cmp / R-S / R-C / R-MC / B-W wiring.

⚠ Use the CRATE-LOCAL `./check.sh` (Lean backend + group-theory export), NOT the top-level `verus-cad/check.sh`
(verus-dev, fails to compile the Lean-backend group-theory dep) and NOT the verus MCP `check`.*

---

*Status (2026-06-26, session N+4): R-relnum-gen STEP 2 — PER-BLOCK ITERATION + PER-BLOCK LOOP COMPLETE
(both block sizes); crate 833/0.*

**THIS SESSION (N+3 783/0 → N+4 833/0) BUILT:**
- **`tm_dwalk_prefix.rs` (802/0)** — the prefix digit-walk-left + the `drev` (low-first digit reverse)
  algebra. `lemma_dwalk_left_prefix` is the digit (`1..4`) analog of `lemma_walk_left_prefix`: walk left over
  a block leaving a high tail `w` (the masters) intact. The reversal bookkeeping — "a left-walk peels `u`
  low-first then re-piles onto `v`, reversing the order" — is NAMED via `drev` (Danielle's call, port 8051):
  `dpile(0,s)==dpack(drev(s))` (`lemma_dpile_zero_drev`), the `v≠0` split `lemma_dpile_is_dpack_drev`,
  `drev` involution/concat/digit-bound, and `lemma_dpile_concat`. So "there-and-back is identity" is one
  clean fact, not inline reasoning.
- **`tm_block_iter.rs` (815/0)** — ONE iteration. `lemma_surge` (move-R off pivot + `dwalk_right` → frontier,
  handles empty/nonempty output uniformly), `lemma_return_walk` (move-L + `dwalk_left_prefix` home, the two
  walks cancel ⟹ output comes out `dpack(output++blk)` clean, masters intact), then the composites
  `lemma_surge_emit_return_block1/_block3` and `lemma_block_iter_block1/_block3` (splice on `dec_temp`):
  home→home, `output ↦ output ++ blk`, `temp ↦ temp−1`. **Masters `U` kept GENERIC** (instantiated to
  `dec_u(temp,w)` only at the `dec_temp` splice) — emitter correctness is a structural prefix-preserve.
  KEY RESOLUTION: net per-iteration effect is `od ↦ od ++ blk` (low-first, NO net reverse — the surge and
  return walks cancel); the block lands at the high/frontier end.
- **`tm_block_loop.rs` (833/0)** — the per-block LOOP. A 2-step non-destructive **guard** (`lemma_guard_continue`
  / `lemma_guard_exit`) peeks the counter at the home pivot (peel pivot left → peek inner cell → move back
  right, restoring) and branches: inner `1` ⟹ continue (fall into `q_iter`), inner `0` (separator) ⟹ exit.
  `dec_u` arithmetic helpers (`lemma_dec_u_step`/`_zero`). `lemma_block_loop_block1/_block3` (induct on
  `temp`, body lands back in `q_loop` since `q_back==q_loop`): `(s)^temp` / `(s0,s1,s2)^temp` emitted onto the
  output, counter consumed, master shifted `w ↦ m^temp·w`. Fuel via `loop_fuel_b1/_b3` spec fns. Output:
  `{u: dec_u(0, m^temp·w), v: dpack(od ++ seq_pow(blk, temp)), q: q_exit}`.

**STATE GRAPH (one phase, settled this session):** `q_loop`(guard peek L / dec walk-back R, `q_back==q_loop`)
→ `q_guard`(cont→`q_iter` / exit→`q_exit`) → `q_iter`(move-R off pivot) → `q_surge`(`dwalk_right` j=1..4 /
emit 0) → `q_e1/q_e2`(triple emit) → `q_eret`(move-L) → `q_home`(`dwalk_left` j=1..4 / dec pivot-peel 0) →
`q_dwalk`(dec walk / erase) → `q_disc`(discard→`q_loop`). All `a=0` roles disambiguated by STATE; tm_wf
determinism holds (distinct (state,scanned) pairs).

**✅ ARCHITECTURE DECISION (2026-06-26, port 8051): the copy-refresh uses a MARKER ⟹ BUMP n=4 → n=5.**
Option (B) of the fork. At n=4 the alphabet `{0,1,2,3,4}` is fully spoken for (0 blank, 1..4 = fam_digits),
so a marker-free copy needs either a 3rd scratch unary region with two-register-increment shuttling
(option A, intricate, error-prone) or a non-destructive marked traversal that REPLACES the verified
consuming loop (option C, throws away `block_iter`/`block_loop` 833/0). Instead, **add sentinel symbol `5`
(= n) as a copy marker** and keep the consuming loop. The copy is then the standard textbook copy
(mark master `1→5`, deposit a `1` in temp, restore `5→1`). **Zero rework of this session's lemmas**: they
all require `tm.n >= 4` (alphabet-monotone) + digits `1..4` + `m > 4`, all of which hold at n=5
(`tm.n=5≥4`, `m>5>4`, fam_digits `1..4 < 5`, marker `5 = n` is a valid symbol `≤ n`). The R-AL scaffold
becomes `assemble5` (a linear `n`-bump of `tm_assemble4`); ignition/α-read survive (α digits `1..4`, needs
`n≥4`). The fallback-n=5 the plan already flagged is now the chosen path.

**NEXT (remaining STEP-2 work):**
1. **copy-refresh gadget (n=5 marker `5`)** — before each of a phase's 4 power-blocks, rebuild `temp` (a
   fresh decrementing copy) from the PRESERVED master. The loop leaves `u = dec_u(0, m^temp·w) = m^temp·w`
   (counter consumed, master `w` shifted UP — its absolute position drifts up by `m^temp` each loop; the
   gap of blanks below the master grows). **The drift is fine** (port 8051): the region between pivot and
   master is all blanks, so "seek master" is just a walk-left over the gap (the only nonzero region in `u`
   above the pivot is the master). Concrete gadget (head starts at pivot, output parked in `v`):
   - **seek**: walk-left `(q,0,0,q,L)` over the gap blanks (piling them onto `v` = `output·m^gap`, restored
     on un-seek) until the first master `1`.
   - **marked copy loop**: for each master `1` (scanning a `1`): write `5` (mark), walk-right back toward
     the pivot skipping `5`s/`1`s(temp)/blanks, deposit a `1` adjacent to the pivot (extending temp), walk-
     left back skipping temp-`1`s/blanks to the next unmarked master `1`. Repeat until master has no `1`
     (all `5`). Output `v` untouched (only `u`-side pushes/pops + state).
   - **restore + un-seek**: walk-left over the master changing `5→1`, then walk-right back to the pivot,
     popping the seek's piled blanks off `v` to restore `output`. Land `{u: dec_u(M, m·repunit(M)... ), v:
     dpack(output), a:0, q:q_loop}` — i.e. `[master M]0[temp M]0[output]`, ready for the next `block_loop`.
   ⚠ Re-examine the EXACT pre/post `u` value (the master's drifted position vs. the fresh temp's position).
   The singletons between power-blocks emit with NO counter (one `surge_emit_return_block1/3`, no loop, no
   dec) — master sits inert in `u` (surge/return only move output `v↔u` + pivot). Build the `assemble5`
   bump first (or keep threading quint indices, deferring assembly to the psc_act window step).
2. **16-block sequencing** — chain the 8 blocks of `uinv_digits(b)` then the 8 of `u_digits(a)` (masters
   `i_b=b+1`, `iₐ=a+1`; ONE master alive per phase, re-init between phases). Prove output `== fam_digits(a,b)`
   (compose `lemma_dds_fam_relator` / `lemma_relnum_is_fam_digits`). The block structure (from
   `gap2_fam_digits`): `u_digits(j) = (1)ⁱ·[4,3,2]·(3)ⁱ·[4]·(4,1,2)ⁱ·[1]·(4,3,2)ⁱ·[2]`,
   `uinv_digits(b) = [4]·(4,1,2)ⁱ·[3]·(4,3,2)ⁱ·[2]·(1)ⁱ·[4,1,2]·(3)ⁱ` (i=exp+1, low-first).
3. Then `psc_act` window assembly (template `gap2_psc_rp.rs`), R-cmp / R-S / R-C / R-MC / B-W wiring.

⚠ Use the CRATE-LOCAL `./check.sh` from inside `tactus-computability-theory/` (`cd` there first — the
top-level `verus-cad/check.sh` is the verus-dev one and prints usage / fails the Lean-backend dep).*

---

## SESSION UPDATE 2026-06-26 (N+5) — copy-refresh SEEK walks DONE; marked-copy core = design gate + ⚠ resource question

**✅ Seek primitives built + verified (`tm_copy_refresh.rs`, 12/0, committed `57354ea`).** The blank-gap
analogs of `tm_dwalk` (which walk over nonzero digit blocks and stop at a blank): here the head walks over a
run of blanks and stops at the first NONZERO cell.
- `lemma_seek_left_blanks`: from `{u: m^g·r, a:0, q}` with `r%m≠0`, the quint `(q,0,0,q,L)` fires `g+1` times,
  piling `g+1` blanks onto `v` (×`m^(g+1)`), landing the head on the master's low digit `{u: r/m, v: c.v·m^(g+1),
  a: r%m, q}`. Induction on `g`. (Locates the master across the post-`block_loop` blank gap.)
- `lemma_seek_right_blanks`: the exact `u↔v`, `L↔R` un-seek mirror (`(q,0,0,q,R)`), for walking back home.
Both are robust to the master's exact representation (only need `r%m≠0` at the target), so they are low-regret.

**⚠ MARKED-COPY CORE = the genuine difficulty, and TWO open questions before the big build:**

1. **The unfindable resource.** Danielle's 06-26 message (`MESSAGES_FROM_USER.md`): *"I put computability of
   recursive functions in tactus-computability-theory, use nix-shell to read it."* Exhaustively searched — NO
   such file/dir/Lean-project is on disk (no `.lean`, no lakefile, no new module; the crate's shell.nix only
   provides lean4+elan). The marked-copy is precisely the "reinvent a computability primitive" pattern her
   standing rule warns against ("wasted 13000 lines"). **Must locate/read her resource before grinding the
   marked-copy** — it may give a higher-level path (or at least a textbook to follow for the copy).

2. **The copy must use a MARK (companion-confirmed).** The "two-places problem" — duplicate one M-one block
   (master, high in `u`) into TWO M-one blocks (preserved master + fresh `temp` at the pivot) — is intrinsic:
   a single `v`-pile cannot duplicate (popping reconstructs ONE run), and the distance between the temp-site
   and master-site is the cost, not the copy mechanism. So the `5`-mark is necessary. Companion's refinement:
   **block-displacement** (pile-relocate the master down adjacent to the pivot → local marked copy at gap≈0 →
   pile-relocate back) turns `O(M·gap)` into `O(M+gap)` and keeps each copy-iteration's invariant LOCAL
   (contiguous region, no big-gap arithmetic). Cleanest VERUS decomposition (proposed, NOT yet built):
   - **(a) relocate master down to pivot** via `lemma_walk_left_prefix` (pile master onto `v`) + `walk_back_prefix`
     (write it back at the low end) — reuses existing lemmas; positions need care.
   - **(b) local marked copy** (gap≈0): induction `j: 0→M` on the home invariant
     `u = [temp: j ones][sep][master: (M−j) ones][j fives][above]`, each step = mark the lowest unmarked master
     `1`→`5`, deposit a `1` in temp (an R-move `u←u·m+1` family), restore — the delicate part, the new
     inductive lemma. Needs `(q,1,5,q',·)` mark quint.
   - **(c) un-mark** master `5→1` (a dwalk-style pass) + **un-seek** (`lemma_seek_right_blanks`) home. Output
     `{u: dec_u(M, w_master_preserved), v: dpack(output), a:0, q}`, ready for the next `block_loop`.
   The plan's earlier roaming-mark sketch (§NEXT.1) is the `O(M·gap)` version; block-displacement is preferred
   for cleaner invariants. **EXACT pre/post `u` bookkeeping** (master's drifted position, gap growth across the
   4 blocks of a phase, where `M`=exponent is read from) is the remaining design pin — co-design before building.

**NEXT:** resolve (1) [locate Danielle's recursive-functions resource — may reshape the approach], then build
the marked-copy per (2) bottom-up (relocate → local marked copy → un-mark/un-seek), then `copy_refresh`
assembly, then 16-block sequencing, then `psc_act` window + `ceer_realizes` wiring.

### ✅ RESOLVED + PINNED (same session, N+5 cont.) — gate 1 closed, copy invariant nailed (tm_copy_refresh 24/0)

- **Gate 1 (resource) RESOLVED — NOT missing.** Danielle's "computability of recursive functions" =
  `ComputabilityOfRecursiveFunctions.pdf` (**Shepherdson-Sturgis URM** paper) in the crate root (read via
  `pdftotext` / `nix-shell -p poppler-utils`). My "can't find it" was an error (searched for Lean/dirs, not a
  top-level PDF; hadn't yet read `project_gap2_g2f_route_decision` which names it). S-S **confirms the bespoke
  route (i)** compositional style: URM macros `C(m,n)` copy (= move-twice with auxiliary storage), `O(n)`
  clear, all built from `P/D/J` and composed as subroutines — exactly the gadget-lemma discipline here. It does
  NOT obviate the emitter. (S-S's copy uses a scratch register = the plan's rejected "option A"; the n=5 mark is
  the in-place variant Danielle already chose — both are "move-twice with auxiliary storage", same idea.)
- **Gate 2 (copy pre/post) PINNED — drift-free closed form, the uncertainty is GONE.** The marked-copy left
  tape is `copy_u(j,M,G) = repunit(j) + m^(j+G)·(5·repunit(j) + m^j·repunit(M−j))` (`tm_copy_refresh.rs`),
  reading low→high `[temp: j ones][G blanks: sep+gap][master: j fives (copied) then (M−j) ones]`. **NO position
  drift**: depositing a temp one (`u·m+1`) + marking a master one (`1→5` in place) preserve `G` and the master
  layout every iteration. Endpoints verified: `lemma_copy_u_start` (`copy_u(0,M,G)=m^G·repunit(M)`, the
  post-`block_loop` input), `lemma_copy_u_end` (`copy_u(M,M,G)=repunit(M)+m^(M+G)·5·repunit(M)`, temp built /
  master all fives), `lemma_copy_u_end_unmarked` (un-mark `5→1` ⟹ `dec_u(M, repunit(M)·m^G)` — fresh
  `M`-counter, master preserved at gap `G`, ready for the next `block_loop`). Plus `lemma_pow_nat_add`
  (`m^(a+b)=m^a·m^b`, was missing). So the master IS `M` ones (`M=exponent`); `G` is constant across a phase's
  4 power-blocks. **REMAINING build (next session, all design-certain now):** the `j:0→M` iteration lemma
  `copy_u(j)→copy_u(j+1)` — per step the region-walks `[seek over temp-`1`s (q_a) → gap-`0`s (q_b, reuse
  `seek_left_blanks`) → master-`5`s (q_c) → stop on the first `1` = lowest unmarked master one]` + mark
  `(q,1,5,q',R)` + symmetric return + **deposit a temp one**; then the `5→1` un-mark pass + `copy_refresh`
  assembly composing `lemma_copy_u_start`→iteration×M→`lemma_copy_u_end`→unmark→`lemma_copy_u_end_unmarked`.
  - **⚠ KEY MECHANICS NOTE (uncovered this session):** distinct STATES per region disambiguate temp-`1`s from
    master-`1`s (the seek can't "walk until a 1" — temp is also `1`s). And the **deposit is NOT a raw `u·m+1`**:
    an R-move that prepends a `1` to `u` PULLS the output's low digit off `v` (corrupts output) and a single
    R+L round-trips to a no-op. The correct deposit **mirrors `dec_temp`'s erase** (`tm_dec_master.rs`): grow
    temp at its HIGH end (the temp/master separator) via the **pile round-trip** — walk-out piling temp onto
    `v`, write a `1` at the separator (was `0`), walk-back restoring — reusing `lemma_walk_left_prefix` /
    `lemma_walk_back_prefix`. So the iteration is a `dec_temp`-shaped gadget (insert instead of erase), NOT new
    machinery — tractable, just careful. The output `v` round-trips through every region-walk (pile/un-pile).

---

## SESSION UPDATE 2026-06-27 (N+6) — copy_u switched to FIXED stationary-master; the GENERAL marked-copy ITERATION is DONE (crate 896/0)

**The N+5 "deposit" design was WRONG and has been replaced (co-designed with Danielle, port 8051).** The N+5
note above ("grow temp at its HIGH end") is arithmetically `u + m^j` (master stationary). But the *verified*
`copy_u` endpoints at the time used the DRIFT closed form `m^(j+G)` (master drifts `G → M+G`), which forces a
full `u·m+1` shift per iteration — and that shift cannot preserve the output `v` cleanly in our convention
(`u` = LEFT tape, `v` = output = RIGHT tape; a raw R-move shift pops `v`'s low digit). The tension was real.

**RESOLUTION = switch `copy_u` to the FIXED (stationary-master) closed form** so the cheap high-end deposit
(`+m^j`, no shift, no `v`-corruption) is CORRECT:
```
  copy_u(j, M, G) = repunit(j) + m^G · (5·repunit(j) + m^j·repunit(M−j))      [master factor m^G, NOT m^(j+G)]
```
Master sits at the FIXED position `G`; temp grows at its HIGH end INTO the gap (gap shrinks `G → G−j`). Needs
`G ≥ M` (else temp overruns the master), **guaranteed**: at every copy_refresh the gap `G = k·i ≥ i = M` (the
phase's shared exponent). Endpoints re-proven: start IDENTICAL (`m^G·R(M)`); end `R(M)+m^G·5·R(M)`;
end-unmarked `dec_u(M, m^(G−M)·R(M))` (now requires `G ≥ M`). **The N+5 "KEY MECHANICS NOTE" is superseded** —
ignore its "deposit = high-end / NOT u·m+1" framing as a vestige of the drift design; the FIXED design's deposit
IS the high-end insert and it IS correct.

### What got BUILT and VERIFIED this session (`tm_copy_refresh.rs`, module 24→63, crate 857→896, all 0 errors)

The **general marked-copy iteration `copy_u(j) → copy_u(j+1)` is COMPLETE** (case `2 ≤ j < M`, gap `g−j ≥ 2`):

- **Arithmetic core.** `lemma_repunit_high` (`R(j+1)=R(j)+m^j`); `lemma_copy_u_iter_arith`
  (`copy_u(j+1) = copy_u(j) + 4·m^(g+j) + m^j`, via `5+m·R(M−j−1)−R(M−j)=4`); `master_at(j,M)=5·R(j)+m^j·R(M−j)`
  spec fn + `lemma_copy_u_master` (`copy_u = R(j)+m^G·master_at`) + `lemma_master_at_step`
  (`master_at(j+1)=master_at(j)+4·m^j`). `lemma_pow_nat_add` (`m^(a+b)=m^a·m^b`).
- **Generic single-symbol run-walks** (the `s`-generalization of `walk_left_prefix`/`walk_back_prefix`, reused
  for temp `s=1` and master fives `s=5`): `lemma_run_walk_left`, `lemma_run_walk_right`, `lemma_pile_sym_div_mod`.
- **The DEPOSIT** (`+m^j`): `lemma_deposit` — the `dec_temp` MIRROR, 4 quintuples (peel / walk-left temp /
  INSERT-turnaround `(q_dw,0,1,q_bk,R)` writing `1` at the separator / walk-back), `dec_u(j,w)→dec_u(j,w)+m^j`,
  `2j+2` steps, `w%m==0`.
- **The MARK** (`+4·m^(g+j)`): `lemma_mark_fwd` (forward seek: peel→temp `q_t`→t2g transition→gap+fives `q_a`,
  landing on the lowest unmarked master one, `g+j+1` steps) + `lemma_mark` (full: fwd ∘ mark-step
  `(q_a,1,5,q_rf,R)` ∘ return leg [`run_walk_right` fives, rf2g, `seek_right_blanks` gap, rg2t, `run_walk_right`
  temp], `2·(g+j+1)` steps, **11 quintuples**, output `v` fully round-tripped). State machine: temp in `q_t`,
  gap+fives+mark in `q_a` (NO `(q_a,1,1,·)` quint, so the master-one STOP is unambiguous), return in `q_rf/q_rg/q_rt`.
- **One iteration:** `lemma_copy_iter` — composes mark ∘ deposit, **wiring the deposit's home state to the
  mark's exit `q_rt`** (peel `(q_rt,0,0,q_dw,L)` vs mark-return `(q_rt,1,1,q_rt,R)` disambiguated by symbol).
  `{u: copy_u(j)}→{u: copy_u(j+1)}`, `2·(g+j+1)+(2j+2)` steps. ✅ FIRST-TRY verify on `lemma_mark`.

### REMAINING (next session) — the iteration is the hard core; the rest is mechanical-but-lengthy

1. **Edge iterations** (the loop needs ALL `j∈0..M−1`, and `g−j` can be `1`):
   - **`j=0`** (no temp, no fives): mark = peel → `seek_left_blanks` gap → master-one, mark, `seek_right_blanks`
     gap → pivot. No temp/fives walks. (And `master_at(0,M)%m = R(M)%m = 1`, so the gap-seek lands on a `1` not a `5`.)
   - **`j=1`** (1 temp, 1 five): `lemma_mark_fwd`/`lemma_mark` ALMOST work (`run_walk_left`/`run_walk_right` handle
     `len=0`), BUT the return's S10 (`run_walk_right` temp, `rem0=j−2`) is invalid; for `j=1` the return ENDS at
     S9 (the `rg2t` transition lands `a=0` at the pivot directly). So `j=1` needs its own return tail.
   - **`g−j=1`** (gap exactly 1; happens when `g=M`, `j=M−1`): the `t2g` transition consumes the only gap blank,
     so `seek_left_blanks(g_seek=g−j−2=−1)` is invalid — skip the gap-seek (head already on the first five after
     the transition). Likewise `seek_right_blanks` on the return. Combines with the `j` value.
   These reuse all the existing primitives; each is a `lemma_copy_iter`-shaped variant with the affected
   sub-steps dropped/adjusted. (Consider: a single edge-tolerant `lemma_mark` with `if` branches on
   `j∈{0,1}` and `g−j==1`, vs. separate lemmas. Separate is probably cleaner for Z3.)
2. **The `j:0→M` LOOP** — induct `copy_u(j)→copy_u(M)` composing `lemma_copy_iter` (+ edges). Needs a fuel
   spec fn summing `2·(g+j+1)+(2j+2)` over `j`. Start = `lemma_copy_u_start` (`copy_u(0)=m^G·R(M)`).
3. **UNMARK pass** — `5→1` over the master's `M` fives: `copy_u(M)=R(M)+m^G·5·R(M) → R(M)+m^G·R(M)` =
   `dec_u(M, m^(G−M)·R(M))` (`lemma_copy_u_end_unmarked`). A `run_walk`-style pass writing `1` over each `5`
   (seek to the master, walk the fives writing `1`, return). 
4. **`copy_refresh` assembly** — start ∘ loop ∘ unmark ∘ end_unmarked → the next `block_loop` home config.
5. Then `psc_act` window assembly (template `gap2_psc_rp.rs`), **16-block sequencing**, R-cmp/R-S/R-C/R-MC/B-W.

⚠ `tm.n >= 5` (the `5` marker, per the N+4 n=5 bump decision) is a precondition of all the mark/copy lemmas.
⚠ Use the crate-local `./check.sh` (Lean backend + group-theory export), NOT the top-level one.

### Edge-case design note (uncovered N+6, for whoever builds the edges)

The general `lemma_mark`/`lemma_copy_iter` couple **temp-count == fives-count == j** (both come from `copy_u(j)`).
The walks use `len = j−1`: `run_walk_left/right` handle `len = 0` (fire 1 step), but `j = 0` gives `len = −1`
(skip the walk) and the return's S10 `run_walk_right` temp has `rem0 = j−2` (invalid at `j ≤ 1`). Concretely:
- **`j = 1`** is "almost general": forward works (walks fire `len=0`), but the return ENDS at the `rg2t`
  transition (S9 lands `a=0` at the pivot directly, `pile_sym(out·m,1,0)=out·m`, `%m=0`) — so DROP S10.
- **`j = 0`** is special: no temp, no fives. **The trap: the return has no temp landmark, so the gap-seek-back
  can't stop at the pivot** (pivot and gap are both `0`; `seek_right_blanks` would overshoot into the output).

**Promising fix — DEPOSIT-FIRST (deposit ∘ mark instead of mark ∘ deposit).** Arithmetic still closes:
`copy_u(j) +m^j (deposit) = R(j+1)+m^G·master_at(j,M)`, then `+4·m^(g+j) (mark) = copy_u(j+1)`. With deposit
first, the **temp count is `j+1` (always ≥ 1)** during the mark, so the return ALWAYS has a temp landmark — the
`j=0` pivot-boundary trap disappears. The remaining edge is only **fives-count `f = j = 0`** (skip the
fives-walk/back), plus the **`g−j = 1`** gap edge (only when `g = M`, `j = M−1`: the `t2g`/`rf2g` transition
eats the only gap blank ⟹ skip `seek_left/right_blanks`). BUT deposit-first **decouples temp-count (`j+1`) from
fives-count (`j`)**, so `lemma_mark` must be re-parametrized over separate `(t, f)` counts (currently `t=f=j`).
That is a re-derivation of the mark/iteration. **DECISION FORK for next session (consider co-design w/ Danielle):**
(a) keep mark∘deposit + write bespoke `lemma_copy_iter_j0` (with a non-pivot-seek return) and `_j1` + a `g−j=1`
variant; or (b) switch to deposit∘mark + generalize `lemma_mark` to `(t,f)` counts so only `f=0` and `g−j=1`
remain. (b) is cleaner for the loop but reworks the verified `lemma_mark`. The general `2≤j<M, g−j≥2` core is
verified and reused either way.

---

## SESSION UPDATE 2026-06-27 (N+7) — ALL marked-copy EDGES + the full j:0→M LOOP + the general UNMARK sweep DONE (module tm_copy_refresh 63→137, crate 947/0)

**The DECISION FORK above (N+6 (a) vs (b)) was resolved to (a)-refined: mark-first, with `j=0` the one
deposit-first exception.** The key correction to the N+6 note: the local model initially favoured (b)
(uniform deposit-first), but working through the gap geometry showed **deposit-first makes the `g−j=1`
(`G=M`) case WORSE** — growing temp first eats the lone gap blank, destroying the separator the mark's
`t2g`/seek need; whereas **mark-first handles `g−j=1` cleanly** (the `t2g` consumes the single gap blank,
the deposit refills it afterward). So mark-first is the base. Only `j=0` (no return landmark) must
deposit-first. The decisive geometric fact: at `g−j=1`, mark-first keeps the separator FOR the mark and
fills it AFTER; deposit-first removes it BEFORE. (See the commit log for the full reasoning.)

### What got BUILT and VERIFIED this session (all additive, no assume/admit/external_body)

- **`g−j=1` edge** (commit `4d12060`): `lemma_mark_fwd_gj1` + `lemma_mark_gj1` + `lemma_copy_iter_gj1`.
  The first intra-phase refresh has `G=M`, so the last iteration `j=M−1` has gap 1. `t2g` consumes it
  and the forward lands DIRECTLY on the master five (no gap-seek; S4/S8 dropped). **Same 11 quints as the
  general `lemma_mark`** — one TM/quint-set drives both; the loop dispatches on `g==j+1`.
- **`j=1` edge** (commit `fda4c40`): `lemma_mark_j1` + `lemma_copy_iter_j1`. The forward already works via
  `lemma_mark_fwd` (precondition LOWERED `2≤j` → `1≤j`, re-verified). The return drops the trailing temp
  walk-back (S10): the single temp one is consumed by `rg2t`, landing the head on the pivot directly. Exit
  IDENTICAL to general `lemma_mark` with `j=1` (`q_rt`, pivot, `copy_u(1)+4m^(g+1)`), so it fits the home
  cycle. Used for `j=1` when `M≥3` (`g=G≥M≥3`, gap `g−1≥2`).
- **`j=0` edge** (commit `fee5935`): `lemma_mark_j0` + `lemma_copy_iter_j0`, DEPOSIT-FIRST. Grow temp to
  one (via `lemma_deposit`'s `j=0` branch — the landmark), then a `(temp=1, fives=0)` mark flips the
  master's single low one → `copy_u(1)`. Own deposit/mark states, exits in `q_rt0` (wired to the loop
  home). `G≥3` (the `M≥3` regime).
- **the full loop** (commit `af7d063`): `copy_loop_fuel` + `lemma_copy_loop_general` (the general-iteration
  middle induction `copy_u(lo)→copy_u(hi)` over the home cycle, `2≤lo≤hi≤M`, `hi≤g−1`); `lemma_copy_prefix`
  (`copy_u(0)→copy_u(2)` = j0∘j1, verifies the j0→home wiring); `full_copy_fuel` + **`lemma_copy_loop`**
  (`copy_u(0)→copy_u(M)`, `M≥3`, `g≥M`, dispatching `g==M` → trailing gj1 vs `g>M` → pure general middle).
  Also strengthened `lemma_repunit_high`'s two hint-free asserts (cache-invalidation re-verified it in the
  new, polluted trigger env).
- **the general UNMARK** (commit `b03edf3`): `lemma_unmark_fives_left` (a `run_walk` that READS 5 / WRITES
  1 — the only genuinely new primitive) + `lemma_unmark_fwd` (forward + convert the M fives to ones,
  landing above the master) + **`lemma_unmark`** (`copy_u(M) → dec_u(M, m^(g−M)·R(M))` in one sweep:
  forward, TURN onto the master high one, walk back). General case `M≥2, g≥M+2` (the `k≥2` refreshes).

### ⚠ KEY DESIGN FINDING (the next blocker) — the loop→unmark wiring needs a SELF-TERMINATING guard

The arithmetic core is DONE, but composing `lemma_copy_loop` (ends `copy_u(M)` at `q_home`) with
`lemma_unmark` (starts at `q_uh`) into a REAL machine is blocked by state wiring:

- `q_home` on the pivot fires the MARK peel `(q_home,0,0,q_t,L)` — i.e. it would start ANOTHER mark
  iteration. To switch to unmark we need a DIFFERENT behaviour, but the pivot is just a `0`.
- Making the last iteration exit at a distinct `q_uh` does NOT work: the deposit insert `(q_dw,0,1,q_bk,R)`
  and peel `(q_rt,0,0,q_dw,L)` are SHARED across all iterations, so a different `q_bk`/`q_dw` for the last
  one CONFLICTS (same source+symbol, two targets ⟹ non-deterministic, `tm_wf`-illegal).
- Setting `q_uh = q_home` is illegal for the same reason (two `(q_home,0,0,·)` quints).

**The right fix = make the marked-copy SELF-TERMINATING.** Currently the forward seek does the gap-seek AND
the fives-walk BOTH in `q_a` (`(q_a,0,0,q_a,L)` gap, `(q_a,5,5,q_a,L)` fives), so the "blank above the
all-fives master" (reached only at `j=M`, when there is NO unmarked one) is indistinguishable from a gap
blank and `(q_a,0,0,q_a,L)` would walk up into the void. **SEPARATE the fives-walk into its own state
`q_b`**: `(q_a,5,5,q_b,L)` enters `q_b` on the first five, `(q_b,5,5,q_b,L)` crosses the rest, then
`(q_b,1,5,q_rf,R)` marks an unmarked one (copy continues) OR `(q_b,0,0,q_turn,R)` fires on the blank above
the all-fives master → the machine NATURALLY switches to the unmark turn. This makes the loop
self-terminating (no external count) and the unmark its natural continuation. It reworks `lemma_mark_fwd`
(+ `lemma_mark`, + the gj1/j1/j0 variants, + the loop) to thread `q_b` — a real but mechanical
re-verification. **This is the next design piece (consider co-design w/ Danielle).**

### REMAINING (after the self-terminating rework)

1. **Self-terminating guard** — separate fives-state `q_b`; rework mark forward + edges + loop to thread it.
2. **`g=M` no-gap UNMARK** — the `k=1` refresh (temp flush against master, no gap-seek). Mirror `lemma_unmark`
   without the gap legs (cf. `lemma_mark_gj1`'s drop of S4/S8).
3. **small-M whole-copy lemmas** (`M∈{1,2}`) — exponents `M=a+1, b+1` can be 1 or 2. `lemma_copy_loop`
   requires `M≥3`. `M=1` (j0 only, gaps `G∈{1,2}`) and `M=2` (j0∘j1, j1 gap edge `G=2`) are bespoke;
   also j0's `G∈{1,2}` no-/tight-gap sub-cases (deposit shrinks the gap, so j0's edge is at `G=2`).
4. **`copy_refresh` assembly** — loop ∘ (self-terminating guard) ∘ unmark → the next `block_loop` home
   config (`dec_u(M, m^(G−M)·R(M))`). Dispatch `g==M` (no-gap unmark) vs `g>M` (general unmark).
5. **16-block sequencing**, `psc_act` window, R-cmp/R-S/R-C/R-MC/B-W → discharge `ceer_realizes` (last GAP-2 piece).

⚠ `tm.n ≥ 5` is a precondition of all mark/copy/unmark lemmas. Use the CRATE-LOCAL `./check.sh`.

### N+7 addendum — the self-terminating guard need NOT discard `lemma_unmark` (reuse option)

Working through the guard design surfaced a subtlety: in the self-terminating machine the SHARED forward
PRESERVES the fives (`(q_b,5,5,q_b,L)`) so it can detect the all-fives master at `j=M`. The un-mark, by
contrast, CONVERTS fives (`5→1`). So a naive "fall-through + convert walking DOWN" would be a NEW un-mark
structure that obsoletes the verified `lemma_unmark` (which converts walking UP from a pivot start). **Two
options:**
- **(efficient, new)** at the `j=M` fall-through (head ABOVE the all-fives master, `q_turn`), walk DOWN
  converting `5→1` in one pass, then continue down through gap/temp to the pivot. One extra pass; a NEW
  convert-down un-mark (reuses `lemma_unmark_fives_left`'s arithmetic but mirrored R-ward).
- **(correctness-first, REUSES `lemma_unmark`)** at the `j=M` fall-through, just WALK BACK DOWN to the
  pivot (cross the M fives + gap + M temp ones in a return state `q_ret`, landing on the pivot in
  `lemma_unmark`'s home state `q_uh`), then run the VERIFIED `lemma_unmark` (which re-seeks up, converts,
  returns). Costs ~2 extra O(g) traversals per refresh but reuses the whole verified un-mark. Since the
  goal is CORRECTNESS (not speed), prefer this — only the `j=M` detection-forward + a plain walk-back are
  new; `lemma_unmark` (and `lemma_copy_loop`) stay intact.

So the minimal self-terminating rework = thread `q_b` through the forward/edges/loop (so `j=M` detection
works) + a `lemma_mark_terminate` (the `j=M` forward → fall-through → walk-back-to-pivot) + the assembly
`loop ∘ terminate ∘ lemma_unmark`. The g=M no-gap unmark and small-M remain as before.

## SESSION UPDATE 2026-06-27 (N+8) — SELF-TERMINATING GUARD + BOUNCE + FULL copy_refresh ASSEMBLY DONE (module tm_copy_refresh 137→165, crate 998/0)

**REMAINING items 1 and 4 are now CLOSED** (the N+7 "next blocker"). The general-case `copy_refresh`
(`M ≥ 3`, `g ≥ M+2`) is one verified deterministic machine. Route taken: **Option A (correctness-first,
REUSES `lemma_unmark`)**, co-design-confirmed with the local model.

### What got BUILT and VERIFIED (all additive, no assume/admit/external_body)

- **(item 1) the q_b self-terminating guard — DONE.** Threaded a fresh fives-state `q_b` + transition
  index `i_a2b` through the WHOLE mark/loop stack **in place** (strict generalization: `q_b == q_a`
  recovers the old single-state forward). The forward now does **gap-walk in `q_a`** (reads `0` → keep
  seeking) then a one-step transition `(q_a,5,5,q_b,L)` (`i_a2b`) into **fives-walk in `q_b`**
  (`(q_b,5,5,q_b,L)`); the mark fires from `q_b` (`(q_b,1,5,q_rf,R)`). At `j=M` (all fives, no unmarked
  one) `q_b` instead reads the blank above the master → the dedicated `(q_b,0,0,q_turn,R)` turn. So `q_b`
  reacts to `5`/`1`/`0` distinctly — **self-termination with NO state conflict** (the design's whole
  point). Reworked: `lemma_mark_fwd`/`_gj1` (forward bodies: transition + q_b walk, with a `j==1` vs `j≥2`
  split where the single five lands directly on the unmarked one), `lemma_mark`/`_j1`/`_gj1`,
  `lemma_copy_iter`/`_j1`/`_gj1`, `lemma_copy_loop_general`/`_prefix`/`_loop`. **`j=0` untouched** (no
  fives at `j=0`). Commit `38913c2`.
- **`lemma_terminate_fwd` — DONE.** The `j=M` forward: mirrors `lemma_unmark_fwd` but PRESERVES the fives
  (`5→5`) and ends above the master in `q_b` (`{0, pile_sym(P_g,5,M), 0, q_b}`). Reuses the loop's forward
  quints — NO new quints. Commit `…terminate_fwd`.
- **(Option A) `lemma_mark_terminate` — DONE.** `copy_u(M)@q_home → copy_u(M)@q_ret`: detect (terminate_fwd)
  → TURN down `(q_b,0,0,q_turn,R)` → walk back NON-destructively reconstructing `copy_u(M)` (master fives
  crossed as `5`s, gap, temp) → land on the pivot in `q_ret`. Mirror of `lemma_unmark`'s S7–S12 over `5`s.
  Config UNCHANGED; only the state advances `q_home → q_ret` (= `lemma_unmark`'s home `q_uh`). 6 fresh
  walk-back quints (`q_turn`/`q_turng`/`q_ret`). Commit `…mark_terminate`.
- **(item 4) `lemma_copy_refresh` — DONE.** The capstone: `copy_u(0) → dec_u(M, m^(g−M)·R(M))` as ONE
  deterministic `tm_run`, composing `lemma_copy_loop ∘ lemma_mark_terminate ∘ lemma_unmark`. The three
  phases SHARE the forward quints (loop ↔ terminate) and chain `q_home → q_ret → q_urt`. `copy_refresh_fuel
  = full_copy_fuel + 2·(2g+2M+2)`. ~73 params (24 states + 46 quint indices) — the parametric machine the
  16-block sequencing will instantiate. Commit `…copy_refresh`.

**Trigger-instability note:** the base-hash changes from each new/edited function destabilized a few
PRE-EXISTING asserts elsewhere in the module (`lemma_unmark` S7 turn `0*m==0`; `lemma_seek_right_blanks`
`pow_nat(m,1)==m`/`m*1==m`). Each fixed by spelling out the multiplication-by-0/1 step. These are the
"~2% false-miss" SST churn; sound, but worth knowing the next edit may re-poke a different assert.

### REMAINING (the higher-level wiring — ALL copy_refresh edge cases now DONE)

2. **`g=M` no-gap copy_refresh** — ✅ **DONE (N+9).**
3. **small-M whole-copy** (`M∈{1,2}`) — ✅ **DONE (N+9): M=2 {g=2 no-gap, g≥4 general}, M=1 {g=1, g=2, g≥3}.**
   **`copy_refresh` is now machine-checked for EVERY `(M≥1, g≥M)` the fixed emitter TM can encounter.**
5. **16-block sequencing** + `psc_act` window + R-cmp/R-S/R-C/R-MC/B-W → discharge `ceer_realizes`. This is
   where a CONCRETE `tm` is built (distinct quints at distinct indices, `tm_wf` proven) and fed to the
   per-`(M,g)` copy_refresh lemmas (the 16-block sequencer case-splits on `M∈{1,2,≥3}` × `g∈{M, M+1(only M=1), ≥M+2}`);
   the parametric `q_b`/turn determinism (5/1/0 distinct) is already discharged by construction there.

## SESSION UPDATE 2026-06-27 (N+9) — g=M NO-GAP copy_refresh DONE + M=2 GENERAL DONE (module tm_copy_refresh 165→194, crate 998→1027)

**Item 2 (`g=M` no-gap) CLOSED, and item 3 partially advanced (M=2 general).** All additive, 0 errors,
no assume/admit/external_body. Two commits (`f44ba13` no-gap, `bb22eab` M=2-general).

### What got BUILT and VERIFIED

- **Two arithmetic helpers:** `lemma_repunit_add` (`R(a+b)=R(a)+m^a·R(b)`, the repunit analog of
  `lemma_pow_nat_add`; identifies the no-gap unmark's `2M` contiguous ones as `R(2M)=dec_u(M,R(M))`) +
  `lemma_pile_sym_concat` (`pile_sym(pile_sym(v,s,a),s,b)=pile_sym(v,s,a+b)`, folds the temp+master ones-runs).
- **`g=M` no-gap machine lemmas** (`M ≥ 2`; the gap legs collapse — there is NO blank between temp and
  master, and after the unmark temp+master become ONE `2M`-contiguous-ones block):
  - `lemma_terminate_nogap_fwd` — forward of the self-terminating bounce; the `t2g`/gap/`a2b` legs collapse
    into ONE direct quint `(q_t,5,5,q_b,L)` (temp lands directly on the master five). `2M+1` steps.
  - `lemma_mark_terminate_nogap` — full bounce `copy_u(M,M,M)@q_home → @q_ret`; walk-back `m2g`/gap/`g2t`
    collapse into `(q_turn,1,1,q_ret,R)`. `4M+2` steps (`= 2g+2M+2` at `g=M`).
  - `lemma_unmark_nogap` — `copy_u(M,M,M) → dec_u(M,R(M))@q_uw`; convert via `(q_ut,5,1,q_uf,L)` +
    `(q_uf,5,1,q_uf,L)`, then TURN and walk ALL `2M` ones down to the pivot in ONE state `(q_uw,1,1,q_uw,R)`
    (no gap landmark — `lemma_run_walk_right` over the contiguous block). `4M+2` steps.
  - `lemma_copy_refresh_nogap` (`M ≥ 3` capstone) — `lemma_copy_loop` (g==M branch) ∘ `mark_terminate_nogap`
    ∘ `unmark_nogap`; fuel `copy_refresh_fuel(M,M)`.
- **M=2 general (`g ≥ M+2 = 4`):** LOWERED `lemma_copy_refresh` precond `3≤big_m` → `2≤big_m` and branched
  PHASE 1: for `M=2` the loop IS `lemma_copy_prefix` (`copy_u(0)→copy_u(2)==copy_u(M)`, the general middle
  `copy_loop_fuel(2,2,g)==0`), for `M≥3` the full `lemma_copy_loop`. So M=2 at `g≥4` (the `k≥2` refreshes of
  an exponent-2 phase) is covered with NO new edge lemmas. `terminate`/`unmark` already require only `M≥2`.

### KEY SCOPING ANALYSIS (the gap regimes per M — worked out this session, ⚠ for Danielle to sanity-check)

The fixed emitter TM processes the exponent `M=i` as RUNTIME data, so the SAME quints must drive the copy
for every `M≥1`; per-M correctness is proven by separate lemmas the 16-block sequencer case-splits over.
The refresh gap is `G = k·M` (master migrates up by `M` per power-block via the inter-block shift; the
local model confirmed this is by-design, NOT a forced consequence — *if* the emitter is later changed to
keep the master stationary, every refresh would be `g=M` and the general `g≥M+2` path becomes dead code.
Worth a Danielle confirmation before building M=1, since it changes the needed gap range). Under `G=k·M`:
- **M≥3:** `g=M` (no-gap, k=1) ✅ + `g=kM≥2M≥M+2` (general, k≥2) ✅ — BOTH DONE.
- **M=2:** `g=2` (no-gap, k=1) ❌ TODO + `g=2k≥4` (general, k≥2) ✅ DONE. (No `gap=1` since `G` even.)
- **M=1:** `g=k` for k=1,2,3,… → `g=1` (no-gap), `g=2` (**gap=1**, the `g=M+1` regime — a THIRD edge, neither
  no-gap nor general), `g≥3` (general). ALL ❌ TODO.

### REMAINING small-M (the new degenerate edge machines needed)

- **M=2 no-gap (`g=2`):** needs a 2-iteration loop `copy_u(0,2,2)→copy_u(2,2,2)` = a NEW `j=0`-at-`g=2` edge
  (deposit-first; the mark's gap-seek `S4`/`S8` vanish, `g-3<0`) + a NEW `j=1`-`gj1` edge (`lemma_mark_fwd_gj1`
  requires `2≤j`: at `j=1` the `a2b` crosses the lone five and lands DIRECTLY on the unmarked one — NO
  fives-walk, `j-2<0`; ENSURES of the existing gj1 lemmas are already correct for `j=1`, only the BODY needs
  the `j==1` branch, cf. how `lemma_mark_fwd` was lowered to `1≤j` with a `j==1` vs `j≥2` split). Then
  `lemma_copy_loop_m2_nogap` (j0∘j1gj1) ∘ existing `terminate_nogap`/`unmark_nogap` (both already `M≥2`).
- **M=1 (all gaps):** the single-master-one copy. `g=1` (no-gap), `g=2` (gap=1), `g≥3` (general). Most
  degenerate; each a bespoke short machine. Build last.

After small-M: **16-block sequencing** (build the CONCRETE `tm`, `tm_wf`, feed the per-(M,g) copy_refresh
lemmas) + `psc_act` window + R-cmp/R-S/R-C/R-MC/B-W → discharge `ceer_realizes` → drop `axiom_ceer_fp_embedding`.

### ✅✅ ADDENDUM (same session N+9, cont.) — ALL small-M DONE; `copy_refresh` COMPLETE for every (M,g)

Both the M=2-no-gap and M=1 (all 3 gaps) "TODO"s above are now CLOSED (module 194→329, crate 1027→1162,
0 errors, additive, no escape hatches). Commits `4d1209a` (M=2 no-gap), `382ef7d` (M=1 general), `cd2e1b5`
(M=1 no-gap + gap-1). The predicted recipes held exactly:
- **M=2 no-gap:** `lemma_mark_j0_g2`/`lemma_copy_iter_j0_g2` (j=0, gap-seeks vanish) + `lemma_mark_fwd_j1gj1`
  /`lemma_mark_j1gj1`/`lemma_copy_iter_j1gj1` (j=1 gj1, a2b lands directly, return ends at S9) +
  `lemma_copy_loop_m2_nogap` + `lemma_copy_refresh_m2_nogap` (loop ∘ terminate_nogap ∘ unmark_nogap, 40 steps).
- **M=1 general (g≥3):** `lemma_unmark_m1` + `lemma_mark_terminate_m1` (single five; every `M−1`-length
  sub-walk vanishes) + `lemma_copy_refresh_m1` (single j0 ∘ terminate_m1 ∘ unmark_m1, 6g+12 steps).
- **M=1 g=2 (gap-1):** `lemma_unmark_m1_g2` + `lemma_mark_terminate_m1_g2` (both gap-seeks vanish) +
  `lemma_copy_refresh_m1_g2` (copy via existing `lemma_copy_iter_j0_g2(big_m=1)`, 24 steps).
- **M=1 g=1 (no-gap):** `lemma_copy_iter_j0_g1` (BESPOKE 4-step MARK-FIRST copy — deposit-first would make
  temp+master adjacent 1s with no separator) + `lemma_unmark_m1_nogap` + `lemma_mark_terminate_m1_nogap`
  (2 contiguous ones) + `lemma_copy_refresh_m1_nogap` (16 steps).

**Net: `copy_refresh` is machine-checked for EVERY (M≥1, g≥M).** The 16-block sequencer will dispatch
`lemma_copy_refresh{,_nogap}` (M≥2), `_m2_nogap` (M=2,g=2), `_m1{,_g2,_nogap}` (M=1) by case-split on the
runtime `(M,g)`. **NEXT = the 16-block sequencing** (build the concrete `tm`/`tm_wf`, thread the per-(M,g)
dispatch) → `psc_act` window → R-cmp/R-S/R-C/R-MC/B-W → discharge `ceer_realizes` → drop the axiom.
⚠ Recurring proof idiom for these edges (learned this session): split apply_quint conjunctions with mixed
div/mod into a raw-form assert + per-field `nonlinear_arith`; establish `pow_nat(m,1)==m` etc. via
`lemma_pow_nat_unfold` + `nonlinear_arith requires` (NOT a bare `by{}` block — it drops the `m·1` step).

---

## SESSION UPDATE 2026-06-27 (N+10) — GAP-GROWTH QUESTION RESOLVED + the per-power-block PERIODIC step (all 4 variants) DONE (crate 1162→1178/0)

**✅ THE `G = k·i` GAP-GROWTH ASSUMPTION IS WRONG — the master is STATIONARY; fix `g = M + 2`.** The
N+9 scoping note (and `copy_u`'s doc comment, lines 62–76) assumed the gap grows `G = k·i` across a phase's
refreshes (master "migrates up by M per `block_loop`"). **Traced the full `copy_refresh → block_loop` cycle
arithmetically (local-model-confirmed, port 8051) and it does NOT migrate:**

```
  copy_u(0,M,g) = m^g·R(M)                        [master R(M) at gap g, no temp]
    ──[copy_refresh]──▶  dec_u(M, m^(g−M)·R(M))    [fresh temp R(M) + master still at g]
    ──[block_loop ]──▶  dec_u(0, m^M·w) = m^M·m^(g−M)·R(M) = m^g·R(M) = copy_u(0,M,g)
```

`block_loop` multiplies the master content by `m^M`, but that EXACTLY compensates the `m^M` the consumed
`M`-cell temp occupied — net absolute position unchanged. So **the gap is CONSTANT for every power-block in
a phase**, and one fixed `g` works throughout.

**The magic uniform choice is `g = M + 2`:**
- `block_loop` needs a `0`-separator below the master (`w % m == 0`, so the dec-walk stops). With `g = M+2`,
  `w = m^(g−M)·R(M) = m²·R(M)`, `w % m == 0`. ✓ (needs `g ≥ M+1`.)
- `copy_refresh` (`M ≥ 2`) needs `g ≥ M+2` ✓ exactly; `copy_refresh_m1` needs `g ≥ 3 = M+2` ✓.
- So **only `M ∈ {1, ≥2}` dispatch is needed** — the no-gap (`g=M`) and `g=M+1`-edge refreshes (`_nogap`,
  `_m2_nogap`, `_m1_g2`, `_m1_nogap`) are all UNUSED by the sequencer. (They stay in the crate as verified
  robustness; the N+9 per-`(M,g)` dispatch table collapses to per-`M`.)

**✅ THE PERIODIC STEP — all 4 variants DONE (`tm_power_block.rs` 8/0 + `tm_power_block_m1.rs` 8/0).**
`lemma_power_block_step_block{1,3}` (`M ≥ 2`, `g ≥ M+2`) + `_block{1,3}_m1` (`M = 1`, `g ≥ 3`). Each composes
`copy_refresh ∘ block_loop` into ONE deterministic run:
`copy_u(0,M,g) @ q_dh0  →  copy_u(0,M,g) @ q_exit`, appending `seq_pow(blk, M)` to the output `v`, master
unchanged. **The bridge is FREE**: `copy_refresh`'s end config equals `block_loop`'s start config except for
the state, so identifying `q_urt := q_loop` splices them with no glue steps. For `M ≥ 2` the shared quint
`(q_urt,1,1,q_urt,R)` is passed as BOTH `i_urtemp` (copy_refresh) and `i_one_r` (block_loop) — one quint, no
determinism conflict. For `M = 1` the copy lands directly on the pivot (no temp-walk-right), so `i_one_r` is
a fresh block_loop quint. The two stacks' states are otherwise disjoint (only `q_home` names collide → the
loop's is `q_bhome`). `w % m == 0` is established in-body (`g−M ≥ 2 ⟹ m | m^(g−M) | w`), and `dec_u(0, m^M·w)
== copy_u(0,M,g)` via `lemma_pow_nat_add` + `lemma_copy_u_start`. All verified first/second try, additive.

**NEXT (the phase-level assembly, multi-session):**
1. **Singleton emits** — the 8 inter-power-block singletons (`[4]`,`[3]`,`[2]`,`[1]`,`[4,1,2]`,`[4,3,2]`)
   emit with NO counter (one `surge_emit_return_block1/3`, master inert at gap `g`, head returns to pivot).
   A `lemma_singleton_step_block{1,3}` mirroring the power-block step but skipping copy_refresh/dec.
2. **Phase chaining** — chain the 4 power-blocks + 4 singletons of `uinv_digits(b)` (then `u_digits(a)`) in
   the right low-first order (see `gap2_fam_digits`: `u_digits` = `(1)ⁱ·[4,3,2]·(3)ⁱ·[4]·(4,1,2)ⁱ·[1]·
   (4,3,2)ⁱ·[2]`; `uinv_digits` = `[4]·(4,1,2)ⁱ·[3]·(4,3,2)ⁱ·[2]·(1)ⁱ·[4,1,2]·(3)ⁱ`).
   - **The splice = STATE IDENTIFICATION** (the key structural insight): every block-step is pivot→pivot,
     so chain by identifying step_k's END-state with step_{k+1}'s START-state. Power-block start `q_dh0`
     (reads pivot-`0`, → L into copy), end `q_exit`; singleton start `q_iter` (reads pivot-`0`, surge R),
     end `q_home` (return-landing, reads `1..4` → L). The shared pivot state's reads are DISTINCT
     (`0` → next-step's first move; `1..4` → the singleton return-walk's `L`), so `tm_wf` determinism holds
     and the splice needs no glue steps. `q_exit` has no outgoing quint, so identifying it with the next
     start just adds that start's `(·,0,·)` quint; the singleton's pivot-`0` is never READ during its
     counted run (the return-walk lands ON the pivot as the terminal config), so adding a `(q_home,0,·)`
     quint for the next step is inert to the singleton lemma.
   - **MASTER MANAGEMENT = Design (A) "Rebuild-One"** (local-model co-designed, port 8051 — chosen over
     "two counters coexist" because rebuild gives a TEMPORAL firewall: phase-2's tape is independent of
     `b`, turning the global spatial invariant `dist(pivot,master₁)<dist(pivot,master₂)` into local
     transition proofs). One master alive per phase. The dovetail stores the enumerated pair as `a+1`/`b+1`
     counters directly (NOT `a`/`b` — avoids an off-by-one increment gadget at load; `load_master` is then a
     plain `copy_u(source_counter → master_dest)`, identical logic for both phases). Between phases use the
     **WIPE-AND-LOAD** pattern: a `q_clean` state (`read 1 → write 0 → L`; `read 0` boundary → R) zeroes the
     master zone FIRST (else phase-1 residue ones make phase-2's copy_u overshoot its `0`-separator and emit
     too many digits), then `load_master` copies `a+1` into the clean zone. NEW gadgets: `load_master`
     (≈ copy_refresh's marked-copy, source = stored counter) + the `q_clean` wipe.
3. **fam_digits assembly** — prove the produced output `== fam_digits(a,b)` (compose `lemma_dds_fam_relator`
   / `lemma_relnum_is_fam_digits`); its `dpack` value is `relnum(a,b)`.
4. **Concrete `tm`/`tm_wf`** (assemble5) — instantiate the threaded indices via `lemma_slot_index`; the
   `psc_act` window. Then R-cmp / R-S / R-C / R-MC / B-W → discharge `ceer_realizes` → drop the axiom.

> **⚠ N+10 FINDING — the phase chain wants the CONCRETE assemble5 tm, NOT more abstract threading.** Within
> a phase the 4 power-blocks emit DIFFERENT symbols via `(q_surge, 0, s, q_eret, R)`. Sharing `q_surge`
> across blocks is a `tm_wf` determinism CONFLICT (same `(state,read)=(q_surge,0)`, different writes `s`), so
> each block needs its OWN emit machinery (distinct states/indices). Threading 8 blocks' worth of ~100-param
> sets abstractly is impractical; the assemble5 scaffold gives each block its own window (`pc → distinct
> entry4/idx`) for free. **So the recommended next move is to build the assemble5 tm and lay the per-block
> windows, then prove the chain about the CONCRETE machine** (each step instantiates the relevant
> `lemma_power_block_step_*` / `lemma_surge_emit_return_*` via `lemma_slot_index`, exactly as `gap2_psc_rp.rs`
> instantiates `lemma_rp_copy_park`). The within-phase chain and the master-mgmt gadgets (`load_master`,
> `q_clean`) also depend on the global tape layout (where the `a+1`/`b+1` counters live relative to master /
> output) — pin that layout when building the assemble5 windows (couples with R-P's `[counters]0[scratch]
> 0[α-block]0` and the dovetail). The 4 verified `lemma_power_block_step_*` primitives are the per-block
> atoms that concrete assembly consumes.

## SESSION UPDATE 2026-06-27 (N+11) — GLOBAL TAPE LAYOUT PINNED + assemble5 STRIDE LOCKED (Danielle co-designed, port 8051)

**✅ GLOBAL TAPE LAYOUT (LOCKED).** The whole `psc_tm` tape, left→right:

```
  [ dovetail state: s | a+1 | b+1 ] 0 [ emit scratch: master 0 temp 0 output ] 0 [ α-block: stored digits ] 0 [ blanks ]
```

- **Separate output / α-block regions** (NOT a local-zip adjacency). R-cmp is a linear scan that walks
  between `emit-output` and `α-block`; the cost is negligible vs. the boundary/overflow complexity a fused
  region would force on R-P and the emitter. (Danielle's call.)
- **R-P (n=5 re-do) deposits α into the dedicated α-block region to the RIGHT**, NOT in `v` over the
  scratch. Reason: the emitter's local `v` (right of the scratch pivot) must be unobstructed so a
  power-block can grow its output without colliding; parking α in `v` would force a per-block shift-right.
  So the n=5 R-P parks α in the α-block; `v` (within the scratch's local frame) is the emitter output.
- **Confirmed flow:** `load_master` (copy persistent `a+1` → emit-scratch master) → emitter (produce
  output in scratch-`v`) → R-cmp (walk between emit-output ↔ α-block). `q_clean` wipes the scratch master
  zone between the two phases (`uinv_digits(b)` then `u_digits(a)`); WIPE-AND-LOAD per N+10.
- **Note on the local emitter frame:** a power-block step's lemma already fixes the LOCAL layout
  `[master]0[temp]0[output]` (master in `u`, output in `v`, head at the home pivot `a=0`). The global
  layout above is the embedding of that local frame into the full tape; the per-block window lemmas are
  layout-agnostic (they speak only of the local `u`/`v`), so the scaffold + window proofs do not depend on
  the global coordinates — those only matter when wiring R-P/R-cmp/R-S.

**✅ assemble5 STRIDE = 48 (LOCKED).** The n=5 (alphabet `0..5`, marker `5`) bump of `tm_assemble4`. A
triple power-block window needs 34 distinct states; STRIDE=48 gives 14 states headroom (room for
`load_master`/`q_clean` glue + R-cmp transitions, no future re-bump). Parameters:
`entry5(pc) = 6 + 48·pc`, `tm_mod5(len) = 54 + 48·len`, `288 = 48·6` quintuples per window
(6 symbols `0..5`). Slot index `pc·288 + off·6 + sym`.

**NEXT:** build `tm_assemble5.rs` (pure index arithmetic, mechanical bump — `lemma_idx5_decomp`,
`lemma_slot_index5`, `lemma_idx5_recover`, `lemma_tm_wf_n5`, peek demo) → lay ONE concrete power-block
window as validation (instantiate `lemma_power_block_step_block1` via `lemma_slot_index5`, mirror
`lemma_psc_rp_copy_park`) → 16-block sequencing (state-id splice) + master-mgmt → `psc_act` window
+ R-cmp/R-S/R-C/R-MC/B-W → discharge `ceer_realizes`.

### ✅ N+11 BUILT (crate 1178 → 1211/0, additive) — assemble5 scaffold + two window shapes

- **`tm_assemble5.rs` (17/0)** — the n=5 (marker `5`) STRIDE=48 scaffold. Mechanical bump of
  `tm_assemble4`: `entry5`, `tm_mod5`, `lemma_idx5_decomp`, `lemma_slot_index5`, `lemma_idx5_recover`,
  `lemma_tm_wf_n5`, peek demo. The pure index arithmetic, layout-independent.
- **`gap2_emit_window.rs` (7/0)** — the **singleton-emit window** `lemma_seret1_phase`
  (`lemma_surge_emit_return_block1`, 4 states→offsets 0..3): `od ↦ od ++ [s]`, master untouched. The
  singletons `[1]`/`[2]`/`[3]`/`[4]` (8× in `fam_digits`).
- **`gap2_emit_power.rs` (9/0)** — the **block1 power-block window** `lemma_pbb1_phase`
  (`lemma_power_block_step_block1`, 32 states→offsets 0..31, 64 quints): one `copy_refresh ∘ block_loop`,
  `od ↦ od ++ (s)^M`, master stationary. The `(1)ⁱ`/`(3)ⁱ` power-blocks. The fattest window — proves the
  recipe at full width.
- **THE RECIPE (reusable for every remaining window):** window-local action table `xxx_act(off, sym, …)`
  returning `(write, next_off, dir)` → manifest generator `xxx_gen` (q-key `entry5(pc)+off`, next
  `entry5(pc)+next_off`) → `lemma_tm_wf_n5` for wf → a generic per-slot locator `locate_…` (the heavy
  `lemma_slot_index5` + gen-unfold, done ONCE) → N cheap `locate_…` calls in the phase lemma → invoke the
  verified step. Concrete `xxx_tm` + `lemma_xxx_emit` validate end-to-end.
- **⚠ RLIMIT PITFALL (SOLVED) — make the generator `#[verifier::opaque]`.** The window hypothesis
  `forall i. tm.quints[i] == xxx_gen(s,i)` (trigger `tm.quints[i]`) was instantiated **1,137×**, each
  dragging the 32-branch `pbb1_act` if-chain into Z3 (**79% of cost**, rlimit blow). Marking `pbb1_gen`
  opaque + `reveal` only in `locate_pbb1`/`lemma_pbb1_tm_wf` kills the storm. **Every future block window
  generator MUST be opaque.**

### ⚠ N+11 DESIGN GATE FOUND — the 16-block state-id SPLICE over uniform windows (next-session crux)

Worked through the N+10 "splice = state identification" for the concrete uniform windows and found a real
encoding subtlety to settle before sequencing:

- Each block's phase lemma starts at `q_dh0 = entry5(pc)` (head on pivot) and ends at `q_exit = entry5(pc)+31`
  (head on pivot, `a:0`). To chain block `k → k+1` purely by state identification, block `k`'s `q_exit`
  must BE block `k+1`'s `q_dh0`. But with uniform stride-48 windows, `q_exit_k = entry5(pc_k)+31 = 37+48·pc_k`
  while `q_dh0_{k+1} = entry5(pc_k+1) = 54+48·pc_k` — a **17-state gap**; they are NOT equal. So "identify the
  states" does not fall out of the layout for free.
- **✅ RESOLUTION LOCKED (Danielle, port 8051): exit-target-parametric windows, cross-window exit edge.**
  Make `q_exit` a PARAMETER of each block's phase lemma — it is a pure label (no outgoing quint required by
  the step lemma), set by the block's exit quint `(q_guard, 0, 0, q_exit, R)`. The action table's exit
  transition targets the NEXT block's window entry: **middle block → `q_exit = entry5(pc+1)`** (a
  cross-window edge — sound, any `q2 < m`; in generator terms `next_off = 48`, i.e. `entry5(pc)+48 =
  entry5(pc+1)`, bounded for `pc < len`); **last block → `q_exit = q_{R-cmp}`** (hand-off to compare).
  Because the step's END config is `{a:0, q:q_exit, head on home pivot}` and block `k+1`'s lemma assumes
  `{a:0, q:q_dh0_{k+1}=entry5(pc+1), head on home pivot}`, setting `q_exit_k = entry5(pc+1) = q_dh0_{k+1}`
  makes `Config_term(k) ≡ Config_init(k+1)` IDENTICALLY — the sequencer chains `Lemma₁ ⟹ … ⟹ Lemma₁₆`
  with NO bridge proofs (Danielle: threading exit-as-entry via a glue step would add 16 unnecessary step
  obligations; the cross-window edge is the only zero-cost splice). **Window is a proof-engineering
  construct, not a physical state boundary** — a quint in window `k` may freely target a state in window
  `k+1`. Build: a `_mid`/`_last` action-table pair (or one table parametric in the exit-target state),
  thread `q_exit` through the phase lemma. **DESIGN LOCKED — execute next session.**

**NEXT:** settle the splice (exit-parametric windows) → remaining window variants (block3 triple
power-block + `block1_m1`/`block3_m1` + triple singletons — all mechanical via the recipe + opaque rule) →
16-block sequencing chaining `uinv_digits(b) ++ u_digits(a)` → master-mgmt (`load_master`, `q_clean`
wipe-and-load per the locked global layout) → `psc_act` window + R-cmp/R-S/R-C/R-MC/B-W → `ceer_realizes`.

## SESSION UPDATE 2026-06-27 (N+12) — ALL FOUR EXIT-PARAMETRIC WINDOW VARIANTS DONE (crate 1211 → 1233/0)

**✅ The N+11 splice gate is CLOSED and all window variants are built & verified.** Every block type in
`fam_digits` now has a verified exit-parametric phase lemma over the assemble5 scaffold. Full crate green
**1233/0**, all additive, no `assume`/`admit`/`external_body`.

**What got BUILT this session (4 commits):**
1. **`pbb1x` (gap2_emit_power.rs 16/0)** — exit-parametric single power-block. `pbb1x_gen` (opaque)
   special-cases the loop-exit slot `(off 24, sym 0)` to target an external `qexit`; `lemma_pbb1x_phase`
   (M≥2) ends in `q: qexit`. PLUS `lemma_pbb1x_m1_phase` (M=1) over the **SAME** window.
2. **`seret1x` (gap2_emit_window.rs)** — exit-parametric single singleton. `seret1x_gen` special-cases the
   q_eret landing `(off 2, sym 0)` to target `qexit`; the 4 walk-back self-loops live AT `qexit` (the next
   window's inert off-0 self-loops, which coincide byte-for-byte) and are supplied as `jl1..jl4`.
3. **`pbb3x` + `pbb3x_m1` (NEW gap2_emit_power3.rs 11/0)** — exit-parametric TRIPLE power-block (34 states,
   `pbb3_act` off 0–23 == `pbb1_act` copy_refresh, off 24–33 the triple-emit block_loop via q_e1=27/q_e2=28).
4. **`seret3x` (gap2_emit_window.rs 11/0)** — exit-parametric triple singleton (6 states, emit `[s0,s1,s2]`).

**✅ KEY ARCHITECTURE FINDING #1 — ONE WINDOW SERVES BOTH M=1 AND M≥2.** The N+10 plan listed
`block1_m1`/`block3_m1` as separate "window variants"; in fact **every M=1 quint
(`lemma_power_block_step_block*_m1`) maps to a `pbb*_act` slot with byte-identical content** — the m1 copy
lands directly on the pivot, reusing off 0–10/15–23 and skipping off 11–14's home-cycle; the shared
`(q_urt,1,1,q_urt,R)` self-loop (i_one_r) is off 23 sym 1. So the m1 dispatch is a **second phase lemma over
the same `pbb*x_gen` window** (`lemma_pbb*x_m1_phase` locates the 51-quint subset), NOT a separate window.
The sequencer dispatches the symbolic master `M`: `M == 1 → m1 lemma`, `else → general (M≥2) lemma`.

**✅ KEY ARCHITECTURE FINDING #2 — NO OFF-BY-ONE, NO M=0 CASE.** `u_digits(j)` / `uinv_digits(b)` use
exponent `i = j+1` (see `gap2_fam_digits.rs:82,96`); the stored counter (and hence the loaded master) is
`a+1` / `b+1` = `i` (N+10's "store a+1" choice). So a power-block emits `(blk)^M = (blk)^(a+1) = (blk)^i`,
**exactly matching `fam_digits`** — the `a+1` store is precisely what makes `M = i`. Since `i ≥ 1` always,
**the master is never 0**, so the per-power-block dispatch is only `M=1` vs `M≥2` — no M=0 emit-nothing case.

**✅ KEY ARCHITECTURE FINDING #3 — SINGLETON SPLICE = TWO-WINDOW (Danielle co-designed, port 8051).** The
power-block `q_exit` is a pure label → set `qexit = entry5(pc+1)`, clean. The singleton's end-state
`q_home` is a WALK-BACK state (loops `(q_home, 1..4, q_home, L)`, terminates ON the pivot without firing
`(q_home, 0)`). The walk-back self-loop is byte-identical to ANY next block's inert off-0 self-loop, so set
`q_home := qexit = entry5(pc+1)`: the 4 walk-back quints COINCIDE with the next window's off-0 self-loops
(supplied as `jl1..jl4`, located from window pc+1). **The FINAL singleton** (last block of the whole chain,
`u_digits(a)`'s `[2]`, targets `q_cmp`) needs `q_cmp` made WALK-BACK-COMPATIBLE — carry the same 4
`(q_cmp, 1..4, q_cmp, L)` self-loops. (Note for the sequencer/R-cmp build.)

**THE 16 BLOCKS (per `fam_digits = uinv_digits(b) ++ u_digits(a)`, low-first):**
```
  uinv_digits(b), i=b+1:  [4]seret1 · (4,1,2)ⁱpbb3 · [3]seret1 · (4,3,2)ⁱpbb3 · [2]seret1 · (1)ⁱpbb1 · [4,1,2]seret3 · (3)ⁱpbb1
  u_digits(a),    i=a+1:  (1)ⁱpbb1 · [4,3,2]seret3 · (3)ⁱpbb1 · [4]seret1 · (4,1,2)ⁱpbb3 · [1]seret1 · (4,3,2)ⁱpbb3 · [2]seret1
```
Counts: pbb1×4, pbb3×4, seret1×6, seret3×2. Two phases (master = b+1 then a+1) with WIPE-AND-LOAD between.

**NEXT (the sequencer — the hard crux, multi-session):**
1. **Within-phase 8-block chain** — chain 8 phase lemmas via `lemma_tm_run_split`, `Config_term(k) ≡
   Config_init(k+1)` by `qexit_k = entry5(pc_{k+1})`. Per-power-block `if M==1 {m1} else {general}` dispatch.
   Singleton→next splice needs the next window's off-0 self-loops located for `jl1..jl4`.
2. **Dispatch generator** — concrete `seq_gen(a,b,idx)` mapping each window pc to its block's gen + exponent
   symbols + `qexit = entry5(pc+1)`; satisfies the per-window hypotheses the chain consumes.
3. **Master-mgmt** — `load_master` (`copy_u(stored counter → master)`), `q_clean` wipe; WIPE-AND-LOAD splice.
4. **fam_digits assembly** — produced output `== fam_digits(a,b)` (compose `lemma_dds_fam_relator` /
   `lemma_relnum_is_fam_digits`); `dpack` value is `relnum(a,b)`.
5. **Concrete `psc_act` tm/tm_wf** + R-cmp/R-S/R-C/R-MC/B-W → discharge `ceer_realizes`.

### N+12 FINAL — BOTH per-phase 8-block chains DONE (crate 1211 → 1254/0)

**✅ Both `fam_digits` phases are fully chained & verified** (`gap2_emit_seq.rs`, abstract over a machine
carrying the 8 window gens per phase):
- **`lemma_uinv_phase`** — `tm_run(…, uinv_phase_fuel) == {…, v: dpack(od ++ uinv_digits(M-1)), q: qend}`.
  Decomposed into `lemma_uinv_half_a` (blocks 0–3) + `lemma_uinv_half_b` (blocks 4–7); last block is a
  power-block → `qend` external (no walk-back needed).
- **`lemma_u_phase`** — `tm_run(…, u_phase_fuel) == {…, v: dpack(od ++ u_digits(M-1)), q: qfinal}`.
  Decomposed into `lemma_u_seg_a` (0–2) + `lemma_u_seg_b` (3–4) + `lemma_u_half_b` (5–7); last block is the
  FINAL singleton → `qfinal` external, so `qfinal` must be walk-back-compatible (4 `kf` quint hypotheses —
  the `q_cmp` hand-off).
- **⚠ RLIMIT LESSON:** a 5-block chain segment exceeds rlimit; **keep chain segments ≤ 4 blocks** and split
  at power-block boundaries (so a singleton's walk-back never crosses a segment boundary). The uinv phase
  split 4+4; the u phase needed 3+2+3.
- Helpers: `lemma_pbb1x_phase_any`/`lemma_pbb3x_phase_any` (M-dispatch), `lemma_*_walkback`,
  `cat_bound`, `lemma_seq_pow_len`/`lemma_seq_pow_bound`. Single-element `seq_pow` length needs an explicit
  `assert(seq![x].len() == 1)` so `M·1` stays linear.

**NEXT (the remaining assembly — master-mgmt + concrete tm; distinct next phase):**
1. **Master-management gadgets (`load_master`, `q_clean`)** — NEW TM gadgets (need design). **KEY DESIGN
   RESOLUTION (N+12, with local-model port 8051):** master-mgmt is LOCAL to `u`, not cross-region. The
   per-phase chain works in the LOCAL frame (`u` = master+gap left of the home pivot, `v` = output right of
   it). Phase 1's last block is a power-block, so it ENDS with `u = copy_u(0, b+1, g)` exactly (master
   preserved, temp consumed); `v` holds `uinv_digits(b)`. Phase 2 needs `u = copy_u(0, a+1, g)` with `v`
   continuing. So between phases ONLY `u` changes — wipe the `b+1` repunit, rebuild the `a+1` repunit, both
   operating on the local `u` region (reuse `copy_refresh`'s short marked-copy walks, NOT a far-left
   cross-region copy). The SOURCE for `load_master` must be a LOCAL backup of `a+1` (e.g. a reserved slot
   adjacent to the master zone) — set up once at init (the partner's "pre-load both counters locally"
   insight, adapted: keep both `a+1`/`b+1` backups local so each phase's load is a short walk).
   **⚠ COUPLES WITH THE GLOBAL LAYOUT / R-P (Danielle's call):** where the local counter-backups live
   relative to `u` is a layout decision tied to R-P/the dovetail. The pre-load-both alternative (two masters
   side-by-side, no wipe) does NOT trivially work because the chain fixes the master's position relative to
   the temp — a second master in the gap changes `copy_u`'s value. So WIPE-AND-LOAD (with local backups) is
   the route; `q_clean` IS needed (if `a+1 < b+1`, overwriting leaves residue ones that the chain would
   miscount). Gadgets: `q_clean` (local: `read 1 → write 0 → L`, stop at the gap-`0`); `load_master`
   (local marked-copy backup→master, a `copy_refresh`-style deposit producing `copy_u(0, a+1, g)`).
   Build the init local-backup setup + both gadgets, then the two-phase wiring.
2. **Two-phase wiring** — chain `lemma_uinv_phase` (qend = master-mgmt entry) → master-mgmt → `lemma_u_phase`
   ⟹ output `= dpack(od ++ uinv_digits(b) ++ u_digits(a)) = dpack(od ++ fam_digits(a,b))`. The `qfinal` of
   the u phase = R-cmp's `q_cmp`.
3. **Concrete dispatch generator + `psc_act` tm/tm_wf** — `seq_gen(a,b,idx)` laying all windows (each pc →
   its block's gen, qexit = entry5(pc+1)); discharge the per-phase window hypotheses; `tm_wf` via
   `lemma_tm_wf_n5`.
4. **fam_digits ⟹ relnum** — `dpack(fam_digits(a,b))` is `relnum(a,b)` (`lemma_dds_fam_relator` /
   `lemma_relnum_is_fam_digits`). Then R-cmp/R-S/R-C/R-MC/B-W → discharge `ceer_realizes` → drop the axiom.

### N+12 addendum — CHAIN MECHANICS FULLY VALIDATED (crate 1233 → 1246/0); the 8-block assembly is mechanical

The sequencer's hard mechanics are now all verified end-to-end (`gap2_emit_seq.rs`, `gap2_relnum_dds.rs`):

- **Unified M-dispatch atoms** — `lemma_pbb1x_phase_any` / `lemma_pbb3x_phase_any` (+ `pb1_fuel`/`pb3_fuel`):
  one call dispatches `M=1` (m1 step) vs `M≥2` (general step) over the same window, unified fuel/output.
  Since the loaded master = `a+1 = i ≥ 1`, this is the ONLY power-block dispatch the chain needs.
- **Walk-back exposers** — `lemma_{pbb1x,pbb3x,seret1x,seret3x}_walkback(tm,len,pc,…,sym)` expose a window's
  off-0 self-loop `(entry5(pc),sym,sym,entry5(pc),L)`. A singleton ending at `entry5(pc+1)` gets its 4
  `jl` quints by calling the NEXT window's walkback for `sym=1..4`.
- **`seq_pow` bookkeeping** — `lemma_seq_pow_len` (`|seq_pow(s,k)|=k·|s|`) + `lemma_seq_pow_bound` (element
  range preserved) — the output-accumulation digit-bound/length helpers.
- **`lemma_chain_seret1_pbb1`** (2-block) + **`lemma_chain_s1_p3_s1`** (3-block) validate ALL splice cases:
  singleton→power (walk-back located from next window), power→singleton (trivial config-equality), FINAL
  singleton (`qexit=qfinal` external, walk-back-compatible via external `kf` hypotheses — the `q_cmp` case).

**THE 8-BLOCK CHAIN TEMPLATE (the exact next build, ≈150 lines, mechanical):** an abstract lemma over a
machine with 8 window hypotheses (windows `pc..pc+7`, each `forall i in window. tm.quints[i] ==
<block>_gen(…, entry5(pc+k+1), i)`; last block's exit = external `qend`). Body: for `k = 0..7`, let-bind
`c_k`/accumulated od; if block k is a singleton, locate the 4 walk-backs from window `pc+k+1` (its type's
`_walkback`); apply the block's phase lemma (`_phase_any` for power, `_phase` for singleton) to get
`tm_run(c_k, F_k) == c_{k+1}`; extend with `lemma_tm_run_split(tm, c0, acc_k, F_k)`. Maintain the
"od_k digits ∈ 1..4" invariant (use `lemma_seq_pow_bound` for the power emits). Encapsulate the 8-term fuel
sum in a `uinv_phase_fuel`/`u_phase_fuel` spec fn to keep the ensures readable. uinv blocks (M=b+1):
`[4]s1·(4,1,2)ⁱp3·[3]s1·(4,3,2)ⁱp3·[2]s1·(1)ⁱp1·[4,1,2]s3·(3)ⁱp1` (last = pbb1(3) → external qend, a power
exit so qend needs NO walk-back). Then prove the produced concatenation `=~= od ++ uinv_digits(b)` (and the u
phase `++ u_digits(a)`) by unfolding the spec fns (the emits already match term-for-term). Keep each block's
sub-proof isolated (let-bound) to stay under rlimit; extract per-block helpers if a monolith blows up.

### N+13 — `q_clean` COMPLETE (master-mgmt gadget #1), position-parametric over the high-tail backup (crate 1254 → 1277/0)

**Design gate resolved (2026-06-27, w/ Danielle port 8051):** the N+12 placement guidance ("backup BELOW the
master in `0..g`") is **inconsistent** — the phase invariant is `u == copy_u(0,M,g)` EXACTLY and the temp
counter GROWS into the gap `0..g` during emission, so a backup there is overwritten. **Resolution = option
(A): the backup `T` lives ABOVE the master**, a preserved high tail at a parametric offset (mark/deposit ops
are bounded by `g ≥ M+2` and never reach it). All master-mgmt gadgets are built **parametric over `T`**, so
the concrete offset (R-P/dovetail) plugs in only at the final `psc_act` — zero rip-out risk, the
exit-parametric-window pattern. This also means **the phase lemmas need additive high-tail variants
(`lemma_uinv_phase_tail`/`lemma_u_phase_tail`)** so the backup actually survives a phase (NEXT, item 1b).

**✅ `q_clean` (new module `gap2_master_mgmt.rs`, +23 verified, additive):** the master-erase half of
WIPE-AND-LOAD. `lemma_q_clean`: from a phase-boundary tape `u == m^g·(R(K) + m^(K+1)·T)` (gap `g`, old master
`K = old+1` ones, separator blank, backup `T` above) with output `v0` (low digit `1..4`) on the right and the
head on the pivot in `q_s`, it erases the master and returns home in `q_home`, leaving `u == m^(g+K+1)·T`
(master region `g..g+K` blank, `T` floated up one separator place, untouched) and `v0` restored — in
`2g+2K+4` steps over **9 quintuples / 3 states** `q_s`/`q_w`/`q_r`. Bricks:
- `lemma_wipe_ones_left` — the `(q,1,0,q,L)` erase sweep (mirror of `tm_copy_refresh::lemma_unmark_fives_left`).
- `lemma_pile_sym_zero` — `pile_sym(v,0,k) == v·m^k` (bridges seek/wipe `v`-formats).
- `lemma_q_clean_erase` — seek-left over the gap (`lemma_seek_left_blanks`) + seek→wipe transition + wipe;
  `K==1`/`K≥2` split; lands at the separator with the master gone, blanks piled on `v`.
- `lemma_q_clean_return` — wipe→return transition + seek-right (`lemma_seek_right_blanks`) + **4-way digit
  walk-back** (one quint per `1..4`, the `q_cmp` walk-back-compatible hand-off) onto the pivot blank. ⚠ the
  blank seek-right can't distinguish the pivot from the piled blanks, so it overshoots by one onto the output
  digit and the walk-back recovers it — that's why the 4 digit quints are needed (not a plain blank return).
- `lemma_q_clean` — composes erase+return; `q_clean_fuel(g,K) = 2g+2K+4`.

⚠ DETERMINISM NOTE for `psc_act`: the 9 quints occupy distinct `(state,symbol)` pairs — `q_w` carries BOTH
`(q_w,1,·)` (wipe) and `(q_w,0,·)` (→return), and the digit walk-backs MUST be in `q_r` (NOT `q_w`, which
already binds symbol `1`).

### N+13.1 — `load_master` DISSOLVED via a frame shift (2026-06-27, w/ Danielle port 8051) ✅

**`load_master` is NOT needed.** The frame-shift insight: `q_clean`'s output is `u == m^(g+K+1)·T`. With the
backup `T = R(a+1)` (the literal `a+1` repunit), this is **exactly** `copy_u(0, a+1, g')` for `g' = g+K+1` —
i.e. q_clean's output IS phase 2's input, with the master `a+1` sitting at its OWN gap `g'`. So instead of
copying/shifting the `a+1` block back down to position `g` (the old `load_master`), **phase 2 just runs with
`g := g' = g+K+1`** (the phase lemmas are fully parametric in `g`). No copy, no shift, no gadget.

- **Gap/blankness check (Danielle-validated):** after phase 1 + q_clean, the whole region `[0, g')` is blank
  (phase-1 gap `[0,g)` restored + the wiped `[g, g+K+1)`); phase 2's clear-path requirement at `g'` holds.
  Pick init `g ≥ a−b+1` so `g' = g+b+2 ≥ a+3` (phase 2 needs `g' ≥ M+2 = a+3`). Parametric, fine.
- **No phase-2 tail variant either** — `a+1` is the topmost block, nothing above it to preserve.

**The critical path is now `lemma_uinv_phase_tail`** (the ONLY genuinely-new proof obligation): phase 1
(`uinv_digits(b)`, master `b+1` at `g`) carrying the `a+1` backup as a preserved high tail at `g' = g+b+2`.
The proof must show every phase-1 op stays within `[0, g+K]` so the tail term `m^(g')·R(a+1)` passes through
untouched (the walk primitives already carry a `w` high tail; thread it up through the block phase lemmas).

**Init tape:** `Pivot · Blank_g · R(b+1) · Blank_1(sep) · R(a+1)` — i.e. `u == m^g·R(b+1) + m^(g+b+2)·R(a+1)`.

### N+14 — STRATEGY RESOLVED: the BLACK-BOX high-tail lift (option b done right). FOUNDATION VERIFIED (crate 1277 → 1315/0).

**Decision (2026-06-27, after a local-model consult + first-principles analysis):** route **(b) the meta-lemma**,
done as a true **black box** — option (a) re-threading the tail through `tm_copy_refresh`'s ~40 value-arith
lemmas is a confirmed trap. The decisive observation that makes (b) clean: a `TmConfig` is `(u, v, a, q)` with
the scanned symbol `a` and state `q` as **separate fields** — they are NOT computed from `u`. So adding a high
tail `add_hi(c) = {u: c.u + m^H·T, ..c}` changes only `u`, the **same quintuple fires every step**, and the tail
only perturbs the step *result*. An R-move sends `m^H·T → m^(H+1)·T` *unconditionally*; an L-move sends it to
`m^(H-1)·T` and leaves the popped symbol `a'=u%m` intact **iff `H ≥ 1`**. So the SOLE safety condition is
**`H ≥ 1` before every L-move** — a control-flow property, not a value-arith one. The earlier "reach isn't
expressible" worry was wrong: it doesn't need to be; the lift never inspects reach, it just threads `H ± 1` per
step and the discharge is the same induction the source gadget already does, tracking ONLY `dir` and `H`.

**VERIFIED FOUNDATION (3 new modules, all additive, no escape hatches):**
- **`gap2_tail_lift.rs`** — the reusable core. `add_hi`, `tail_safe` (the `H≥1`-before-each-L-move predicate),
  `tail_end_h` (`±1` per step); `lemma_run_tail` = the **black-box lift** `tm_run(add_hi(c)) == add_hi(tm_run(c))`
  given `tail_safe`; `lemma_tail_unfold` (one-step spec unfold at a known firing quint — the workhorse);
  `lemma_step_tail_safe` (single step); `lemma_tail_safe_split` + `lemma_tail_chain` (compose tail_safe across
  segment boundaries). **The lift touches ZERO value arithmetic of copy_refresh.**
- **`gap2_tail_walks.rs`** — `tail_safe` for all 5 walk primitives: `seek_left_blanks`/`run_walk_left`/
  `unmark_fives_left` (L-walks, need entry `h ≥ len+1`, offset drops by `len+1`), `seek_right_blanks`/
  `run_walk_right` (R-walks, unconditional, offset rises). Each mirrors the primitive's own induction.
- **`gap2_tail_phases.rs`** — `lemma_terminate_fwd_tail_safe`, the first multi-segment composition: mirrors
  `terminate_fwd`'s 6 segments and chains the companions with `lemma_tail_chain`. **Validates the TIGHTEST
  margin** — the master-detecting fives-walk enters at `h = M = len+1` and lands at exactly `h = 0` (blank above
  the all-fives master); the very next step (the turn) is an R-move, so `h=0` is reached only at an unconditional
  R-step. This is where the single separator blank between master and tail is load-bearing — **it verifies.** All
  conceptual risk is now retired; the rest is the same mechanical mirror-and-chain pattern.

**THE RECIPE for each remaining gadget companion** (`lemma_<gadget>_tail_safe`): copy the source gadget's body
(it already derives the boundary configs `c1…cN` and `tm_run(c0, fuel_k) == c_k`), and at each segment apply the
matching primitive/single-step companion at the tracked offset `h_k`, then `lemma_tail_chain(c0, fuel_k, segf,
h0, h_k, h_{k+1})`. Entry offset is `H_0 = g+M+1` at every pivot boundary (each gadget has **net displacement 0**,
so `tail_end_h == H_0` between gadgets — no cross-gadget offset bookkeeping). The offset only matters WITHIN a
gadget; the deepest excursion (terminate) is the tight one and is already done.

**Revised NEXT (the mechanical grind, then setup + wiring):**
1. **Finish copy_refresh `tail_safe`** by mirror-and-chain, bottom-up. **✅✅ COMPLETE (phase 1 + assembly).**
   - PHASES 2 & 3 (gap2_tail_phases.rs, 38/0): `lemma_terminate_fwd_tail_safe` + `lemma_mark_terminate_tail_safe`
     (phase 2) and `lemma_unmark_fwd_tail_safe` + `lemma_unmark_tail_safe` (phase 3) — tight `h=0` margin verifies.
   - PHASE 1 + ASSEMBLY (new module **gap2_tail_phase1.rs, 58/0**, crate green): the full bottom-up chain ALL
     VERIFIED FIRST-TRY (every companion, no escape hatches): `lemma_pile_ones_eq_pile_sym` bridge →
     `lemma_deposit_tail_safe` (reuses the s=1 general walk companions for the `walk_left_prefix`/`walk_back_prefix`
     ones-walks) → `lemma_mark_fwd_tail_safe` (ends `M-j`, NOT tight; j==1/j≥2 branch) → `lemma_mark_tail_safe`
     (fwd + all-R return, net-disp-0) → `lemma_copy_iter_tail_safe` → `lemma_copy_loop_general_tail_safe`
     (induction on hi) → `lemma_mark_j1_tail_safe` + `lemma_mark_j0_tail_safe` (deposit-first) →
     `lemma_copy_iter_j0_tail_safe` + `lemma_copy_iter_j1_tail_safe` → `lemma_copy_prefix_tail_safe` →
     `lemma_copy_loop_tail_safe` (g≥M+1 phase-path branch only; tight g==M skipped) → **`lemma_copy_refresh_tail_safe`**
     (the capstone: copy_loop ∘ mark_terminate ∘ unmark, all net-disp-0 at `H_0`, reusing phases 2&3 companions).
   - The mirror-and-chain recipe was 100% reliable: copy the source gadget's body, apply the per-segment
     primitive/step companion at the tracked offset, `lemma_tail_chain`. Every gadget net-disp-0, entry `H_0=g+M+1`.
   - **M=1 path** (`copy_refresh_m1` + sub-gadgets) — same recipe, shallower; NOT yet done. Whether it is on the
     uinv_phase critical path depends on whether `power_block` ever instantiates M=1 (it does via `pbb*_m1_phase`,
     used when `big_m == 1`; but uinv_phase requires `1 ≤ big_m` generic, so M=1 IS reachable — see item 2). (`g ≥ M+2`
     ⟹ the *nogap* `g==M` variants are NOT on the phase path, skip them.)
2. **Power-block + phase-block tail_safe** — `power_block_b1`/`b3` (+ `_m1`) wrap `copy_refresh`; then
   `pbb1x_phase`/`pbb3x_phase`/`pbb*_phase_any` and the `seret1x`/`seret3x` singletons (shallow reach, easy).
   Each enters at `H_0`, net-disp-0.
   **✅ LOWER HALF DONE (the emit loop): new module `gap2_tail_emit.rs`, 26/0.** ALL verified first-try
   (one trivial dpile-determinism fix): `lemma_dwalk_right_tail_safe` + `lemma_dwalk_left_prefix_tail_safe`
   (the output digit-walks, R-only/L-only) → `lemma_surge_tail_safe` + `lemma_return_walk_tail_safe`
   (+ the `drev` bridge) → `lemma_surge_emit_return_block1_tail_safe` (net-disp-0 for ANY `h` — the surge
   raises the offset before the return lowers it, so the return is never tight) → `lemma_dec_temp_tail_safe`
   (the decrement; REUSES the phase-1 s=1 walk companions + `lemma_pile_ones_eq_pile_sym`) →
   `lemma_block_iter_block1_tail_safe` → `lemma_guard_continue_tail_safe` + `lemma_guard_exit_tail_safe` →
   `lemma_block_loop_block1_tail_safe` (the loop induction on `temp`, `h ≥ temp+1`) → the **block3** mirrors
   (`surge_emit_return_block3`/`block_iter_block3`/`block_loop_block3`, triple-emit). The emit loop never
   goes within `g` of the tail (deepest reach is over the temp counter), so `h ≥ temp+1` is the only
   constraint and it holds trivially at `H_0 = g+M+1`.
   **REMAINING UPPER HALF (power_block + the per-window phases) — all pure COMPOSITION of proven pieces:**
   - `lemma_power_block_step_block1_tail_safe` = `lemma_copy_refresh_tail_safe` ∘
     `lemma_block_loop_block1_tail_safe`, both at `H_0`, net-disp-0. The block_loop runs at `temp = M`,
     `w = m^(g-M)·R(M)` (`w%m==0` since `g≥M+2`), home state `q_urt`, loop quint `i_one_r = i_urtemp`.
     Constraint `H_0 ≥ M+1` ✓. **SIGNATURE = copy the source `lemma_power_block_step_block1` requires
     VERBATIM (≈170 lines, lines 54–225 of tm_power_block.rs); only swap the `ensures` to tail_safe and the
     body to the 2-piece chain.** Same for `_block3` (uses `lemma_block_loop_block3_tail_safe`).
   - `power_block_*_m1` (M=1): needs the **M=1 copy_refresh path** (`lemma_copy_refresh_m1` +
     sub-gadgets, NOT yet done — item 1 leftover) tail-safe'd first (same recipe, shallower), then the same
     2-piece composition with `block_loop_*` at `temp=1`.
   - `pbb1x_phase`/`pbb3x_phase`/`pbb*_phase_any` + `seret1x`/`seret3x` phases (gap2_emit_window/power/power3):
     each wraps a `power_block` (or a singleton emit) + a `walkback` into the per-window "phase" that runs
     on `{copy_u(0,M,g), dpack(od), 0, entry5(pc)}` → `{copy_u(0,M,g), dpack(od++digits), 0, entry5(pc+1)}`.
     `u == copy_u(0,M,g)` UNCHANGED, net-disp-0 at `H_0`. The walkback is a short shallow R/L hop — mirror it.
   - The `seret` singletons (`seret1x`/`seret3x`) are NOT power-blocks — they emit ONE block via a single
     `surge_emit_return` (already have `_block1`/`_block3` companions) + a walkback. Shallowest of all.
3. **`lemma_uinv_phase_tail`** — apply `lemma_run_tail` to the whole 8-block phase run: discharge `tail_safe`
   over `uinv_phase_fuel` by `lemma_tail_chain`-ing the 8 block-companions (each net-disp-0 at `H_0`), then the
   lift gives `tm_run(add_hi(c0, H_0, R(a+1))) == add_hi(uinv_phase result, H_0, R(a+1))` — i.e. the phase-1
   output with the `a+1` backup preserved at `g' = g+b+2`. (`H_0 = g'`; the tail term is `m^(g')·R(a+1)`.)
4. **Init setup** — lay `u == m^g·R(b+1) + m^(g+b+2)·R(a+1)` at machine start (a `copy_refresh`/`block_loop`
   prelude that builds both repunits from the input `e`; couples to R-P).
5. **Wiring** — `lemma_uinv_phase_tail` (ends q_clean's `q_s`) → `lemma_q_clean` (ends `q_home` = phase-2
   `entry5(pc2)`) → **plain `lemma_u_phase` at `g := g+b+2`** ⟹
   `v == dpack(od ++ uinv_digits(b) ++ u_digits(a)) == dpack(od ++ fam_digits(a,b))`.
6. concrete `psc_act` tm/tm_wf + `fam_digits ⟹ relnum` → discharge `ceer_realizes` (unchanged from N+12).

### N+15 — THE HIGH-TAIL LIFT IS COMPLETE (items 1–3 above DONE; crate 1486/0, no escape hatches).

`lemma_uinv_phase_tail` (in `gap2_emit_seq.rs`) is verified: `tm_run(add_hi(c0, H_0, t)) == add_hi(uinv_phase
result, H_0, t)` — the 8-block phase-1 emission runs with the `a+1` backup preserved as an inert high tail at
`H_0 = g+M+1`, re-deposited at the same offset. The recipe ("copy source body, apply per-segment companion at the
tracked offset, `lemma_tail_chain`") held 100% — every new module verified first-try (one omitted `seq_pow_len`
length-lemma was the only fix). New modules / additions:
- **`gap2_tail_power.rs`** — `lemma_power_block_step_block{1,3}{,_m1}_tail_safe` = `copy_refresh_tail_safe` ∘
  `block_loop_block*_tail_safe`, 2-piece chain at `H_0`.
- **`gap2_tail_phase1_m1.rs`** — the M=1 `copy_refresh` path (`mark_terminate_m1`/`unmark_m1`/`copy_refresh_m1`
  tail_safe; fuel `6g+12`, `H_0 = g+2`). Both phase-2/3 share the 5-L-down-to-0, 5-R-back skeleton.
- **per-window phase companions appended to `gap2_emit_power.rs` / `gap2_emit_power3.rs` / `gap2_emit_window.rs`**
  (must live there for the module-private `locate_*`): `pbb1x/pbb3x{,_m1,_phase_any}` + `seret1x/seret3x`
  `_phase_tail_safe`. `seret` is parametric in `h` (offset only rises over the output, never below `H_0`).
- **`gap2_emit_seq.rs`** — `lemma_uinv_half_a/b_tail_safe` (chain 4 block companions each) →
  `lemma_uinv_phase_tail_safe` (chain the halves) → `lemma_uinv_phase_tail` (apply `lemma_run_tail`).

**NEXT = items 4–6 above** (init setup laying `u`, wiring `uinv_phase_tail → q_clean → u_phase`, concrete
`psc_act` + `fam_digits ⟹ relnum`) → discharge `ceer_realizes`, the last GAP-2 piece.

**Wiring (item 5) is config-match-de-risked (verified by inspection):** `lemma_uinv_phase_tail`'s output
`add_hi(result, H_0, t) = {u: m^g·R(b+1) + m^(g+b+2)·R(a+1), v: dpack(od++uinv_digits(b)), q: qend}` is
**EXACTLY** `lemma_q_clean`'s start form `{u: m^g·(R(big_k) + m^(big_k+1)·t), v: v0, q: q_s}` with
`big_k := big_m = b+1`, `t := R(a+1)`, `v0 := dpack(od++uinv_digits(b))`, `q_s := qend`. And `q_clean`'s
output `{u: t·m^(g+big_k+1), ...} = R(a+1)·m^(g+b+2) = copy_u(0, a+1, g+b+2)` is **EXACTLY** `lemma_u_phase`'s
start at `g' = g+b+2`, master `a+1`. So the wiring is a clean 3-lemma `lemma_tm_run_split` composition over
the 3 window-layouts (8 uinv blocks + q_clean's 9 quints + u_phase's blocks), set `qend := q_s` /
`q_home := entry5(pc_u)`. q_clean needs `1 ≤ v0 % m ≤ 4` (the output's low digit is a real digit). The only
genuinely-new construction is **item 4** (lay the initial double-repunit `u` from input `e`, couples to R-P).

### N+16 — ITEM 4 u-SIDE FLOAT-UP DONE + the v-SIDE α-block lift (the float-up/lift TOOLKIT is CLOSED). crate 1486 → 1512/0.

**Design locked (2026-06-27, w/ Danielle port 8051):** item 4 = take the dovetail's natural blank-separated
two-counter block `D = R(b+1) + m^(b+2)·R(a+1)` (`b+1` ones, sep blank, `a+1` ones) and **float it up by a gap
`g`** so `u == m^g·D == copy_u(0,b+1,g) + m^(g+b+2)·R(a+1)` (the EXACT `add_hi`-tailed phase-1 start config). The
phase constraints force `g ≥ max(b+3, a−b+1)` (phase 2's master `a+1` at gap `g'=g+b+2` needs `g' ≥ a+3`), so `g`
SCALES with `a` — a large variable gap, **counter-driven, not a fixed-sentinel shift**. Use `g = a+b+3` (a
counter concatenation; Danielle's call — avoids a tape `max`/subtract). The float-up is `block_loop`'s "consume the
counter, master's absolute position preserved" mechanic with the emit (surge) stripped — a pure **transporter**.

**✅ ITEM 4 u-SIDE FLOAT-UP — DONE (`gap2_init.rs`, additive).** The genuinely-new, **dovetail-agnostic** core:
- **`lemma_shift_right_ones`** — the `(q,1,0,q,R)` no-emit float-up, the **rightward mirror** of
  `gap2_master_mgmt::lemma_wipe_ones_left`. READS a one, WRITES a blank, moves R: each step `u' = m·u` (the
  written `0` becomes `u`'s new low digit) and pops a one off the gap-counter packed in `v`. Over a gap-counter of
  `len+1` ones (`1` scanned + `len` in `v`) bounded by a separator `rv` (`rv%m ≠ 1`), it floats `u` up by
  `m^(len+1)` and lands on `rv`'s low cell. Induction on `len`, structurally identical to `lemma_wipe_ones_left`.
- **`init_block(a,b,m) = R(b+1) + m^(b+2)·R(a+1)`** (the block `D`) + **`lemma_init_double_repunit_value`**:
  `m^g·D == copy_u(0,b+1,g) + m^(g+b+2)·R(a+1)` (pure place-value: `lemma_copy_u_start` + `lemma_pow_nat_add`).
- **`lemma_lay_init`** — the headline: from `{u: D, v: R(g−1), a: 1, q}` (the gap-counter of `g` ones at the head,
  `rv = 0` = empty local output) running the shift-up `g` steps gives EXACTLY
  `add_hi({u: copy_u(0,b+1,g), v: 0, a: 0, q}, g+b+2, R(a+1), m)` — the config `lemma_uinv_phase_tail` consumes
  (`q` splices to `entry5(pc)` at the concrete `psc_act`).

**SCOPE (Danielle-confirmed):** the remaining pre-shift pieces — (P1) lay `D` in `u`, (P2) lay the `g`-one
gap-counter in `v` — are pure **addressing** problems coupled to R-S's output format (where the dovetail parks
`a,b`). They are R-S **glue**, NOT item-4 logic; build them WITH R-S when the source layout is known. Item 4's
standalone u-side scope is satisfied by `lemma_lay_init`: when R-S delivers the pre-shift config, item 4 = a
`lemma_lay_init` composition.

**✅ v-SIDE α-BLOCK HIGH-TAIL LIFT — DONE (`gap2_tail_lift_v.rs`, additive).** The missing mirror: the global
layout parks α in an α-block to the RIGHT of the emitter output (`[…output] 0 [α-block] 0`), so at the emit pivot
`v == dpack(od) + m^H·A` — the α-block is a **high tail in `v`**. The emit phases are stated in the LOCAL frame
`v == dpack(od)`; to apply them on the concrete machine, lift over the α-tail. The **exact L↔R mirror** of the
`u`-side `add_hi` lift: `add_hi_v(c) = {v: c.v + m^H·A, ..c}` leaves `(q,a)` untouched ⟹ same quint fires; an
**L-move** pushes onto `v` (tail `H→H+1`, unconditional), an **R-move** pops `v` (tail `H→H-1`, needs `H ≥ 1`).
So `tail_safe_v` = "`H ≥ 1` before every R-move" (the head never reaching the α-block while shuttling over the
output). Verbatim mirror: `add_hi_v` / `tail_safe_v` / `tail_end_h_v` / `lemma_apply_add_hi_v_{l,r}` /
`lemma_run_tail_v` / `lemma_tail_unfold_v` / `lemma_step_tail_safe_v` / `lemma_tail_safe_v_split` /
`lemma_tail_v_chain` (reuses `gap2_tail_lift::lemma_match_is`). All verified first-try, no escape hatches.

**The float-up/lift TOOLKIT is now CLOSED** (u-side shift `lemma_lay_init` + u-side `add_hi` lift +
v-side `add_hi_v` lift). **NEXT = assemble the machine (R-S phase)** — the dovetail/search that produces `(a,b)`
and the pre-shift config (P1/P2), then R-cmp / R-S / R-C / R-MC / B-W → discharge `ceer_realizes`. Per Danielle:
do NOT enter R-S mid-toolkit (now done); R-S should be a composition of the verified tools. When R-S's emit step
needs the α-block carried through a phase, discharge `tail_safe_v` over the emit gadgets (a v-side mirror of the
`gap2_tail_emit`/`gap2_tail_power`/`gap2_tail_phase1` discharge work) — a sizeable but mechanical mirror, deferred
to R-S integration when the concrete α offset `H` is known.

### N+17 — the u-phase v-side α-tail lift COMPLETE (the v-tail toolkit is now symmetric). crate 1710 → 1715/0.

**✅ `lemma_u_phase_tail_v` BUILT (`gap2_emit_seq.rs`, +5 verified, additive, first-try).** The previous
session (the v-side discharge ending at commit `a6da193`) built the v-side `tail_safe_v` for the **uinv**
phase only (`lemma_uinv_phase_tail_v`). But the α-block is parked one separator-blank above the output and
**persists through BOTH `fam_digits` phases**, so the SECOND (`u_digits`) phase needs its own v-tail lift
before R-cmp (which reads output AND α-block) can be wired. Mirror of the uinv v-side stack onto the u
phase's 3-segment structure (`seg_a` blocks 0–2, `seg_b` 3–4, `half_b` 5–7):
- `lemma_u_seg_a_tail_safe_v` (binding surge = block-2 pbb1, `h ≥ |od| + 2M + 4`),
- `lemma_u_seg_b_tail_safe_v` (binding = block-4 pbb3, `h ≥ |od3| + 3M + 2`),
- `lemma_u_half_b_tail_safe_v` (binding = block-7 seret1, `h ≥ |od5| + 3M + 3`; hands off to external
  `qfinal`/R-cmp `q_cmp` via the 4 `kf` walk-back self-loops),
- `lemma_u_phase_tail_safe_v` (chains the 3 segments at one `h`, tightest bound `h ≥ |od| + 8M + 7` — the
  SAME margin as the uinv phase, set by the last power-block surge),
- `lemma_u_phase_tail_v` (the lift: `lemma_u_phase` ∘ `lemma_u_phase_tail_safe_v` ∘ `lemma_run_tail_v`).

**✅ DESIGN CONFIRMED — the u phase needs NO u-side (`add_hi`) tail.** Per N+13.1, after `q_clean` the
`a+1` backup floats down to become phase-2's master at gap `g' = g+b+2` and is the TOPMOST block — nothing
above it in `u` to preserve. So the u phase's only carried tail is the v-side α-block.

**✅ THE COMBINED u+v CARRY (uinv phase) — GENERIC LIFT BUILT (`gap2_tail_lift_v.rs`, +2, first-try).** On
the concrete machine the uinv phase runs from `add_hi(add_hi_v(c_local, H_v, A), H_u, T_backup)` — BOTH tails
present at once. `add_hi` (u) and `add_hi_v` (v) touch DISJOINT `TmConfig` fields, and neither perturbs the
head trajectory, so the carry composes. Built the generic substrate:
- `lemma_tail_safe_under_add_hi_v` (the bridge — the one non-trivial fact): the u-side `tail_safe(c, fuel,
  H_u)` is invariant under `add_hi_v(c, H_v, A)` *given* `tail_safe_v(c, fuel, H_v)`. Induction on `fuel`,
  per-step `v`-commute from `lemma_apply_add_hi_v_{l,r}`; the same quints fire because `add_hi_v` leaves
  `(q,a)` and (under `tail_safe_v`) the whole trajectory untouched.
- `lemma_run_tail_uv`: `tm_run(add_hi(add_hi_v(c, H_v, A), H_u, t)) == add_hi(add_hi_v(tm_run(c), …), …)` —
  a 3-line composition of `lemma_run_tail` (u-tail over the v-tailed config, via the bridge) ∘
  `lemma_run_tail_v` (v-tail over the local config). The reusable carry for any run, parametric in
  `(H_u, H_v, T_backup, A)`; the uinv-phase capstone instantiates it at wiring time with the concrete
  offsets. For the u phase this is moot (no u-tail — `lemma_u_phase_tail_v` alone suffices).

**NEXT (the R-S proper arc, unchanged order):** pre-shift glue — (P1) lay `init_block(a,b)` in `u` from the
parked dovetail counters, (P2) lay the `g`-one gap-counter in `v` (`g = a+b+3`), and an α-tail-parametric
`lemma_lay_init` (parameterize over `rv` = the empty-output+α-block high tail above the gap-counter, instead
of the hardcoded `rv=0`) — then **R-cmp** (digit-by-digit compare of the emitted output against the α-block,
the "sink" whose interface is now pinned: output low in `v`, α-block as a v-tail at offset `H`, head at
`qfinal`), R-S (dovetail over `(a,b)=declared_pair(e,s)`), R-C (cleanup to origin), R-MC, B-W → discharge
`ceer_realizes`. The peer-recommended order is R-cmp first (it constrains the emit/α orientations upstream);
`q_clean` will also need a v-tail companion (`lemma_q_clean_*_tail_safe_v`) since the α-block rides above the
output across the inter-phase wipe too.

#### R-S proper arc — entry plan for the next session (the tail/lift toolkit is now CLOSED; this is the new frontier)

The whole tail-carry substrate is done (`lemma_uinv_phase_tail` u-side, `lemma_uinv_phase_tail_v` +
`lemma_u_phase_tail_v` v-side, `lemma_run_tail_uv` combined). What remains is genuinely-new TM gadget
logic + the dovetail control flow — design-heavy, and per the AGENDA pattern these pieces are **co-design
points with Danielle** (port 8051). Surfaced design considerations to settle BEFORE coding:

1. **⚠ R-cmp MUST be NON-DESTRUCTIVE on α (the load-bearing design question).** α is the machine INPUT,
   fixed across the whole dovetail — every stage `s` compares its own emitted output against the SAME α
   block. So R-cmp cannot consume α (a naive peel-both-and-erase compare destroys it). Options to weigh:
   (a) mark/compare/restore α in place (more states, but no copy); (b) the per-stage output is disposable —
   compare by consuming the OUTPUT against a non-destructively-read α (read α's digit via peek, don't erase);
   (c) copy α to scratch each stage (simple but Θ(|α|) copy per stage — and the dovetail runs ~stages² so
   this is fine asymptotically). Likely (b): walk the output low→high, for each output digit peek the
   matching α digit (ping-pong via `dwalk_left`/`dwalk_right`), reject on mismatch; accept iff both exhaust
   together. The output IS consumed (good — it must be cleared before the next stage anyway).
2. **⚠ Orientation/reversal must be checked against R-P.** The emitter writes `fam_digits` low-first into
   `v` (`dpack`); R-P parked α **reversed** in its block (N+2 note: "α parked reversed in v, high digit
   lowest"). Confirm the two land in the SAME order at the compare, or insert one `dwalk` reversal. The
   compare only needs psc_tm to emit in `decode_word`'s canonical order to match α — pin this first.
3. **R-S dovetail = mirror `search_rm`'s STRUCTURE** (already proven: `lemma_search_rm_halts_iff`), re-expressed
   as n=5 TM gadgets: enumerate `s`, decode `(a,b)=declared_pair(e,s)` into the parked counters, run
   pre-shift→emit→R-cmp, on mismatch clear the output + advance `s` + loop; on match fall through to R-C.
   The dovetail counters `s, a+1, b+1` live in the persistent left region (a high u-tail during emit, carried
   by `lemma_run_tail_uv`'s `T_backup` slot — OR re-derived from `s` each stage; pick when wiring).
4. **Pre-shift glue (P1/P2 + α-tail `lay_init`)** is coupled to the dovetail's parked-counter layout (item 3),
   so build it WITH R-S. The α-tail `lay_init` now has its substrate: `lemma_shift_right_ones` + a new
   `lemma_shift_right_ones_tail_safe_v` (mirror `lemma_run_walk_right_tail_safe_v`) lifted by `lemma_run_tail_v`.
5. **R-C / R-MC / B-W** are the closeout: cleanup-to-origin (mirror `tm_cleanup`), the machine-content splice
   (`lemma_ignition_yields` ∘ `lemma_frame_reaches` ∘ `lemma_tm_h0_iff` ∘ R-S halts-iff ⟹ `mm_decides_relnum`),
   then `lemma_ceer_realizes_from_machine` (DONE) discharges `ceer_realizes` and drops `axiom_ceer_fp_embedding`.

**Recommended first concrete brick next session:** settle items 1–2 with Danielle (the R-cmp algorithm +
orientation), then build the R-cmp comparison phase lemma as a self-contained gadget over the assemble5
scaffold (its interface is pinned: head at `qfinal`/`q_cmp`, output low in `v`, α as a v-tail at offset `H`).

**Peer-proposed R-cmp design (port 8051 consult, N+17) — for Danielle's call:** COPY-TO-SCRATCH + destructive
DUAL-PEEL. The spent `a+1` master in `u` is free scratch, so: **(Copy phase)** copy α (from v's high tail,
past the output) into `u`, non-destructively (mark/restore α in place during the walk-back, so the ORIGINAL
α survives in v for stage `s+1`); **(Compare phase)** now α-copy sits low in `u`, output low in `v`, head at
the pivot — a classic two-stack dual-peel: read `u`'s low + `v`'s low, **accept iff both blank together**,
reject on `(digit ≠ digit)` OR `(one blank, other not)` (length mismatch falls out for free), else erase both
and step. **(Cleanup)** output already consumed; clear any residue → R-S coordinator. Trade-off vs ping-pong:
the copy is Θ(|α|) per stage (dovetail is ~stages², asymptotically fine) but turns the compare into the
simplest, least-error-prone TM pattern (no positional markers needed in α). ⚠ The copy step still ping-pongs
the head past the output to reach α — reuses the `dwalk`/copy machinery. **OPEN: confirm this vs a direct
non-destructive ping-pong compare (no copy) — Danielle's design call before the build.**

### N+18 — R-cmp design fork SHARPENED (deep grounding pass, no code). The crux is the *compare action*, not copy-vs-ping-pong. DANIELLE DECISION NEEDED.

**This session was a read-only grounding + co-design pass on the N+17 fork.** Verified the post-emit
interface, traced the (u,v,a,q) mechanics down to the quintuple level, and ran two port-8051 consults.
Baseline re-confirmed green (`tm_dwalk` 6/0 sample). No code written — the fork is genuinely undesigned at
a level the project reserves for Danielle, and it is now *much* better characterized. **The headline: the
N+17 framing (copy-to-scratch vs ping-pong) is the wrong axis. The real crux is whether the per-digit
compare can be MARKERLESS at all in the Minsky model — and that is open, with the existing toolkit's own
docstrings on one side and a clean infeasibility argument on the other.**

**The precise R-cmp entry interface (now pinned, from `lemma_u_phase` / `lemma_u_phase_tail_v`):**
`u = copy_u(0,big_m,g,m)` (the spent emit-scratch `a+1` master — disposable, will be reloaded by
`load_master`), `v = dpack(fam_digits) + m^H·dpack(alpha_stored)` (output low = `relnum(a,b)` value, blank
gap, then alpha as a v-tail at the still-unpinned offset `H` — `H` is R-S glue, deferred), `a=0`, `q=q_cmp`
(carries the 4 `kf` walk-back self-loops). R-cmp must accept (-> R-C) iff `dpack(fam_digits) == (alpha value)`,
else clear output + advance `s` + loop.

**Finding 1 — orientation makes "output == alpha" a same-index low-to-low pairing IF the head sits at the gap.**
`tm_rp` parks alpha REVERSED (`alpha_stored = drev(alpha)`); the emitter writes output forward. Move the head
to the gap and `u = ...*m^L + dpack(drev(output))` (output relocated, `u`-low `= output[L-1]`),
`v = dpack(alpha_stored)` (`v`-low `= alpha_stored[0] = alpha[L-1]`). So `u`-low vs `v`-low compares
`output[L-1]` vs `alpha[L-1]` — the CORRECT same-index pairing, peeling inward. (With alpha stored *forward*
the same trick checks `output == drev(alpha)`, wrong; so the reversed parking is load-bearing and should be
kept.) No reversal insertion needed — item 2 RESOLVED in favour of "head-at-gap, low-to-low".

**Finding 2 — the between-stacks wall (the real crux).** With the head at the gap, `u` = output, `v` = alpha:
this is exactly N+17's "dual-peel". But in the Minsky model **every move is a swap** — L pops `u`/pushes `v`,
R pops `v`/pushes `u`; there is no "delete". To compare `u`-top vs `v`-top you can get BOTH into the state
(R to read `v`-top, L to read `u`-top, the two reads cancel), but to ADVANCE while keeping alpha intact you
must remove the consumed output digit — and pushing it to `v` blocks the next alpha digit, while pushing it
back to `u` undoes the read. **A markerless dual-consume that preserves `v` loops.** (Port-8051 consult worked
this through independently and hit the same wall: *"M2's clean cycle is an illusion — Minsky machines don't
consume, they relocate."*) ⟹ the compare needs EITHER a frontier MARKER (symbol `5`) in alpha, restored after,
OR a sacrificial COPY whose destructive consume you don't care about.

**Finding 3 — `copy_refresh` is UNARY, so M3's "just reuse the big copy gadget" is overstated.**
`copy_refresh` (the 356 KB verified file) copies a *unary counter* (master->temp). alpha is a digit-string
(`1..4`). M3 would need a *new digit-string copy* (the `dwalk`-level analog), and the destructive compare of
the copy STILL faces the between-stacks wall unless the copy is laid adjacent (-> a single-region fold, which
needs a marker -> circular). So M1 (marker) and M3 (copy) both need substantial *new* digit-string machinery;
the asymmetry the peer cited is smaller than it looked.

**Finding 4 — a possible MARKERLESS route the consults missed, and the docstring tension.** The verified
`dwalk` docstrings explicitly say "the R-cmp **ping-pong**" (markerless) and `tm_rp` calls the reversed park
"the canonical layout the R-cmp **ping-pong** reads" — i.e. the toolkit was *built assuming a markerless
compare*. That contradicts Finding 2. The reconciliation candidate: a consumed digit CAN be deleted by writing
`a2=0` when it is the scanned symbol (a move R with `a2=0` overwrites the scanned digit and shifts a `0` onto
`u`). The disposable emit-scratch master in `u`-low is a legitimate "delete-bin" for those `0`s. **This may be
the markerless scheme the docstrings intend** — but it has delicate coupling: the `0`s interleave with the
master content, so `load_master`'s expected `u` layout on the reject path must survive (or the reject path
must fully wipe `u` first). NOT traced to completion this session.

**State of the three sub-questions:**
- (item 1, non-destructive compare) — REFRAMED: it is a *marker vs markerless* question, not copy vs ping-pong.
  Markerless feasibility is OPEN (Finding 4 vs Finding 2).
- (item 2, orientation/reversal) — RESOLVED: keep alpha reversed, head-at-gap, low-to-low (Finding 1).
- (offset `H`) — still R-S glue, deferred (unchanged).

**RECOMMENDATION (for Danielle's call):** my lean is **M1 — a digit-level mark-and-restore compare** (marker
`5` tracks the alpha frontier; per step peel one output digit, walk to the marker via a `dwalk`-to-marker,
compare, advance+restore). Rationale: it is the `dwalk`-native approach, the non-destructive-on-alpha guarantee
is the same pattern `copy_refresh` already proves (read a counter without destroying it), and the loop
invariant is the cleanest ("marker at frontier `k`; alpha equals its initial value with one cell overwritten
by `5`; output suffix consumed"). M3 (copy) needs a new digit-string copy AND still hits the between-stacks
wall on the compare; M2 (markerless dual-consume) is refuted by Finding 2. **BUT** before building I want
Danielle's call on Finding 4: the `dwalk` docstrings she co-designed assume markerless ping-pong — if she
intended the `a2=0`-delete-into-scratch scheme, that is a cleaner (no-marker) compare worth doing instead of
M1, and I do not want to build M1 against a markerless intent. The `H`-offset glue and the compare-action are
the only things between here and `mm_decides_relnum` -> `ceer_realizes` -> dropping `axiom_ceer_fp_embedding`.

**NEXT (once Danielle picks marker / markerless):** build the chosen compare as a self-contained gadget over
the `assemble5` scaffold (interface pinned above), then R-S (dovetail), R-C/R-MC/B-W -> discharge
`ceer_realizes`.

### N+19 — R-cmp fork RESOLVED = M1 (marker-5, α immutable). Two §N+18 errors corrected from the model. First brick built (skip-blank loops).

**Decision (port-8051 consult, this session): build M1.** The fork is closed in favour of the
marker-based compare. Two corrections to the §N+18 analysis, both re-derived directly from `tm.rs`, were
folded into the call:

- **§N+18 Finding 2 is WRONG.** It claimed "the Minsky model has no delete; every move is a swap, so a
  markerless dual-consume loops." But `apply_quint` (`tm.rs:90`) writes `qt.a2` on *every* move
  (R: `u'=u·m+a2`; L: `v'=v·m+a2`). Writing `a2=0` deletes a cell to blank. The existing
  `lemma_dwalk_left`/`right` already peel nonzero-digit blocks and **stop at `0`** — `0` is the toolkit's
  universal delimiter. So a markerless-via-`0` compare is *feasible* (it reuses the `0`-delimited walks),
  not blocked. This was the load-bearing correction.
- **§N+18 / older "no free sentinel at n=4" is OUTDATED.** The committed machine is **n=5**
  (`tm_assemble5`: `0`=blank, `1..4`=digits, `5`=the `copy_refresh` mark). Symbol `5` is FREE during
  R-cmp (post-emit, all `copy_refresh` marks restored), so a marker-based compare can use `5` as the
  α-frontier mark/sentinel, and `dwalk-to-5` is just the `dwalk` template with the stop-constant `0→5`.

**Why M1 wins anyway (the consult's call, which I agree with after the corrections):** the deciding cost
is **α-survival**. α is the loop invariant of the generate-and-compare dovetail — it must be intact for
every stage `s`. Markerless-via-`0` *destroys* α as it compares, forcing a copy-then-compare wrapper
(copy α into the spent-master scratch in `u`, Θ(|α|) head-travel per stage). M1 keeps α in place: mark
the frontier with `5`, read it, restore it. Since `5` is free and `dwalk-to-5` is a trivial template
instantiation, M1's "new primitive" cost is small while its lifecycle cost (α never copied) is much
lower. **Verdict: M1, α treated as a read-only resource during R-cmp.**

**Exhaustion / length-mismatch detection (the part §N+18 underweighted): SENTINEL-5 at each string's far
end.** You cannot test `v==0` (an empty right half-tape is an infinite sea of blanks; moving R just loops
scanning `0`). So at park/relocate time, write a single `5` *below* (far end of) BOTH the parked α block
and the relocated output block. Then exhaustion becomes a *search for a marker*, not a search for nothing:
hit `5` scanning the output side ⟹ output exhausted; hit `5` on the α side ⟹ α exhausted; both reached
together with all digits matched ⟹ **ACCEPT**; one exhausts before the other ⟹ lengths differ ⟹ REJECT
(clear output, advance `s`, loop). This is the standard marker-boundary trick used in formal TM
constructions (Aanderaa–Cohen) to dodge the blank-tape trap.

**Precise M1 micro-algorithm (worked out at the quintuple level this session, for the build to follow):**
post-relocation layout, head at the gap: `u = dpack(drev(output)) ++ [5] ++ scratch` (output reversed,
its low digit = `output[L-1]` nearest the head, then a far-end sentinel `5`, then disposable scratch);
`v = dpack(drev(alpha)) ++ [5]` (α reversed, low digit `alpha[L'-1]` nearest, far-end sentinel `5`);
`a=0`, `q=q_cmp`. Per round (peeling the frontier pair inward):
  1. **Onto the α-frontier:** from the gap, move R onto α's low digit `d_a` (∈1..4 or the sentinel `5`).
     Record `d_a` in state (4 states), **write `5`** (mark this cell), move L back toward output.
  2. **Cross the gap left:** skip-blank-left loop `(q,0,0,q,L)` over the gap `0`s (the original gap plus
     the cells of already-consumed output, now `0`) until the first nonblank = `output` frontier `d_o`
     (∈1..4) or the output sentinel `5`.
  3. **Compare:** `d_o` vs the recorded `d_a`. `5` on either side here = exhaustion (see above). If
     `d_o == d_a`, **write `0`** (consume the output digit — output is disposable), move R.
  4. **Cross the gap right + restore:** skip-blank-right loop `(q,0,0,q,R)` until the first nonblank =
     the `5`-mark from step 1. **Write `d_a` back** (restore α — α is now value-preserved, relocated one
     cell toward `u`), move R to the next α frontier. Loop to step 1.
  5. **Accept/reject:** when step 1 reads sentinel `5` AND the matching output frontier is sentinel `5`
     ⟹ equal lengths, all matched ⟹ drive to `tm_origin` (ACCEPT). Any digit mismatch or single-sided
     `5` ⟹ clear remaining output to `0`, rewind α from `u` back into `v` (a single `dwalk`), `INC s`,
     re-enter `q_cmp` (REJECT/loop). Note α ends a successful run relocated into `u` (value-preserved);
     the reject path's α-rewind is a clean extra brick.

**Brick breakdown (the build queue):**
  - **B-cmp.0 `skip-blank` loops** — `lemma_skip0_left` / `lemma_skip0_right`: peel `k` blanks off the
    near stack onto the far stack, land on the first nonblank. *(BUILT this session — `tm_skip_blank.rs`,
    the blank analog of `tm_walk::lemma_walk_left_inner`; gap-crossing for steps 2 & 4.)*
  - **B-cmp.1 mark/restore** — read-record-mark-`5` (step 1) and find-`5`-restore (step 4) single-cell ops.
  - **B-cmp.2 round step** — one frontier-pair comparison (steps 1–4) as a fuel lemma.
  - **B-cmp.3 compare loop** — iterate B-cmp.2, decreasing on remaining α length; threads the gap-size.
  - **B-cmp.4 accept/reject dispatch** — sentinel handling, drive-to-origin, clear+rewind+INC.
  - **B-cmp.5 park-time sentinels** — add the two far-end `5`s (touches `tm_rp` park + the relocation;
    deferred — done last to avoid perturbing verified emit lemmas).

**NEXT:** B-cmp.1 (mark/restore single-cell ops), then B-cmp.2 round step. Then R-S (dovetail) →
R-C/R-MC/B-W → discharge `ceer_realizes` → drop `axiom_ceer_fp_embedding`.

### N+20 — R-cmp round design CORRECTED + CONFIRMED (the side-separation/pollution pitfall). Caught a soundness flaw at config-trace time, before writing the round.

**The pitfall (found by config-level tracing of a candidate round, NOT in code — no lines wasted).** The
"obvious" M1 round — *mark α-frontier `5`, walk left to output frontier, compare, consume output→`0`, walk
right to the `5`, restore α-digit, move R to the next α-frontier* — is **UNSOUND**. Tracing the configs:
the final "restore + move R" pushes the restored α digit onto `u` (the output side). After one round
`u = [restored-α-digit][gap 0s][consumed-output 0][output rest]`, so the **next** round's leftward
output-scan (`skip0_left`, which stops at the first nonblank) immediately hits the migrated α digit — a
`1..4` — and mistakes it for the output frontier. **Because output and α share the `1..4` alphabet, ANY
scheme that lets compared-α digits migrate into `u` is unsound**: the walk/skip primitives cannot tell an
α digit from an output digit. (n=5 affords only ONE spare mark, `5`; there is no second symbol to tag
migrated α.)

**The fix — STRICT SIDE-SEPARATION (confirmed by port-8051 consult against the reading; this is the
Minsky / Aanderaa–Cohen "two-stack tape simulation" probe pattern — `To read a cell at distance k from
the boundary without shifting the boundary, do k pushes then k pops`):**
- **α lives entirely in `v`, output entirely in `u`.** The head only OSCILLATES through the boundary.
- **Every excursion into `v` is BALANCED (there-and-back):** `dwalk_right` peels the already-compared
  α digits onto `u`, then `dwalk_left` peels them back onto `v` — net change to `v` is ZERO (the
  "there-and-back is identity" fact, already available via the `drev`-involution lemmas in
  `tm_dwalk_prefix.rs`). **No digit ever permanently crosses the boundary** ⟹ no pollution.
- **The α frontier is a single `5`-mark living IN `v` at the current position `k`; the marked digit's
  VALUE is carried in the finite control** (so α is value-preserved — exactly one cell shows `5`, its
  value in state, restored on exit). Reading α[k] reads the STATE, never the cell. Moving the value via
  the tape would need a *third* mark symbol, which n=5 does not afford — value-in-state is forced and is
  the standard mechanism. `dwalk_right` naturally stops at the `5` (5 ∉ 1..4), so "dwalk-to-5" is free.
- **The first comparison (k = α-low, nearest the boundary) needs NO traverse;** the traverse grows as the
  marker moves deeper into `v`, giving O(|α|) per round, O(|α|²) total — fine (dovetail is already ~stages²).

**Confirmed ACCEPT path:** output frontier consumed AND marker has traversed all of α ⟹ restore the last
`V_last` into the marked cell (replace `5`), drive head left to the blank boundary, → `q_accept` → drive
to `tm_origin`. Tape clean: `u` empty, `v` = original α.
**Confirmed REJECT path** (`d_o ≠ V_k`, head at the `5`): write `V_k` back, balanced-traverse left to the
boundary (α intact, `5` gone), wipe `u` to `0`s (the clear-output the `skip0`/write-0 primitives give),
`INC s`, drive to origin, re-enter the dovetail. α survives every reject ⟹ ready for stage `s+1`.

**Revised brick breakdown (supersedes the B-cmp.1/.2 split in §N+19):**
  - **B-cmp.0 `skip-blank` loops** — DONE (`tm_skip_blank.rs`, crate 1725/0). Gap-crossing in `u`
    (skip consumed-output `0`s) and the symmetric `v` skip.
  - **B-cmp.1 balanced α-traverse** — FOUNDATION DONE (`tm_cmp_traverse.rs`, crate 1731/0):
    `lemma_dwalk_right_gen`/`left_gen` generalize `dwalk` to a `1..4` block followed by an arbitrary tail
    `W`, landing scanning `W % m` (`W=0` = old `dwalk`; `W%m==5` = stop at the frontier mark). REMAINING:
    compose right-gen→turnaround-at-`5`→left-gen into the config-level net-identity-on-`v` round-trip (the
    turnaround couples with B-cmp.2's marker work).
  - **B-cmp.2 marker advance** — at the `5`: restore `V_k`, step to `k-1`, load `V_{k-1}`, write `5`.
  - **B-cmp.3 output read+consume** — non-destructive read of the `u` frontier, write `0`, record `d_o`.
  - **B-cmp.4 round step** — compose B-cmp.1–.3 + the digit compare; fuel lemma, decreasing on |α|−k.
  - **B-cmp.5 compare loop** — iterate B-cmp.4 over all positions; threads the gap size.
  - **B-cmp.6 accept/reject dispatch** — the two paths above (drive-to-origin / clear+rewind+INC).
  - **B-cmp.7 park-time sentinels + relocation** — far-end `5` below α (and the output-side end marker);
    the Finding-1 relocation; touches `tm_rp`/emit — done LAST to avoid perturbing verified lemmas.

**NEXT:** the B-cmp.1 round-trip turnaround (compose right-gen→at-`5`→left-gen, net-identity on `v`),
which folds in B-cmp.2's marker work (restore `V_k`, step to `k-1`, load `V_{k-1}`, write `5`); then
B-cmp.3 output read+consume, then the B-cmp.4 round step. The design is fully pinned and confirmed against
the reading — no further design gate before the build. (B-cmp.0 skip-blank + B-cmp.1 foundation DONE,
crate 1731/0.)

### N+21 — R-cmp B-cmp.1 round-trip COMPLETE (the balanced probe). Marker-direction inconsistency flagged for B-cmp.2.

**Built this session (2026-06-27):** `lemma_cmp_balanced_roundtrip` in `src/tm_cmp_traverse.rs` — the
B-cmp.1 composition that §N+20 left as REMAINING. It glues the three sub-walks into one config-level move:
  1. `lemma_dwalk_right_gen` over the already-compared prefix `blk` (peels it onto `u`, lands scanning the
     `5`-mark — the tail is `w == m·whi + 5`, so `w % m == 5`);
  2. a **single L-move turnaround** on the marker quintuple `(q_back, 5, 5, q_walk, L)` — it re-writes the
     `5` (so `v`'s marker cell is value-preserved: the L-move's `a2 = 5` push reconstitutes `v = (w/m)·m + 5
     = w`) and flips to the leftward state, the L-move's free `u`-pop handing the head `drev(blk)[0] =
     blk[k-1]`, exactly the low digit the left walk needs;
  3. `lemma_dwalk_left_gen` over `drev(blk)` with tail `c.u` (peels the prefix back onto `v`).

**Net config effect (the ensures):** `tm_run(tm, c, 2·|blk|+1) == { u: c.u/m, v: dpack(blk) + m^{|blk|}·w,
a: c.u % m, q: q_walk }`. I.e. `v` is restored to the **full α stack** (the scanned α digit `blk[0]` folded
back in, the `5`-mark intact), `u` content untouched, and the head has stepped **one cell left into `u`**,
now scanning the output frontier `c.u % m` — precisely the position B-cmp.3 reads. The balanced there-and-
back is net-identity on the α content; the proof rides the `drev`-involution / `dpile_is_dpack_drev` bridges
in `tm_dwalk_prefix.rs`. Requires `n ≥ 5` (the `5`-mark must be a real symbol). Crate **1735/0**, committed
(50e92c8). No verifier escape hatches.

**⚠ Marker-direction inconsistency to resolve in B-cmp.2.** §N+20's prose says comparison starts at `k = 0`
(α low digit, no traverse) and the marker moves **deeper** (`k` increasing, traverse grows) — O(|α|²) total.
But the §N+20/§N+19 B-cmp.2 brick line says "restore `V_k`, **step to `k-1`**, load `V_{k-1}`, write `5`"
(`k` decreasing, toward the boundary). These disagree on direction. The B-cmp.1 round-trip above is
**direction-agnostic** (it just probes to the current marker and returns), so nothing built is affected.
But B-cmp.2 must pick one. Leaning toward the §N+20-prose direction (marker starts at the boundary `k=0`,
walks deeper): it makes the **first** round need no traverse (cheapest base case) and matches "the traverse
grows as the marker moves deeper." Under that reading the marker-advance middle is: at the `5` (position
`k`), write `V_k` back, move **R** one more cell to read `α[k+1]` into state as `V_{k+1}`, write `5` there,
then the LEFT walk returns over `blk ++ [V_k]` (now `k+1` digits). Confirm with the port-8051 consult when
opening B-cmp.2.

**Brick queue (updated):** B-cmp.0 ✅, B-cmp.1 ✅ (foundation + composition). NEXT = **B-cmp.2 marker
advance** (resolve direction first), then B-cmp.3 output read+consume, B-cmp.4 round step, B-cmp.5 compare
loop, B-cmp.6 accept/reject dispatch, B-cmp.7 park-time sentinels + relocation. After R-cmp: R-S dovetail →
R-C/R-MC/B-W → discharge `ceer_realizes` → drop `axiom_ceer_fp_embedding`.

### N+22 — R-cmp B-cmp.2 marker-advance COMPLETE (the matched-digit step). Direction resolved = marker deepens. Next design gate = the digit-compare state space (B-cmp.4).

**Built this session (2026-06-27):** `lemma_cmp_marker_advance` in `src/tm_cmp_traverse.rs` — the
marker-ADVANCING round-trip (B-cmp.2), the variant of B-cmp.1 whose middle does the marker work instead of
a no-op rewrite. Same probe skeleton (right-walk → middle → left-walk) but: the entry state `q_back` carries
the recorded frontier value `vk` (value-in-state, forced by n=5); the middle is two steps —
`(q_back, 5, vk, q_read, R)` restores `vk` into the marked cell and steps onto `α[k+1]=s`, then
`(q_read, s, 5, q_walk, L)` writes the new `5`-mark at position `k+1`, records `s = V_{k+1}` into `q_walk`,
and steps back onto the just-restored `vk`; the left-walk then returns over `[vk] ++ drev(blk)` (the prefix
grown by `vk`).

**Net effect (ensures):** `v == dpack(blk ++ [vk]) + m^{k+1}·(5 + m·suf)` — the **same invariant shape** as
entry with `(prefix, k, tail) → (blk ++ [vk], k+1, 5 + m·suf)`. Head ends one cell into `u` scanning the
output frontier `u % m`, in `q_walk` holding the next frontier value `s`. Fuel `2k+3`. This is exactly the
inductive step the B-cmp.5 compare loop iterates: each call grows the restored α prefix by one digit, slides
the marker one deeper, and threads the next-position value through the state. Crate **1740/0**, committed
(9731736). No escape hatches.

**Marker-direction question (flagged in §N+21) RESOLVED — marker deepens (`k` increasing).** Re-derived
geometrically: each round consumes one output digit to `0` (gap in `u` grows, crossed by `skip0_left`,
B-cmp.0) and slides the α marker one cell deeper into `v` while keeping all of α in `v` (the restored prefix
between boundary and marker grows, traversed by the balanced probe, B-cmp.1/.2). You CANNOT advance by
pushing the restored digit into `u` — that's the §N+20 pollution flaw. So the prefix lives in `v`, the
marker deepens, and the traverse grows O(|α|) per round (O(|α|²) total). The "step to k-1" in the older
brick line was the error; the §N+20 prose (marker deeper, traverse grows) is correct. `lemma_cmp_marker_advance`
implements this and verifies, confirming the geometry closes.

**Brick queue:** B-cmp.0 ✅, B-cmp.1 ✅ (probe), B-cmp.2 ✅ (marker advance). NEXT = **B-cmp.3 output
read+consume** then **B-cmp.4 round step** — but B-cmp.4 hits a **new design gate**: the digit COMPARE. Both
operands live in finite control (`d_o` read from the output frontier, `V_k` the marker value already in the
state), so the compare is a 2-D state branch (≈4×4 transitions) splitting into match (consume output→`0`,
fire `lemma_cmp_marker_advance`) vs mismatch (→ reject dispatch). Pin that state-space encoding (and the
sentinel/exhaustion paths, B-cmp.6) — likely a port-8051 consult — before building B-cmp.4. B-cmp.3 (cross
the gap with `skip0_left`, land on `output[k]`, read its value into the compare state) is buildable now and
is the clean bridge into B-cmp.4. After R-cmp: R-S dovetail → R-C/R-MC/B-W → discharge `ceer_realizes`.

### N+23 — R-cmp B-cmp.3 + B-cmp.4 COMPLETE. Compare state-space PINNED (port-8051 co-design): value-in-state families + boundary-transition-on-gap-0 (caught a determinism collision).

**Built this session (2026-06-27, crate 1740 → 1753/0, additive, no escape hatches):** `lemma_cmp_gap_cross`
(B-cmp.3) and `lemma_cmp_match_round` (B-cmp.4) in `src/tm_cmp_traverse.rs`.

**The compare state-space — PINNED (two port-8051 consults). Value-in-state FAMILIES indexed by `V ∈ 1..4`**
(`q_walk(V)`, `q_cmp(V)`, `q_back(V)` are 4 parallel state-tracks). The steady-state round (gap `g ≥ 1`
always, since each prior match consumed an output digit to `0`):
  1. `(q_read, s, 5, q_walk(s), L)` — read+remark (marker-advance step 3): save the next α digit `s` in state.
  2. `(q_walk(s), 1..4, same, q_walk(s), L)` — left-walk the α prefix back to the boundary.
  3. `(q_walk(s), 0, 0, q_cmp(s), L)` — **BOUNDARY TRANSITION** (the gap-`0` is the *virtual boundary marker*).
  4. `(q_cmp(s), 0, 0, q_cmp(s), L)` — skip the consumed-output gap.
  5. `(q_cmp(s), d_o, 0, q_back(s), R)` if `d_o == s` — MATCH: consume output→`0`, go STRAIGHT to the
     marker-advance entry state `q_back(s)`; else `(q_cmp(s), d_o, d_o, q_reject, ·)` — MISMATCH.

**⚠ THE DETERMINISM COLLISION (caught at design time, before B-cmp.4).** Output and α share the `1..4`
alphabet. The naive compare `(q_walk(V), V, 0, q_match, R)` would COLLIDE with marker-advance's left-walk
`(q_walk(V), V, V, q_walk, L)` — same `(q,a)=(q_walk,V)` ⟹ breaks `tm_wf` determinism in the assembled
machine. **Fix = switch state on the first gap-`0`** (which always separates the α-region from the
output-region post-match): `q_walk(V)` handles `{1..4 → walk L, 0 → q_cmp(V) L}`; `q_cmp(V)` handles
`{0 → skip L, 1..4 → compare}`. Both deterministic, no collision. n=5 has no spare symbol for a real boundary
marker (would need n=6), so gap-`0` detection is forced. The RIGHTWARD return has NO collision — `q_back(V)`
uniformly handles `{0 → skip-R, 1..4 → walk-R, 5 → marker-step}` (all distinct scanned symbols), so the
match-action's return walk feeds marker-advance's right-walk seamlessly in one state.

**B-cmp.3 `lemma_cmp_gap_cross`** — entry = marker-advance's exit (head one cell into `u` scanning the output
stack's low cell `U%m`, `u==U/m`, `U==pile_zeros(d_o + m·out_rest, g, m)`, gap `g ≥ 1`, state `q_walk`). First
step does the boundary transition `(q_walk, 0, 0, q_cmp, L)`, then `lemma_skip0_left` in `q_cmp` skips the
rest, landing scanning `d_o` in `q_cmp`. Output `{u: out_rest, v: pile_zeros(c.v, g, m), a: d_o, q: q_cmp}`.
Fuel `g`. (Revised mid-session from a first cut that landed in `q_walk` — that cut verified in isolation but
would have collided at assembly; the determinism check is what forced the boundary-transition redesign.)

**B-cmp.4 `lemma_cmp_match_round`** — the MATCH round, end-to-end. Entry = B-cmp.3 output with `d_o == vk`.
Composes: (1) compare-match `(q_cmp, vk, 0, q_back, R)` consume + step; (2) `lemma_skip0_right` return walk
over the gap to α-low (= marker-advance entry — NO glue state, since match → `q_back(vk)` directly);
(3) `lemma_cmp_marker_advance`. Net: α prefix grows by `vk`, marker slides `k → k+1`, gap grows `g → g+1`,
head ends one cell into `u` scanning `0` in `q_walk` holding next value `s` — the **same INV shape** B-cmp.5
iterates (feeds the next B-cmp.3 with gap `g+1`). Fuel `2·|blk| + g + 4`. In the loop `g == |blk| == k`
(each round consumes one output digit AND advances the marker), so per-round fuel is `4k+4` (O(|α|²) total).

**Exhaustion/ACCEPT design (PINNED, consult 1 Q3 — not yet built, = B-cmp.6):** marker-advance reading `5`
(α exhausted, far sentinel) → `q_verify_end`; then output `0` → ACCEPT, output `1..4` → REJECT (output too
long). Output exhausted (skip0_left hits the output far sentinel while expecting a digit) → REJECT (too
short). B-cmp.1 (balanced probe) = base case only (gap 0); steady state self-sustains via marker-advance.

**Brick queue:** B-cmp.0 ✅, B-cmp.1 ✅ (probe), B-cmp.2 ✅ (marker advance), B-cmp.3 ✅ (gap-cross +
boundary), B-cmp.4 ✅ (match round). NEXT = **B-cmp.5 compare loop** (induction over B-cmp.4∘B-cmp.3 with
`g==k`, accumulating the matched prefix) then **B-cmp.6 accept/reject dispatch** (the `q_verify_end`
exhaustion variant of marker-advance + drive-to-origin / clear+rewind+INC) + **B-cmp.7 park-time sentinels**.
After R-cmp: R-S dovetail → R-C/R-MC/B-W → discharge `ceer_realizes` → drop `axiom_ceer_fp_embedding`.

### N+24 — R-cmp B-cmp.5 STEP done (`lemma_cmp_round`); full loop threading + value-in-state family structure WORKED OUT (handoff for the loop induction).

**Built this session (crate 1753 → 1754/0):** `lemma_cmp_round` in `src/tm_cmp_traverse.rs` — the **induction
STEP** of the compare loop: one matched round `INV(k) → INV(k+1)`, composing B-cmp.3 (`lemma_cmp_gap_cross`)
∘ B-cmp.4 (`lemma_cmp_match_round`) via `lemma_tm_run_split`. Fuel `2·|blk| + 2·g + 4` (`= 4k+4` when
`g==|blk|==k`). Entry/exit are the same INV shape, so it iterates cleanly. Verified, additive, no escape hatches.

**The INV(k) shape (PINNED, verified by `lemma_cmp_round`'s entry/exit matching):**
  - `v = dpack(blk, m) + m^{|blk|}·w`, `w = m·whi + 5`, `whi = m·suf + s` — restored prefix `blk = α[0..k-1]`,
    marker `5` at position `k` HIDING `α[k] = vk` (value in state), `s = α[k+1]` the next α digit, `suf = α[k+2..]`.
  - `u = pile_zeros(out_rest, k-1, m)`, `a = 0` — head one cell into `u`; full output stack
    `= pile_zeros(α[k]+m·out_rest, k, m)` (gap `k`, i.e. `k` consumed-output `0`s, then output frontier `α[k]`).
  - `q = q_walk(α[k])`.
  Round `k` matches `output[k]` vs `α[k]=vk`; MATCH requires `output[k]==α[k]`. The round also reads `α[k+1]=s`
  (needs `s ∈ 1..4`); when `α[k+1]` is the far `5` sentinel (α exhausted) the round can't fire → B-cmp.6.

**THE LOOP THREADING (worked out, ready to grind — induct on a digit list `ds`).** Carry
`ds = [α[k0], α[k0+1], …, α[k0+n]]` (length `n+1`, all `∈ 1..4`): `ds[0..n-1]` are the `n` matched digits
(`output[k0+i] == ds[i]`), `ds[n] = α[k0+n]` the final lookahead (the hidden value at `INV(k0+n)`). Plus
`pre = α[0..k0-1]` (|pre|=k0), `suf = α[k0+n+1..]`, `out_above = output[k0+n..]`, `g` (gap, `==k0`).
Express INV via:
  - α-above-marker `= dpack(ds.drop_first(), m) + m^{ds.len()-1}·suf`;  `v = dpack(pre) + m^{|pre|}·(5 + m·(α-above))`.
  - output pre-gap `= dpack(ds.take(ds.len()-1), m) + m^{ds.len()-1}·out_above`;  full output stack
    `= pile_zeros(output-pregap, g, m)`, INV `a = ·%m`, `u = ·/m`.
**Recursion** (`ds → ds.drop_first()`, decreases `ds.len()`, base `ds.len()==1` = 0 rounds): one
`lemma_cmp_round` then recurse with `pre ++ [ds[0]]`, `g+1`, `suf`/`out_above` unchanged. **The algebra LINES
UP** (verified by hand): `lemma_cmp_round`'s exit `v = dpack(pre++[ds[0]]) + m^{k0+1}·(m·suf_r + 5)` equals the
recursive INV's `v` because the round's `suf_r` (= α-above the new marker = `α[k0+2..]`) IS the recursive
`whi'`; exit `u = pile_zeros(out_rest, g)` feeds the recursive entry as `pile_zeros(·, g+1)/m` (gap grows by 1);
key Seq lemma = `lemma_dpack_append` (`dpack(a++b) = dpack(a) + m^{|a|}·dpack(b)`). Exact fuel:
`spec fn cmp_loop_fuel(k0, g, n) decreases n { if n==0 {0} else { (2·k0 + 2·g + 4) + cmp_loop_fuel(k0+1, g+1, n-1) } }`.

**⚠ STRUCTURAL COMPLICATION for the loop (the real work):** the compare/marker quintuples depend on the
per-round value `vk = ds[i]`, which VARIES. So the loop lemma's states must be **value-indexed functions**
(`q_walk, q_cmp, q_back: spec_fn(nat)->nat`; `q_read: nat` SHARED) and the quintuple hypotheses
**quantified over `V ∈ 1..4`** (∃-index or a finder), with per-round index extraction. The pinned family
(N+23) instantiated: `(q_walk(V),0,0,q_cmp(V),L)`, `(q_cmp(V),0,0,q_cmp(V),L)`, `(q_cmp(V),V,0,q_back(V),R)`,
`(q_back(V),0,0,q_back(V),R)`, `(q_back(V),d,d,q_back(V),R)` ∀d∈1..4, `(q_back(V),5,V,q_read,R)`,
`(q_read,V,5,q_walk(V),L)` [q_read dispatches by scanned digit], `(q_walk(V),d,d,q_walk(V),L)` ∀d∈1..4.

**Brick queue:** B-cmp.0..B-cmp.4 ✅, B-cmp.5 STEP ✅ (`lemma_cmp_round`). NEXT = **B-cmp.5 loop induction**
(value-indexed families + quantified quintuples + `ds` induction, threading above) → **B-cmp.6 accept/reject**
(consult 3 Q3: ACCEPT must WIPE both tapes to literal `tm_origin()=(0,0,0,0)` — α "restore" is a proof
invariant, NOT the final state; clean-up = wipe `v`, wipe `u`, home; REJECT = clear output + rewind + INC + re-dovetail)
→ **B-cmp.7 dual far-`5` sentinels** (consult 3 Q2: far `5` on `u` = output end, far `5` on `v` = α end;
ACCEPT iff both hit same round; output-`5`-while-α-digit → REJECT too-short, α-`5`-while-output-digit → REJECT
too-long). After R-cmp: R-S dovetail → R-C/R-MC/B-W → discharge `ceer_realizes` → drop `axiom_ceer_fp_embedding`.

#### N+24 addendum — `lemma_cmp_round` walk-states SPLIT (second design bug caught working toward the loop) + loop encoding decision.

**Second bug caught + fixed (crate 1754/0, additive):** `lemma_cmp_round` originally used ONE `q_walk` param
for BOTH the entry-boundary state and the exit state. With value-in-state families the entry carries the
CURRENT value `vk` (state `q_walk(vk)`) and the exit carries the NEXT value `s` (state `q_walk(s)`) — DIFFERENT
tracks since `vk ≠ s` in general. It verified in isolation (degenerate `q_walk_in==q_walk_out`) but would NOT
chain in the loop. **Fixed:** `lemma_cmp_round` now takes `q_walk_in` (entry, `=q_walk(vk)`) and `q_walk_out`
(exit, `=q_walk(s)`); the loop feeds round `k`'s `q_walk_out` as round `k+1`'s `q_walk_in`. (marker-advance /
match_round were already correct — their entry `q_back`/`q_cmp` and exit `q_walk` are distinct params.)

**⚠ OPEN DESIGN DECISION for the loop induction — the value-indexed quintuple-hypothesis encoding.** Three
options, each with a real tradeoff (pick before building B-cmp.5 loop; candidate for a port-8051 consult):
  - **(a) spec_fn state+index functions** (`q_walk,q_cmp,q_back: spec_fn(nat)->nat`, index fns
    `spec_fn(nat)->int`), quintuple hyps `forall V∈1..4`. Cleanest signature, BUT spec_fn applications inside
    `forall` hit Verus/Lean trigger-inference pain (see memory `reference_tactus_quantified_specfn_no_fold` /
    `feedback`); likely needs a recursive-predicate reformulation or careful `#![trigger]`.
  - **(b) concrete per-value params** (`q_walk1..q_walk4`, … ~80 params + ~56 quint hyps, NO forall). Verbose
    but trigger-free; per-round dispatch is a `match (ds[0], ds[1])` (16 branches — entry track from `ds[0]`,
    exit track from `ds[1]`).
  - **(c) bundle quints in a spec PREDICATE with ∃-index, `choose` per round.** Medium; the choose extraction
    per round is mechanical but adds proof bulk.
  Recommendation: try (a) with a recursive-predicate hypothesis (avoids the bare-forall trigger issue) before
  falling back to (b). The digit-list/dpack/fuel threading (N+24 body) is encoding-independent and ready.

### N+25 — R-cmp B-cmp.5 LOOP induction COMPLETE (`lemma_cmp_loop`). The whole matched-rounds compare loop is machine-checked.

**Built (crate 1754 → 1764/0, additive, no escape hatches):** new module `src/tm_cmp_loop.rs`. The encoding
decision resolved to **a hybrid of (a)+(c)** that dodges the trigger trap cleanly: value-indexed spec-fn states
`qw, qc, qb: spec_fn(nat)->nat` (+ shared `qr: nat`), but the 14 per-value quintuples are bundled behind a
**named** `open spec fn cmp_quints_present(tm, qw, qc, qb, qr, V)` whose body holds the `has_quint(…)`
existentials. The availability hypothesis is `forall|V| #![trigger cmp_quints_present(…,V)] 1≤V≤4 ==>
cmp_quints_present(…,V)` — the trigger is the named predicate, so the bare `qw(V)` spec-fn apps stay HIDDEN in
its body (never a forall trigger). Per round, `assert(cmp_quints_present(…,vk))` + `assert(…,s)` instantiate it,
and `extract_quint` (`choose` wrapper) pulls the concrete indices for `lemma_cmp_round`.

**Pieces (all verified):**
  - Spec helpers `cmp_above` (α digits above marker), `cmp_marker` (`= m·cmp_above + 5`), `cmp_out_pregap`
    (the `n` matched output digits `ds[0..n-1]` + `out_above`), `cmp_inv_config` (the `INV(k)` TmConfig over
    `(pre, ds, suf, g, out_above)`), `cmp_loop_fuel(k0, g, n)` (recursive sum of the per-round step fuels).
  - `lemma_cmp_above_step` / `lemma_cmp_out_pregap_step` — peel `ds[0]` (the marked / frontier digit) so the
    `cmp_inv_config` entry matches `lemma_cmp_round`'s spelled-out preconds (`whi == s + m·suf_param`,
    `cmp_out_pregap(ds) == vk + m·out_rest`). The one Seq subtlety: `ds.subrange(0,n-1).drop_first() =~=
    ds.drop_first().subrange(0,n-2)` (both `= ds.subrange(1,n-1)`), discharged by `=~=` extensionality.
  - `lemma_cmp_round_packaged` — one round in `cmp_inv_config` form (`INV → INV'` for `pre++[ds[0]]`,
    `ds.drop_first()`, `g+1`), fuel `2|pre|+2g+4`; extracts indices, matches entry/exit to `lemma_cmp_round`.
  - `lemma_cmp_loop` — `decreases ds.len()`, base `ds.len()==1` (0 rounds), step = packaged round ∘ recurse,
    fuel composed by `lemma_tm_run_split`. **Ensures**: `tm_run(c, cmp_loop_fuel(|pre|, g, ds.len()-1)) ==
    cmp_inv_config(qw, pre ++ ds.subrange(0,n), ds.subrange(n,len), suf, g+n, out_above, m)` — i.e. land at
    `INV(k0+n)` with the marker on the lookahead `ds[n]`. Recursion seq-arg equalities (`pre2 ++ ds2.sub(0,..)
    =~= pre ++ ds.sub(0,..)`, `ds2.sub(end) =~= ds.sub(end)`) by `=~=`; the `=~=`→`==` lift makes the two
    `cmp_inv_config` calls congruent.

**Brick queue:** B-cmp.0..B-cmp.5 ✅ (STEP `lemma_cmp_round` + LOOP `lemma_cmp_loop`). **NEXT = B-cmp.6
accept/reject** — the EXHAUSTION transitions out of the steady-state loop. The loop's marker-advance reads the
NEXT α digit `s∈1..4`; when α is exhausted it reads the far-`5` sentinel instead (a DIFFERENT step than
`lemma_cmp_marker_advance`, whose precond is `1≤s≤4`). Design (consult 3 Q2/Q3, settled at high level):
α-exhaust → `q_verify_end`; then output frontier `0` ⟹ ACCEPT, output `1..4` ⟹ REJECT (output too long);
output-exhaust (skip0_left hits the output far-`5` while expecting a digit) ⟹ REJECT (too short). ACCEPT then
WIPES both tapes to literal `tm_origin()=(0,0,0,0)` (the α "restore" is only a proof invariant); REJECT =
clear output + rewind + INC + re-dovetail. → **B-cmp.7 dual far-`5` sentinels** (u=output-end, v=α-end). After
R-cmp: R-S dovetail → R-C/R-MC/B-W → discharge `ceer_realizes` → drop `axiom_ceer_fp_embedding`.

### N+26 — R-cmp B-cmp.6 design PINNED (two port-8051 consults) + the REJECT bricks (mismatch + too-short) DONE.

**Design pinned (consults 4 & 5, 2026-06-27).** Two corrections to the consult-3 sketch, both caught at the
config level:
  - **No Stay direction.** `apply_quint` has only `Dir::R`/`Dir::L` (no Stay) — every reject/halt transition
    MUST move L or R. The consult's `S`-moves are replaced by real L/R steps.
  - **Accept = scan the SENTINEL `5`, not blank `0`.** Accepting on `0` is ambiguous (could be an interior
    gap blank). Both string-ends carry a far-`5` sentinel (B-cmp.7), and ACCEPT fires when the head reaches
    the sentinel. The earlier "output `0` ⟹ accept" wording was pre-sentinel.
  - **Accept geometry (confirmed).** At ACCEPT (output == α, same length `L`, all matched): every output
    digit was consumed to `0`, so the output region in `u` is **all `0`** (the gap = whole output region),
    with the **output far-`5` sentinel at `u`'s high end**; `v` = the fully restored α digits + the marker(s)
    + the α far-`5`. Crossing the gap (skip-`0`) lands on the output sentinel — that scan-`5` IS the accept
    signal. The wipe is then asymmetric: `u` is already all-`0` (just clear the one sentinel), `v` needs a
    real digit-block wipe (no internal `0`s in `v`, so "wipe-until-blank" is sound). End at `tm_origin()`.
  - **Reject = pure sink.** Every failure path (mismatch / too-short / too-long) transitions to a single
    `q_reject`; the OUTER dovetail **R-S** owns the cleanup (clear output → rewind → increment candidate →
    re-dovetail). So a B-cmp.6 reject brick's only obligation is "reach `q_reject`".
  - **Build order (consult):** REJECT bricks first (layout-light) → B-cmp.7 sentinels (pin the far-`5`
    layout) → B-cmp.6 ACCEPT wipe (co-designed with .7, since the accept tape state IS the .7 layout).

**Built (crate 1764 → 1766/0, additive, no escape hatches):**
  - **Generalized `lemma_cmp_gap_cross`** — bound `1≤d_o≤4`, `n≥4` → `1≤d_o≤5`, `n≥5`. The SAME gap-cross now
    lands on a digit (MATCH/mismatch dispatch) OR the far-`5` (too-short reject). Weaker precond for the
    `lemma_cmp_round`/`_loop` callers (they pass `d_o=vk∈1..4`); whole chain re-verified green (no regression).
  - **`lemma_cmp_mismatch_round`** (`src/tm_cmp_decide.rs`, new) — from `INV(K)`, gap-cross lands on output
    frontier `d_o∈1..4`; when `d_o≠vk` the quint `(q_cmp, d_o, d_o, q_reject, R)` fires ⟹ `q_reject`. Fuel `g+1`.
  - **`lemma_cmp_tooshort_round`** — from `INV(K)`, gap-cross lands on `d_o=5` (output sentinel, α still has
    a digit pending); `(q_cmp, 5, 5, q_reject, R)` ⟹ `q_reject`. Fuel `g+1`.

**Brick queue:** B-cmp.0..B-cmp.5 ✅, B-cmp.6 REJECT mismatch+too-short ✅. **NEXT = B-cmp.6 too-long reject**
(the α-exhaust path: marker-advance reads the α far-`5` instead of a digit `s∈1..4` → `q_verify_end`; then the
output frontier digit `1..4` ⟹ `q_reject`). This needs the α-exhaust marker-advance variant (a sibling of
`lemma_cmp_marker_advance` whose `s`-read is `5` not `1..4`) feeding `q_verify_end`. **Then B-cmp.7 sentinels →
B-cmp.6 ACCEPT wipe** (`q_wipe_v` right-wipe-until-blank + return to origin; `u` already all-`0`). After
R-cmp: R-S dovetail → R-C/R-MC/B-W → discharge `ceer_realizes` → drop `axiom_ceer_fp_embedding`.

### N+27 — R-cmp B-cmp.6 α-EXHAUST DECISION PATH COMPLETE (the whole compare decision surface is machine-checked). Far-sentinel encoding `suf=5` confirmed (port-8051 consult). Decision lemmas refactored to a uniform `INV` entry.

**Design confirmed (port-8051 consult, this session, 2026-06-27):** (1) the far-α-sentinel is encoded as
`suf == 5` threaded through the existing loop — when the loop reduces `ds` to the last digit, `cmp_above([last],
5, m) == 5`, so the cell above the marker (hiding the last α digit) IS the far-`5` sentinel, with all blank
above (`whi == 5`). Zero new loop machinery. (2) the α-exhaust transition `(q_read, 5, 5, q_verify_end, L)` is a
distinct scanned symbol from the normal `(q_read, s, 5, qw(s), L)` dispatch (`s∈1..4`), so no `tm_wf`
determinism collision. (3) build the α-exhaust marker-advance variant FIRST as the shared anchor for both
too-long and ACCEPT; (4) ACCEPT geometry decoupled — prove "reaches `q_accept`", leave the tape-wipe to a
separate cleanup brick.

**Built (crate 1766 → 1785/0, additive, no escape hatches):**
  - **`lemma_cmp_marker_advance_end`** (`tm_cmp_traverse.rs`) — the α-exhaust marker-advance primitive (the
    shared anchor). Phases 1–2 identical to `lemma_cmp_marker_advance` (walk right to the `5` mark, restore
    `vk`, step R), but phase-2 lands scanning the far sentinel `5` (`whi == 5`); the α-exhaust transition
    `(q_read, 5, 5, q_verify_end, L)` re-writes the sentinel and the left-walk returns the fully-restored α to
    `v`. Net `v == dpack(blk ++ [vk]) + m^{|blk|+1}·5` (α restored + exhausted, far sentinel on top, NO marker),
    head one cell into `u` at the output frontier in `q_verify_end`. Fuel `2·|blk| + 3` (same as the normal
    advance).
  - **`lemma_cmp_match_round_end`** (`tm_cmp_traverse.rs`) — the FINAL matched round (sibling of
    `lemma_cmp_match_round`): compare-match the last digit + return-walk + `lemma_cmp_marker_advance_end`,
    landing at the `q_verify_end` boundary. Fuel `2·|blk| + g + 4`.
  - **`lemma_cmp_accept_decide`** (`tm_cmp_decide.rs`) — ACCEPT end-to-end (reaches `q_accept`): from the
    loop-exit `INV`, gap-cross #1 → `lemma_cmp_match_round_end` → verify-end gap-cross #2 reads the output
    far-`5` sentinel → `(q_verify_cmp, 5, 5, q_accept, R)`. Output `==` α (equal length, all matched). Fuel
    `2·|blk| + 3·g + 6`.
  - **`lemma_cmp_toolong_round`** (`tm_cmp_decide.rs`) — too-long reject end-to-end (reaches `q_reject`): same
    `INV` entry, but the output continues with a digit `d_o2∈1..4` above the last matched one → α exhausted but
    output longer → `q_reject`. Fuel `2·|blk| + 3·g + 6`.

**Decision-lemma entry made UNIFORM** (refactor): `lemma_cmp_accept_decide`/`lemma_cmp_toolong_round` now start
from the loop-exit `INV` (head one cell into `u` scanning gap-`0`, the `q_walk` track), prepending gap-cross #1,
exactly like the existing `lemma_cmp_mismatch_round`/`lemma_cmp_tooshort_round`. So the eventual assembly is a
clean branch on the gap-cross frontier `d_o`: `d_o==vk` (last digit, lookahead) → accept (if output exhausts) /
too-long (if output continues); `d_o∈1..4, ≠vk` → mismatch; `d_o==5` → too-short. Each branch's lemma does its
own gap-cross internally — only the value-selected one fires, no double-cross.

**B-cmp.6 DECISION SURFACE COMPLETE** — all five compare outcomes machine-checked: match-loop (`lemma_cmp_loop`),
mismatch (`lemma_cmp_mismatch_round`), too-short (`lemma_cmp_tooshort_round`), too-long (`lemma_cmp_toolong_round`),
ACCEPT (`lemma_cmp_accept_decide`). The α-exhaust path consumes the dual far-`5` sentinels purely via
preconditions (`whi==5` α-side, `out_rest==5`/`d_o2` output-side, the `(q_verify_cmp, 5, …)` accept quint), so the
`q_verify_end` output-read anchor the handoff flagged is in place and proven to compose.

**Brick queue:** B-cmp.0..B-cmp.5 ✅, B-cmp.6 ✅ (mismatch + too-short + too-long + ACCEPT-reaches-`q_accept`, all
decision outcomes). **NEXT = B-cmp.7 first-round / gap-`0` ENTRY (design CONFIRMED, build is the next brick).**

**B-cmp.7 first-round design (port-8051 consult, 2026-06-27): OPTION B = a dedicated BOOTSTRAP gadget with a
DISJOINT state space (`q_start`, `q_boot(d)`), keeping every steady-state brick untouched.** The wrinkle: the
loop / marker-advance / match-round / decision bricks ALL require a non-empty restored prefix (`blk.len() ≥ 1`)
and `g ≥ 1` (a prior consumed-output `0`). But the true R-cmp entry has an EMPTY prefix, NO marker placed yet,
and `g == 0`. Relaxing `blk.len() ≥ 1` was rejected (lemma rot — would force re-verifying every steady-state
transition for the empty case). So the first compare is a bespoke gadget; because `Q_boot ∩ Q_steady = ∅`, the
existing bricks stay valid. **Target: `c_entry → INV(1)`** (or a first-position decision state), where `INV(1) =
cmp_inv_config(qw, [α[0]], [α[1],…], 5, g=1, out_above, m)` — prefix `[α[0]]` restored, marker on `α[1]`, the
`output[0]→0` consumed gap, head one cell into `u` scanning it, state `qw(α[1])`.

**MECHANICS RESOLVED (traced this session) = PARKED-`g=1` + empty-prefix siblings.** The two-stack (Minsky)
model made the bootstrap subtler than the high-level sketch; three sub-questions, all now resolved: (1) **Gap
creation** — the parked layout leaves ONE boundary `0` below `output[0]` so the entry is `g=1` directly (the
cleanest of the options; a B-cmp.7 emit-wiring requirement). (2) **No double-consume** — marker PLACEMENT (write
`5` onto `α[0]`, record `α[0]`) must NOT consume `output[0]` (the round-at-`k=0` consumes it). With parked-`g=1`
the placement is a clean **2-step** gadget that touches only `v` and the boundary `0`: from the entry `{a:0
(boundary), u:output, v:[α[0],α[1],…,sentinel], q_start}`, step `(q_start, 0, 0, q_read_α, R)` pops `α[0]` into
the head, then `(q_read_α, α[0], 5, qw(α[0]), L)` writes the marker `5` and records `α[0]` — landing at exactly
`INV(0)` (`g=1`, empty prefix, marker on `α[0]`), `output` untouched. (3) **Empty-prefix advance / side-
separation** — to reach `INV(1)` the marker advances `α[0]→α[1]` while RESTORING `α[0]` to `v` as the prefix; you
cannot move right past `α[0]` without pushing it onto `u` (the §N+20 pollution flaw), so the side-preserving
route is the balanced right-then-left probe with phase-1 walk = 0 (head already on the marker). **BUILT this
session — THE FULL FIRST-ROUND BOOTSTRAP `parked-entry → INV(1)` (crate 1785 → 1801/0, additive, no escape
hatches):** **`lemma_cmp_marker_advance_empty`** (`tm_cmp_traverse.rs`, the `blk=[]` marker advance — head scans
the marker `5` directly; fuel `3`); **`lemma_cmp_match_round_empty`** (`tm_cmp_traverse.rs`, the `blk=[]` match
round `INV(0)→INV(1)` = compare-match + return-walk-onto-marker + `marker_advance_empty`; fuel `g+4`);
**`lemma_cmp_place_marker`** (`tm_cmp_traverse.rs`, the 2-step entry gadget `parked → INV(0)`: pop `α[0]`, write
the marker `5`, record `α[0]`, output untouched; fuel `2`); and the capstone **`lemma_cmp_bootstrap`**
(`tm_cmp_decide.rs`, `parked-entry → INV(1)` = `place_marker ∘ gap-cross(g=1) ∘ match_round_empty`; fuel `8`).
The value-indexed states thread correctly: placement + first gap-cross run in `α[0]`'s track (`qw_a0`/`qc_a0`/
`qb_a0`), the match's exit (after recording the lookahead `s=α[1]`) is `α[1]`'s track `qw_s` — exactly the state
`INV(1)` expects, so the steady-state `lemma_cmp_loop` runs unchanged from there. **B-cmp.7 compare-internal
bootstrap COMPLETE.** **REMAINING (true emit-coupling, "done LAST"):** the park-time emit-wiring that produces
the `lemma_cmp_bootstrap` entry interface (the dual far-`5` sentinels into `tm_rp`/emit output + the one boundary
`0` for `g=1`); then the full compare-decides assembly (`bootstrap → cmp_inv_config bridge → loop → branch on
gap-cross frontier`); then the deferred ACCEPT tape-wipe cleanup.

**Then:** the park-time sentinel insertion (wire the dual far-`5` sentinels into `tm_rp`/emit output — the plan's
"done LAST to avoid perturbing verified emit lemmas") + the full compare-decides assembly (loop ∘ branch on
gap-cross frontier `d_o`: `==vk`→accept/too-long, `∈1..4≠vk`→mismatch, `==5`→too-short) + the deferred **ACCEPT
tape-wipe** cleanup (`u` already all-`0`, `v` needs a digit-block wipe to `tm_origin`). After R-cmp: R-S dovetail →
R-C/R-MC/B-W → discharge `ceer_realizes` → drop `axiom_ceer_fp_embedding`.

### N+28 — R-cmp B-cmp.8 COMPARE-DECIDES ASSEMBLY COMPLETE (the whole decision surface composes end-to-end from the parked entry, all five outcomes). Danielle co-design: Assembly→Relocation; relocation = wipe→transfer→stamp→g=1.

**Port-8051 consult (this session, 2026-06-27):** confirmed the emit-coupling design + sequencing.
(1) The relocation must **wipe `u` scratch** first (the `copy_u` spent master), then **transfer output
`v→u` REVERSED** (a rightward head-walk over `od` naturally reverses it: each R-move pops `v`-low into the
head, pushes the prev head onto `u`-low — so `od[L-1]` ends at `u`-low, the correct low-to-low pairing with
the reversed-α `v`-low, Finding-1), then **stamp the output far-`5`** at the top (the `lemma_cmp_accept_decide`
"clean ceiling" requires the far-`5` immediately above the exhausted output, `out_rest==0` — scratch debris
between would mis-trigger too-long/mismatch). (2) The **α far-`5` sentinel is written at PARK time** (`tm_rp`),
the **`g=1` boundary `0` is created by the transfer** (the head stops exactly at the gap-`0`). (3) **Sequencing
= Assembly → Relocation:** define the parked-entry CONTRACT first (lock the compare's input interface), THEN
prove the relocation produces it ("Relocation ⟹ Contract" beats building a relocation for a moving target).

**BUILT this session — THE FULL COMPARE-DECIDES ASSEMBLY (`tm_cmp_assemble.rs`, crate 1801 → 1833/0, additive,
no escape hatches).** The comparator now provably reaches `q_accept` ⟺ output `==` α and `q_reject` otherwise,
end-to-end from the parked entry, for EVERY output/α relation. Two layers:

  - **`lemma_cmp_reach_inv_p`** — THE REUSABLE CORE (bootstrap ∘ bridge ∘ loop). From the parked entry whose
    output matches α on a length-`p` prefix (`u == dpack(α[0..p]) + m^p·out_tail`, the divergent/sentinel
    remainder `out_tail` above; `v == dpack(α) + m^L·5`), reaches `INV(p)` — marker hiding `α[p]`, restored
    prefix `α[0..p-1]`, gap `g = p+1`, output frontier `= out_tail % m`. **The bridge insight:** the bootstrap
    exit is `cmp_inv_config` with **`g=2`** (the original boundary `0` PLUS the just-consumed `α[0]` cell, NOT
    `g=1`); `pile_zeros(out_rest, 1) == pile_zeros(cmp_out_pregap, 2)/m` ⟺ `cmp_out_pregap == out_rest`. The
    loop-`suf` carries `alpha_tail_above(α, p)` (the α value above position `p`) via the concat identity
    `lemma_bridge_suf` (`lemma_dpack_append` + `lemma_pow_nat_add`: `α[2..L]=α[2..p+1]++α[p+1..L]`,
    `m^{p-1}·m^{L-1-p}=m^{L-2}`). Every decision terminal consumes this `INV(p)` and reads only `out_tail`.

  - **Five decision terminals** (all first/second try after the core):
    - **`lemma_cmp_decides_accept`** — output `==` α (`u==v==dpack(α)+m^L·5`) → `q_accept` (`p=L-1`,
      `accept_decide` α-exhaust both sentinels).
    - **`lemma_cmp_decides_mismatch`** — `out_tail` low `= d_o ∈ 1..4`, `d_o ≠ α[p]` (`1≤p≤L-1`) → `q_reject`.
    - **`lemma_cmp_decides_tooshort`** — `out_tail = 5` (output exhausts, α has `α[p]`) → `q_reject`.
    - **`lemma_cmp_decides_toolong`** — `p=L-1`, α exhausts, output continues `d_o2∈1..4` → `q_reject`.
    - **`lemma_cmp_decides_mismatch0`** — the `p=0` first-digit mismatch (`output[0]≠α[0]`): bootstrap match
      path inapplicable, so `place_marker → mismatch_round` (fuel 4) directly. Rounds out `p≥0` coverage.

**The parked-entry CONTRACT is now locked** (the relocation's target): `a=0` (boundary, `g=1`); `u = output
reversed, far-`5` at top, NOTHING above; v = α reversed, far-`5` at top; q=q_start; output[0]==α[0] for the
match cases, the mismatch0 terminal covers the divergent first digit. **B-cmp.8 COMPLETE.**

**Brick queue:** B-cmp.0..B-cmp.7 ✅, **B-cmp.8 (decides assembly) ✅**. **NEXT = the RELOCATION gadget
(emit-coupling proper, design pinned above): wipe `u` → transfer output `v→u` reversed → stamp output far-`5`
→ land on `g=1`; α far-`5` into `tm_rp` park-time.** Then the deferred ACCEPT tape-wipe (drive `q_accept` to
`tm_origin`). After R-cmp: R-S dovetail → R-C/R-MC/B-W → discharge `ceer_realizes` → drop `axiom_ceer_fp_embedding`.

### N+29 — RELOCATION gadget: the LOCAL phase COMPLETE (WIPE ∘ STAMP+TRANSFER). `gap2_reloc.rs` 12/0, additive.

The emit-coupling proper, built bottom-up as three bricks (`gap2_reloc.rs`, crate 1833 → 1845/0, no escape
hatches). The N+28 design (wipe → transfer → stamp → g=1) executes with one build-level refinement: **the
far-`5` stamp MERGES into the transfer's first step** — `(q_reloc, 0, 5, q_xfer, R)` writes the output far-`5`
onto `u` while crossing the boundary onto `output[0]`, so the reversed output piles *above* the `5` with no
separate stamp walk and no ping-pong. The far-`5` lands at the top because the first push ends highest.

  - **B-reloc.1 — `lemma_reloc_stamp_transfer_local`/`_contract`** (the novel core). From the wiped boundary
    (`u==0, a==0, v==dpack(output)`): step 0 stamps the `5` + crosses, then [`tm_dwalk::lemma_dwalk_right`]
    peels output onto `u`. Net `u == dpile(5, output) == dpack(drev(output)) + m^L·5` (the
    [`tm_dwalk_prefix::lemma_dpile_is_dpack_drev`] bridge), `v==0`, `a==0`, `q==q_xfer`.
  - **B-reloc.2 — `lemma_reloc_stamp_transfer_tailed`/`_contract`** (the workhorse). Carries the α-block on
    `v` as a high tail via [`tm_cmp_traverse::lemma_dwalk_right_gen`] (the tail-aware right walk — NO
    `run_tail_v` needed): from `v == dpack(output) + m^L·w` (above-output value `w` = one-cell gap `0` +
    parked α-block, `w%m==0`), lands `u == dpack(drev(output)) + m^L·5`, `v == w/m` (the α-block), `a==0`
    (the `g=1` boundary, `= w%m`). Step-0 div/mod factored via `lemma_div_mod_step` (dodges the nonlinear-
    division rlimit blow).
  - **B-reloc.3 — `lemma_reloc_local`** (WIPE ∘ STAMP+TRANSFER). From the emit-end `u == copy_u(0,M,g) ==
    m^g·R(M)` (the spent master), `v == dpack(output) + m^L·w`, it runs **`gap2_master_mgmt::lemma_q_clean`
    with `t=0`** (the existing master-erase: wipe the master to `0`, return the head to the boundary in
    `q_reloc`) then B-reloc.2. The splice is **state identification** (`q_clean`'s `q_home == q_reloc`, lands
    scanning `a==0`, the stamp quint fires — no glue). `copy_u(0,M,g)` ≡ `q_clean`'s `t=0` master form via the
    `repunit` bridge; the `q_clean` precond `1 ≤ v%m ≤ 4` = `output[0]` via `div_mod_step`.

**Why no separate wipe brick:** `lemma_q_clean` (t=0) IS the master wipe — it erases `copy_u`'s ones and
returns to the boundary with `v` restored, `u==0` locally. The α-block is just part of `v` (rides through the
pile/unpile of `q_clean` automatically; its low digit is `output[0]`, so `q_clean`'s `v%m∈1..4` precond holds).

**The parked-entry CONTRACT is now PRODUCED** by `lemma_reloc_local` (local frame): `u == dpack(drev(output))
+ m^L·5` = `lemma_cmp_bootstrap`'s `u` shape with W = `drev(output)`; `v == α-block`; `a==0` (g=1); state
`q_xfer`. **Wiring reloc → compare** = state-id `q_xfer == q_start` + the value-bridge (`drev(output)` value ==
α value ⟺ `output==α` by `drev` involution ⟺ the relation, via `lemma_relnum_is_fam_digits`).

**REMAINING for R-cmp (all deferred-glue or self-contained):** (1) **u-tail-lift** — carry the surviving
dovetail/temp above the far-`5` through the relocation (deferred WITH R-S: the exact backup offset H is the
unpinned R-P/dovetail layout call; the relocation is `tail_safe` since `q_clean`'s deepest left reach is the
master separator, below the backup). (2) **reloc∘compare assembly** + value-bridge. (3) **the deferred ACCEPT
tape-wipe** (`q_accept` → `tm_origin`; from the accept config drive both stacks to `(0,0,0,0)`). After R-cmp:
R-S dovetail → R-C/R-MC/B-W → discharge `ceer_realizes` → drop `axiom_ceer_fp_embedding`.

### N+30 — RELOCATION ∘ COMPARE *DECIDES* COMPLETE (both directions). `gap2_reloc_compare.rs` + `gap2_reject_classify.rs`, crate 1845 → 1868/0, additive.

The emit→decide coupling proper: the emit-end machine provably reaches `q_accept` iff `output == α`, else
`q_reject`. A pure composition of the two pinned contracts (relocation `lemma_reloc_local` produces exactly
the comparator's parked entry), glued by `lemma_tm_run_split`. **Layout-independent** — lives entirely in the
relocation's LOCAL frame, needing none of the deferred R-S/dovetail `u`-tail (the relocation is `tail_safe`).
So N+29's "REMAINING (2) reloc∘compare assembly + value-bridge" is **DONE** at the machine level; the previous
session's caution that this coupling needed the layout was over-conservative for the local-frame decide.

  - **The state-id splice:** the relocation exits in `q_xfer` scanning `a==0`, which IS the comparator's
    `q_start` — we pass the SAME state for both, no glue step.
  - **The value bridge = `drev`:** the relocation lands the output *reversed* on `u` (a rightward digit-walk
    reverses), and α is parked *reversed* on `v`, so the comparator compares `drev(output)` vs `drev(α)` —
    equal iff `output == α` (`drev` is an involution + preserves the `1..4` digit bound). Phrased via the
    on-tape block `beta == drev(α)`; the accept premise `drev(output) =~= beta` reads forward as `output =~= α`.
    (The *content* bridge to `relnum` — `output == fam_digits(a,b)`, `dpack(output) == relnum` via the existing
    `lemma_relnum_is_fam_digits` — is the downstream R-S/R-relnum wiring, not this brick.)

**ACCEPT** (`gap2_reloc_compare::lemma_reloc_then_compare_accept`): from the emit-end tape with `drev(output)
=~= beta`, compose `lemma_reloc_local` ∘ `lemma_cmp_decides_accept` (`alpha := beta`, `q_start := q_xfer`),
reaching `q_accept` at exact fuel `reloc_compare_accept_fuel`. The `v`-tail `w == m·(dpack(beta)+m^|β|·5)`
unpacks to the parked α-block via `lemma_div_mod_step`.

**REJECT** (the divergence classifier + dispatch). `gap2_reject_classify.rs`: `cpl` (common-prefix length) +
`lemma_cpl_{le,match,diff}` (the case split is exhaustive + mutually-exclusive, cross-checked with a port-8051
consult), `lemma_dpack_far5_split` (factor `dpack(X)+m^|X|·5` at any cut), and four **u-shape** lemmas
recasting that value into each terminal's `u`. `gap2_reloc_compare.rs`: `lemma_reloc_to_parked` (shared
reloc→parked core), the four per-terminal reject assemblies (`mismatch`/`mismatch0`/`tooshort`/`toolong`), and
**`lemma_reloc_then_compare_reject`** — the generic `drev(output) != beta ⟹ q_reject`, routing by
`p == cpl(drev(output), beta)`: `p<|X|,|β|` → mismatch(0); `p==|X|<|β|` → too-short; `p==|β|<|X|` → too-long
(the `p==|X|==|β|` case is impossible — it forces `X==β`). Exact case-fuel via `reloc_compare_reject_fuel`.

**The `reject_quints` bundle** (the dispatch's comparator precondition) is the comparator's full reject-quint
set over the `1..4` alphabet (per-first-digit bootstrap read, per-`V≠d` mismatch, per-`V` too-short, verify
chain + per-digit too-long). It's a faithful over-approximation of the quints the real `psc_tm` carries (the
deterministic comparator has no state/symbol collision: reject symbols are disjoint from the match symbol `V`
and gap `0`) — **a concrete co-design target for R-S's `psc_tm` quint layout**.

**REMAINING for R-cmp:** (1) **u-tail-lift** — still deferred WITH R-S (offset `H` = the unpinned dovetail
layout). (2) **ACCEPT tape-wipe = R-C** (`q_accept` → `tm_origin`): needs the accept *config* (the existing
`lemma_cmp_decides_accept` exposes only `.q == q_accept`, not the tape), so it's a distinct config-tracing
brick (mirror `tm_cleanup`), best built with R-C. After R-cmp: R-S dovetail → R-C/R-MC/B-W → discharge
`ceer_realizes` → drop `axiom_ceer_fp_embedding`.

### N+31 — R-S dovetail design SETTLED (port-8051 co-design) + u-tail-lift HALF 1 (tail-safe relocation) DONE. crate 1868 → 1877/0, additive.

This session moved the keystone. The three remaining R-cmp items (u-tail-lift, ACCEPT tape-wipe, R-S
dovetail) all funnel through **R-S** — it pins the global tape layout, which pins the u-tail offset `H` and
the cleanup target. So R-S was attacked first (design), then the one concrete sub-brick the design unblocks
(tail-safe relocation) was built and verified.

**R-S DESIGN — SETTLED (port-8051 consult, this session).** The dovetail must be **base-m-native** for the
compare: materializing α as a unary register is the `2^α` FACT-2 blow-up, dead. So R-S factors as
**[poly-bounded control] glued to [base-m emit→reloc→compare→branch]**:

- **Control (unary, RM-style n≥4 gadgets):** the outer bound `T`, inner stage `s≤T`, the enumerator `E`
  register-bank sim, and `(a,b)=declared_pair(e,s)` extraction are ALL poly-bounded in `T,s` (NOT α) ⟹
  unary blocks + the existing `tm.n≥2`-monotone inc/dec/walk/peek gadgets. Re-express `search_rm`'s
  `outer-T / inner-s≤T` nesting LOGIC as a TM-orchestrator (you CANNOT black-box `search_rm`-as-an-RM: its
  per-stage body now ends in a base-m emit+compare, not an `eq_test`). The enum-sim **re-runs from scratch
  each outer round** — `search_rm`'s standard discipline; poly overhead, **confirmed NOT a dragon**.
- **Per-stage body (DONE, base-m):** recompute `(a,b)` → feed unary `i_a=a+1, i_b=b+1` to the emitter
  (`gap2_emit_*`) → emit `relnum(a,b)` digits → `reloc` → compare vs the **immutable** α-block → on
  `q_reject` advance the dovetail and retry; on `q_accept` → cleanup→origin. Halts iff α is a declared
  relator word-number. Compose to `mm_decides_relnum` via `lemma_tm_h0_iff` ∘ R-S-halts-iff.

**THE LAYOUT — corrected against the VERIFIED u/v frame.** The consult's abstract "u-region right of β" does
NOT map to the built machinery, whose frame is FIXED: `u`=left tape, `v`=right tape, head at the
master/output boundary, `reloc` moves output `v→u`, compare walks output(`u`) vs α(`v`). So the Control Zone
cannot be "to the side" in tape-space — in the u/v model it must be a **high tail** (a digit-offset above the
head's reach), and the per-stage surface must be proven to **carry it untouched**. There is no placement that
avoids a tail-carry: the Control Zone is finite data that must coexist with the working tape through both
emit and compare. The previous instance's choice (**u-high-tail above the master**) is right — `q_clean`'s
deepest left reach is the master separator, below the backup.

**u-TAIL-LIFT — HALF 1 (tail-safe RELOCATION) DONE (`gap2_reloc.rs`, +3 lemmas, crate 1877/0).** Key finding:
`lemma_q_clean` **already carries the tail** (its `t` param: entry `u=m^g·(R(M)+m^{M+1}·t)`, exit
`u=t·m^{g+M+1}`); `lemma_reloc_local` just calls it with `t=0`. And `lemma_dwalk_right_gen` is fully
tail-aware on `u` (`dpile(c.u,blk)` piles onto WHATEVER `c.u` is). So the lift is a clean additive
generalization, no deep re-thread:
- **`lemma_reloc_stamp_transfer_ufloor`** (+ `_contract`) — the stamp+transfer from an arbitrary `u`-floor
  `c.u==u_floor` (was pinned `0`): step-0 stamp lifts `u_floor→u_floor·m+5`, the tailed walk piles output
  above ⟹ `u == dpack(drev(output)) + m^L·5 + m^{L+1}·u_floor`.
- **`lemma_reloc_local_tailed`** — entry `u==copy_u(0,M,g)+m^{g+M+1}·T_u` (master + backup), via
  `q_clean(t=T_u)` then the u-floor transfer ⟹ exit `u==dpack(drev(output)) + m^L·5 + m^{(L+1+g+M+1)}·T_u`,
  `v==w/m`, `q==q_xfer`. `T_u==0` recovers `lemma_reloc_local`. The backup rides to offset `L+1+g+M+1`,
  well above the far-`5` (digit `L`) — so the compare (reach ≤ `L`) is naturally tail-safe.

**u-TAIL-LIFT — HALF 2 (tail-safe COMPARE) = NEXT.** The comparator must carry the same `m^{H}·T_u` tail
(`H = L+1+g+M+1`) on `u` from the parked entry through to `q_accept`/`q_reject`. The compare gadgets pin
`c.u` EXACTLY (e.g. `lemma_cmp_accept_decide`: `c.u == pile_zeros(vk+m·5,g,m)/m`), so a tail is a frame
addition that breaks those preconditions. **Two candidate routes (scope before building):** (a) **re-thread**
each `tm_cmp_*` sub-lemma (gap_cross, match_round, bootstrap, loop, the 5 decide terminals) with a
`+ m^{H}·T_u` u-term — mechanical but ~10-15 lemmas; (b) a **generic u-high-tail frame meta-lemma**: if a run
never pops `u` past digit `H` (head's net-left-excursion-on-`u` < `H` throughout) then `tm_run` is invariant
under `u += m^{H}·T_u` — elegant, reusable for R-C too, but needs a head-excursion bound the current
compose-of-lemmas structure doesn't expose. Lean (b) if the excursion bound is cheap to thread through the
existing fuel-additive composition; else (a). **PROBE (this session, `lemma_cmp_gap_cross`):** the tail
offset **shifts down by the net left-excursion** of each gadget — gap_cross (`g` left-moves) takes a tail at
offset `H` to offset `H−g`, value intact (entry `u=(d_o+m·out_rest)·m^{g-1}` → exit `u=out_rest`; a
`+m^H·T_u` rides to `+m^{H−g}·T_u`). The compare's max `u`-reach is the far-`5` (digit `L`), and the decide
terminals fire `q_accept`/`q_reject` immediately on reading it (no further left pop), so **any tail at offset
`> L` is preserved** — and the relocation lands it at `L+1+g+M+1 ≫ L`. So route (a) is concrete: each
gadget's post-offset = pre-offset − (its net left-excursion), same `+m^{offset}·T_u` frame-arithmetic shape
as the reloc lemmas just built; the final offset (for R-C) is the compare's total net excursion below `H`. **This unblocks: the per-stage surface inside the global frame,
AND (via the same exposed accept config) the ACCEPT tape-wipe.** **DE-RISK 2 (this session,
`lemma_skip0_left`):** the recursive compare PRIMITIVES are **already tail-generic** — `skip0_left`/`_right`
take an *arbitrary* `rest`, and a u-tail absorbs straight into it
(`pile_zeros(low + m^h·T_u, k) = low·m^k + m^{h+k}·T_u`). So the cascade is shallower than "re-thread
everything": the loops need NO change; only the per-gadget *boundary reads* (`rest % m`, `rest / m` at
gap_cross/match_round/decide) need the carry-free atom. **✅ THE ATOM IS BUILT (this session,
`tm_dstring::lemma_pow_high_tail`, crate 1883/0):** `(low + m^h·t)/m^k == low/m^k + m^{h-k}·t` AND
`% m^k == low%m^k` for `k ≤ h, m ≥ 1` — placed LOW in `tm_dstring` (everyone imports it; `gap2_reloc`
imports `tm_cmp_traverse`, so the tailed gadgets in `tm_cmp_*` cannot pull from `gap2_reloc`) so both the
reloc and the cmp cascade consume it. Supporting `lemma_pow_nat_pos`/`lemma_pow_nat_split` added alongside.
**So HALF 2's FOUNDATION is in place** — the next session threads `lemma_pow_high_tail` through the
`tm_cmp_*` gadget boundary reads (loops unchanged), starting at `gap_cross`/`match_round`.

**DE-RISK 3 (this session — HALF 2 is SMALLER than "10-15 lemmas").** `lemma_cmp_gap_cross` is itself
**tail-generic via its `out_rest` (above-frontier) parameter** — a u-tail absorbs into it for free:
`pile_zeros(vk + m·(out_rest + m^{H−g}·T_u), g)/m == [pile_zeros(vk + m·out_rest, g)/m] + m^{H}·T_u`
(verified algebraically: `(vk + m·out_rest')·m^{g-1} = vk·m^{g-1} + out_rest·m^g + m^{H-g}T_u·m^g`). So
calling the EXISTING `lemma_cmp_gap_cross` with `out_rest := out_rest + m^{H−g}·T_u` gives the tailed behavior
with NO new lemma — the tail rides in the high parameter, the frontier digit `d_o` is untouched. Same for
`skip0_left` (the tail rides in `rest`). **Implication:** HALF 2 is largely *instantiating the existing
compare chain with the u-tail living in the high/`out_rest`/`rest` parameters*, plus `lemma_pow_high_tail`
ONLY at the few points a gadget div/mods a value whose tail could reach the scanned cell. The next session
should (1) trace the parked-entry → bootstrap → loop → decide chain confirming the tail stays in the high
parameter throughout (likely true given gap_cross/skip0_left/match_round all treat the above-frontier part
opaquely), (2) re-state the top-level `lemma_reloc_then_compare_{accept,reject}` with the `+m^{H}·T_u` tail
on `u` (`H` = the relocation's `L+1+g+M+1` from HALF 1). This is the genuine remaining u-tail-lift work, and
it now looks like a thin instantiation layer, not a deep re-thread.

**ACCEPT tape-wipe (R-C) prereq, noted:** the accept config IS already computed inside
`lemma_cmp_accept_decide` (`c_acc = apply_quint((q_verify_cmp,5,5,q_accept,R), c_v, m)`, body line ~236) —
only the `ensures` discards it. Exposing it is a cheap strengthening (thread `c_acc` up through
`lemma_cmp_decides_accept` → `lemma_reloc_then_compare_accept`); deferred to R-C since the wipe-to-origin
needs the global-frame accept config (= local + u-tail, i.e. HALF 2).

**NEXT:** u-tail-lift HALF 2 (tail-safe compare, route (a)/(b) per the excursion-bound probe) → then R-S can
embed the per-stage surface in the dovetail. R-S build order: control skeleton (T/s counters + back-edges,
mirror `search_rm`'s nesting) → enum-sim-on-tape + `(a,b)` extraction → wire to emit→reloc→compare→branch →
R-C (cleanup, consumes the exposed accept config) → R-MC (`mm_decides_relnum` via `lemma_tm_h0_iff`) → B-W
(discharge `ceer_realizes`) → drop `axiom_ceer_fp_embedding`.
