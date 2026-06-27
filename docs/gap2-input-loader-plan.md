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
