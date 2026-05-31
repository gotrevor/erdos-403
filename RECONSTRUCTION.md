# Erdős #403 — proof reconstruction & formalization plan

Lin's and Frankl's 1976 proofs are unpublished/lost (see `HANDOFF.md`), so this is a from-scratch
reconstruction. **Good news: most of the argument reconstructs cleanly; the whole problem reduces to
a single carry-ceiling lemma.** This doc records the math (with proofs where we have them) and the
ordered Lean plan. Build is green; nothing here is formalized yet.

## Notation

- `S : Finset ℕ`, `factSum S = ∑_{a∈S} a!`. Model "distinct factorials" = distinct indices.
- `M := max S`, `a₀ := min S`.
- `v₂ := padicValNat 2`. `s₂ n := (n.digits 2).sum` (binary digit sum / popcount).

## Reduction

`factSum S = 2^m` ⟺ `factSum S` has odd part `1` ⟺ `factSum S = 2^{v₂(factSum S)}`.
So a solution forces **`m = v₂(factSum S)`** AND **`factSum S = 2^m`**. We exploit both: the value
pins `m` near `log₂(M!)` (large), while the valuation `v₂` wants to be small. The collision bounds `M`.

## Lemma A — size sandwich  ✅ (have proof)

For `M = max S ≥ 1`:  `M! ≤ factSum S < 2·M!`.
- Lower: `M! ` is one of the summands.
- Upper: `factSum S ≤ ∑_{a=0}^{M} a!`, and `∑_{a=0}^{M-1} a! ≤ M!` (equality only at `M=2`; for
  `M≥2`, `∑_{a=0}^{M-1} a!/(M-1)! ≤ 2` etc.), so `∑_{a=0}^{M} a! ≤ 2·M!`.

**Consequence:** if `factSum S = 2^m` then `2^m ∈ [M!, 2·M!)`, hence **`log₂(M!) ≤ m < 1+log₂(M!)`**,
i.e. `m = ⌈log₂(M!)⌉`. In particular `m ≥ log₂(M!)`, which for `M ≥ 4` exceeds `M` (e.g. `log₂ 4! ≈
4.585 > 3`) and grows like `M log₂ M`.

## Lemma B — valuation of factorials  ✅ (mathlib + easy)

1. `v₂(n!) = n − s₂(n)`  — mathlib `sub_one_mul_padicValNat_factorial` at `p=2` (`p−1=1`).
   So `v₂(n!) ≤ n − 1` for `n ≥ 1` (since `s₂(n) ≥ 1`), and `v₂(n!) ≤ n` always
   (`padicValNat_factorial_le`).
2. `v₂(n!)` is non-decreasing; `v₂((n+1)!) − v₂(n!) = v₂(n+1)`.
3. **Ties come only in consecutive pairs `{2j, 2j+1}`.** `v₂((2j+1)!) = v₂((2j)!)` (since `2j+1`
   odd ⟹ `v₂(2j+1)=0`), but `v₂((2j+2)!) = v₂((2j+1)!) + v₂(2j+2) = v₂((2j+1)!) + 1 + v₂(j+1) >
   v₂((2j+1)!)`. So no three consecutive factorials share a `v₂`. Values of `v₂(a!)`, `a=1,2,…`:
   `0,1,1,3,3,4,4,7,7,8,8,10,10,…`.

## Lemma C — the generic (unique-minimum) case  ✅ (have proof) — this is the key simplifier

**Claim.** If the minimum of `v₂(a!)` over `a∈S` is attained *uniquely* (at `a₀`), then
`v₂(factSum S) = v₂(a₀!)`.

*Proof.* `factSum S = a₀!·(1 + ∑_{a∈S, a>a₀} a!/a₀!)`. Each `a!/a₀!` (`a>a₀`) has
`v₂ = v₂(a!) − v₂(a₀!) ≥ 1` (strict, by uniqueness), so the inner sum is even and `1 + (even)` is
odd. Hence `v₂(factSum S) = v₂(a₀!) + 0`. ∎

**When does uniqueness fail?** Only when `a₀` is even and `a₀+1 ∈ S` (the bottom is a tied pair
`{2j,2j+1}`), by Lemma B.3.

**Payoff.** In the unique-min case, `m = v₂(factSum S) = v₂(a₀!) ≤ a₀ − 1 ≤ M − 1`. But Lemma A
gives `m ≥ log₂(M!) > M − 1` for `M ≥ 4`. Contradiction. **So every solution with `M ≥ 4` has a
tied pair `{a₀, a₀+1}` at the bottom (`a₀` even, both in `S`).** Unique-min ⟹ `M ≤ 3` (finite check).

## The remaining kernel — bound the carry  ⚠️ (the one real gap)

Everything now hinges on the **tied-pair-at-bottom** case. The pair collapses:
`(2j)! + (2j+1)! = (2j)!·(2j+2) = (2j)!·2·(j+1)`, so `v₂` of the pair `= v₂((2j)!) + 1 + v₂(j+1)` —
the carry. The remaining terms have strictly larger `v₂`, and the question is how far the carry can
cascade as it meets them. Sanity: `{2,3} → 8 = 2³`; `{2,3,5} → 128 = 2⁷`.

**What we need is an explicit ceiling.** Either suffices:
- **(Crude, enough for Tier-1 finiteness):** `v₂(factSum S) ≤ C·M` for an absolute constant `C`.
  Then `log₂(M!) ≤ m ≤ C·M` forces `log₂(M/2) ≲ C`, so `M ≤ 2^{C+1}` — *bounded* ⟹ finitely many
  `S` ⟹ **`erdos_403_finite`.** Conjecturally `C` is small; even a loose `C` closes Tier 1.
- **(Sharp, Lin):** if `2 ∈ S` then `v₂(factSum S) ≤ 254` (an *absolute* bound — the carry cannot
  cascade past 254 once anchored by the low term `2!`). Gives `m ≤ 254 ⟹ M ≤ 57`.

**Two routes to attack the ceiling** (this is the research kernel — and the natural Aristotle race):
1. **`a₀!·K` recursion.** `factSum S = a₀!·K`, `K = 1 + ∑_{a>a₀} a!/a₀!`; `v₂(factSum)=v₂(a₀!)+v₂(K)`.
   In the tied-pair case `K` is even; peel one factor of 2 and recurse on a structurally smaller
   "1 + sum of ascending products," tracking that the recursion depth (hence total carry) is bounded.
2. **Carry-step counting.** Bound the number of cascade steps by the number of distinct `v₂`-levels
   the chain can climb before hitting a level with an odd resident that terminates it; show each step
   adds `O(1)` and the count is `O(M)` (crude) or absolutely bounded when `2∈S` (sharp).

**The easy sub-case `2 ∉ S`** (for finiteness, dispatch separately): if `2∉S` and `factSum=2^m`,
then for evenness `{0,1}⊆S` or `{0,1}∩S=∅`. With `2∉S`, the smallest factorial of index `≥2` present
has odd index or is a lone min (its pair-partner `2` is absent), so Lemma C applies with small `v₂`,
forcing small `m` and hence small `M`. (Spell out the `{0,1}` bookkeeping in Lean.)

## Finite endgame — factorial base  ✅ (clean, decidable)

Factorial number system: every `n` is uniquely `∑_{i≥1} d_i·i!` with `0 ≤ d_i ≤ i`.
**`n` is a sum of distinct factorials (indices ≥1) ⟺ every factorial-base digit `d_i ≤ 1`.**
(Bottom wrinkle: `0!=1!=1`, so `0∈S` bumps the `d_1` digit; handle indices `0,1,2` by hand.)
So once `m ≤ B` is known, "which `2^m` are sums of distinct factorials" is a **per-`m` digit check**
over `m ≤ B` — decidable, ~`B` fast checks, **not** `2^{57}` subset enumeration. This yields the
sharp `m ≤ 7` (and the sibling #404 `3^m` result, `m∈{0,1,2,3,6}`, by the same check at `p=3`).

## Lean formalization plan (ordered)

| # | target | depends on | mathlib / notes |
|---|--------|-----------|-----------------|
| 1 | ✅ **DONE** `factorial_max_le_factSum` (lower) + `factSum_le_two_mul_factorial_max` (upper, **non-strict** `≤ 2·M!` — strict `<` is false at `M∈{1,2}`) + `sum_range_factorial_le` + `two_pow_lt_factorial` | — | `Finset.single_le_sum`, `sum_le_sum_of_subset`, `Finset.sum_range_succ` |
| 2 | ✅ **partial** `padicValNat_two_factorial` (Legendre wrapper) + `_le` + `_mono` DONE. `ties_only_pairs` **TODO** (deferred — needed for step 6, not for 3/4) | B | `sub_one_mul_padicValNat_factorial`, `padicValNat_dvd_iff_le`, `Nat.factorization`-free via dvd |
| 3 | ✅ **DONE** `v2_factSum_of_unique_min : (∀ a∈S, a≠a₀ → v₂(a₀!) < v₂(a!)) → v₂(factSum S) = v₂(a₀!)` | 2 | split off `a₀!` via `Finset.add_sum_erase`; `2^k ∣`/`2^{k+1}∤` sandwich + `Nat.dvd_add_left` |
| 4 | ✅ **DONE** `unique_min_bound : unique-min ∧ factSum=2^m → M ≤ 3` | 1,3 | `m = v₂(a₀!) ≤ a₀ ≤ M` ⟹ `M! ≤ 2^M` ⟹ `M ≤ 3` via `two_pow_lt_factorial` |
| 5 | ✅ **`tied_sharp_ceiling` PROVEN** (reduced to kernel `cascade_two`); ⚠️ **THE GATE (sole `sorry`)** is now `cascade_two : min'=2 ∧ 3∈S ∧ factSum=2^m → m ≤ M+2`, **scoped to `M ≥ 6`** | 2,3 | bottom-pinned to `a₀=2`; `tied_carry_ceiling` (∃B) proven from it |
| 6 | ✅ **DONE** `erdos_403_finite` (modulo step 5) | 1,4,5,ties | `exists_factorial_gt_two_pow` + sandwich + ceiling ⟹ `S ⊆ (range (N+1)).powerset` ⟹ `Set.Finite` |
| 7 | ✅ **DONE (modulo step 5)** `erdos_403_sharp (m ≤ 7)` | 5 | no factorial-base / decide needed: unique-min ⟹ `m ≤ 3` (`sharp_of_unique_min`); tied ⟹ `m ≤ M+2` (kernel) + `four_two_pow_lt_factorial` (`2^{M+2}<M!` for `M≥6`) ⟹ `M ≤ 5` ⟹ `m ≤ 7` |

**Steps 1–4 + ties + step 6 GREEN** (axiom-clean) as of session 2; **steps 5→single-kernel + step 7
DONE as of session 4.** Both headline theorems `erdos_403_finite` *and* `erdos_403_sharp` now reduce
to **exactly one `sorry`: `tied_sharp_ceiling`** (`#print axioms` of both = the standard three +
`sorryAx`). `unique_min_bound` and the whole unique-min half are axiom-clean. Step 4 lands `M ≤ 3`
directly (sharper than the doc) via `v₂(a₀!) ≤ a₀`, sidestepping the `a₀ = 0` edge. The strict upper
sandwich `< 2·M!` was corrected to non-strict `≤ 2·M!` (false at `M∈{1,2}`, e.g. `{0,1}↦2`).

**Session-4 restructure (sorries 2 → 1):** the old free-`B` `tied_carry_ceiling` sorry + the
independent `erdos_403_sharp` sorry were unified. `tied_sharp_ceiling` (tied bottom + `factSum=2^m`
⟹ `m ≤ M+2`, explicit `B=2`) is now the *single* kernel; `tied_carry_ceiling` is proven from it
(witness `2`), and `erdos_403_sharp` is proven from it (tied case) plus `sharp_of_unique_min` (the
unique-min case is unconditional, `m ≤ 3`). The sharp endgame needs **no** factorial-base layer or
`decide` — just the size sandwich `four_two_pow_lt_factorial`. So a proof of the one kernel makes
**both** Erdős #403 (finiteness) and its sharp form `m ≤ 7` unconditional and axiom-clean.

**Session-4 finding — `B=2` is sharp and the constraint is essential.** Exhaustive search: every
power-of-two factorial sum has `m − max'S ≤ 2` (extremal `{2,3,5}↦2⁷`). But the *general* gap
`v₂(factSum S) − max'S` is **unbounded** — `{2ᵗ−2, 2ᵗ−1, 2ᵗ+1}` gives gap `2t−2` (e.g. `{6,7,9}↦2¹³·45`,
gap 4; `{14,15,17}`, gap 6) — so no constant `B` works without `factSum = 2^m`. The carry jump is
governed by *odd-part ratios* of factorials (`oddpart(9!)/oddpart(6!·7!) = 2835/45 = 63 = 2⁶−1`,
giving the +6 jump). This is exactly why it's Lin's hard estimate, and confirms the odd-part-`1`
hypothesis is load-bearing, not cosmetic.

### The actual solution set (enumerated, session 2)
Brute force over indices `0..12` (`tools/`-style check): the **only** solutions are
`m ∈ {0,1,2,3,5,7}`, values `1, 2, 4, 8, 32, 128`. Largest `2⁷ = 128`. Each appears with `min = 0`
and (via the `0!+1! = 2 = 2!` duality) a `min = 2` twin:

| m | value | `min=0` form | `min=2` form |
|---|---|---|---|
| 0 | 1 | `{0}` (`= {1}`) | — (`1 < 2!`) |
| 1 | 2 | `{0,1}` | `{2}` |
| 2 | 4 | `{0,1,2}` | — (no clean twin) |
| 3 | 8 | `{0,1,3}` | `{2,3}` |
| 5 | 32 | `{0,1,3,4}` | `{2,3,4}` |
| 7 | 128 | `{0,1,3,5}` | `{2,3,5}` |

Note `m ∈ {4,6}` have **no** representation (16, 64 aren't sums of distinct factorials). This is
richer than the original handoff (which listed only `2⁷=2!+3!+5!`); `{2,3,4}=32` is a genuine
solution we'd missed. `erdos_403_sharp` is therefore `m ≤ 7`, attained.

### `min'_le_two` ✅ DONE — reduces the kernel bottom to `a₀ ∈ {0,2}`
Proven & axiom-clean: `factSum S = 2^m ⟹ min' S ≤ 2` (because `a₀! ∣ 2^m` forces `a₀!` to be a power
of two). With the tied hypothesis (`a₀` even), the kernel's bottom is now exactly `a₀ ∈ {0, 2}`.

### Bottom-pinning ✅ DONE (session 5) — `tied_sharp_ceiling` proven, kernel is now `cascade_two`
`tied_sharp_ceiling` (the old `sorry`) is **fully proven** by dispatching `a₀ ∈ {0,2}` down to a
single bottom-pinned kernel `cascade_two (min'=2 ∧ 3∈S ∧ factSum=2^m → m ≤ M+2)`:
- **`a₀ = 0 ∧ 2 ∈ S`** dies by parity: `not_eight_dvd_factSum_of_mem_012` (axiom-clean) shows
  `{0,1,2}⊆S ⟹ factSum ≡ 4` or `2 (mod 8) ≠ 0`, so `8 ∤ factSum` and hence `m ≤ 2`.
- **`a₀ = 0 ∧ 2 ∉ S`**: the `0!+1! = 2!` twin surgery `{0,1} ↦ {2}` maps `S` to
  `S' = insert 2 ((S.erase 0).erase 1)`, preserving `factSum` and (as `max' S ≥ 3`) `max'`, landing
  `min' S' = 2`; then `cascade_two` (if `3∈S'`) or `m_le_max_of_unique_min` (if `3∉S'`, unique-min).
- **base `max' S ≤ 2`**: `factSum ≤ 0!+1!+2! = 4 ⟹ m ≤ 2`.

Inside `cascade_two`, the `M = max' S ≤ 5` regime falls to the sandwich (`M! < 2^{M+2}` for `M ≤ 5`
by `decide`), so the **lone `sorry` is scoped to `M ≥ 6`** — the regime where `2^{M+2} < M!` makes
the sandwich too weak and only the odd-part-`1` constraint tames the carry. This `M ≥ 6` cascade is
the irreducible Lin/Frankl estimate. `#print axioms` of `erdos_403_finite`/`erdos_403_sharp` = the
standard three + `sorryAx` (via `cascade_two` only).

### Why the kernel is genuinely hard (the cascade, traced)
The earlier "bound `v₂(K)`" framing was **wrong** (`v₂(K) = m − v₂(a₀!) ≈ m`, circular). The real
content: for `a₀ = 2`, `factSum = 2!+3!+∑_{a≥4} a! = 8 + ∑_{a≥4}a!`; dividing by 8,
`1 + ∑_{a≥4} a!/8 = 2^{m-3}`. Now `a!/8` is **odd** exactly for `a∈{4,5}` (`=3,15`), even for `a≥6`.
So the parity at each level pins which of two consecutive indices may appear, and *recurses one level
up* with the target valuation bumped. The branch tree is finite but intricate:
`{2,3}→8 (stop)`; add `4 → {2,3,4}=32 (stop)`; add `5 → {2,3,5}=128 (stop)`; any higher addition
forces `∑_{a≥6} a!/8 = 4·(odd)`, recursing again — and Lin's analysis shows it always terminates by
`128`. **Termination of this cascade is the irreducible Lin/Frankl kernel** (`tied_carry_ceiling`);
there is no cheap crude bound — `v₂(factSum)` is genuinely unbounded over general tied pairs
(`{2k,2k+1}` gives `v₂ ≈ 2k`), and only the odd-part-`=1` constraint tames it. This is the clean
self-contained target for the Aristotle race: *"the cascade `1 + ∑_{a≥4} a!/8 = 2^{m-3}` has no
solution with `m > 7`."*

## Confidence
- Steps 1–4 + ties + step 6 (the whole **unique-min** half + finiteness skeleton): **DONE** (was ~85%).
- Step 5 crude ceiling ⟹ **Tier-1 finiteness**: ~60% — the carry recursion is elementary but is the
  genuine derivation Lin/Frankl did and never published. **No analytic input expected** (~90% on "no
  hard wall").
- Step 7 sharp `m ≤ 7`: ~50%, contingent on 5 + a factorial-base layer (may need building in mathlib).

## Pointers
KB: `core/projects/erdos-403` (TODO add), [[binomial-thresholds]] (Legendre toolbox + the
formalized-flag footgun), [[erdos-formalization-hunt]] (why #403 was chosen), [[collatz-cryptid]]
(Shen Lin = Busy Beaver, the same person whose memo we're reconstructing).
