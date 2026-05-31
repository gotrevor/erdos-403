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
| 1 | `factSum_lt_two_mul_factorial : 1 ≤ M → factSum S < 2 * M !` + lower `M! ≤ factSum S` | — | `Finset.sum_le_sum`, `Nat.factorial`; `max'`/`min'` for `M`,`a₀` |
| 2 | `v2_factorial : v₂ (n !) = n - s₂ n` wrapper + monotone + `ties_only_pairs` | B | `sub_one_mul_padicValNat_factorial`, `Nat.digits` |
| 3 | `v2_factSum_of_unique_min : (∀ a∈S, a≠a₀ → v₂(a₀!) < v₂(a!)) → v₂(factSum S) = v₂(a₀!)` | 2 | `padicValNat` of sum; factor `a₀!`; parity of the cofactor |
| 4 | `unique_min_bound : unique-min ∧ factSum=2^m → M ≤ 3` (then `decide` the ≤3 cases) | 1,3 | combine sandwich + Lemma C |
| 5 | **carry ceiling** `factSum=2^m → m ≤ B` (B crude for finiteness) | 2,3 | ⚠️ the research kernel above |
| 6 | `erdos_403_finite` | 1,4,5 | `M` bounded ⟹ `S ⊆ range (N+1)` ⟹ `Set.Finite` |
| 7 | factorial-base digit criterion + endgame `decide` → `erdos_403_sharp (m ≤ 7)` | 5 | factorial base may need building; small finite check |

Steps 1–4 are GREEN and should land first (they already cut the problem to `M ≤ 3` ∪ tied-pair).
Step 5 is the gate; steps 6–7 follow quickly once `B` exists.

## Confidence
- Steps 1–4 (and thus the whole **unique-min** half): ~85%, routine.
- Step 5 crude ceiling ⟹ **Tier-1 finiteness**: ~60% — the carry recursion is elementary but is the
  genuine derivation Lin/Frankl did and never published. **No analytic input expected** (~90% on "no
  hard wall").
- Step 7 sharp `m ≤ 7`: ~50%, contingent on 5 + a factorial-base layer (may need building in mathlib).

## Pointers
KB: `core/projects/erdos-403` (TODO add), [[binomial-thresholds]] (Legendre toolbox + the
formalized-flag footgun), [[erdos-formalization-hunt]] (why #403 was chosen), [[collatz-cryptid]]
(Shen Lin = Busy Beaver, the same person whose memo we're reconstructing).
