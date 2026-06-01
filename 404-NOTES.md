# Erdős #404 — investigation notes 🔢

**Status:** OPEN (not started). Sibling of #403; shares this repo's FNS/Legendre engine.
**Date:** 2026-05-31 · captured from a planning session, not yet a formalization target.

This is a scratch note, not a result. It records the structure of [Erdős #404](https://www.erdosproblems.com/404),
why it is the natural next-door problem to the #403 solve in this repo, and which sub-pieces look
ripe. Confidence levels are explicit and mine; treat them as bets, not facts.

---

## The problem (as stated on erdosproblems.com/404)

For integers `a ≥ 1` and primes `p`: is there a finite upper bound on those `k` such that there
exist `a = a₁ < a₂ < ⋯ < aₙ` with

> `pᵏ | (a₁! + ⋯ + aₙ!)` ?

Let `f(a,p)` be the greatest such `k`. Three questions:

1. **For which `(a,p)` is `f(a,p)` finite?**
2. **How does `f(a,p)` behave?** (asymptotics in `a`, in `p`)
3. **Is there a prime `p` and an infinite sequence `a₁ < a₂ < ⋯` such that, with `p^{m_k}` the
   highest power of `p` dividing `∑_{i≤k} aᵢ!`, we have `m_k → ∞`?**

Reference: [ErGr80, p.79]. The page notes: see also #403; **Lin [Li76] showed `f(2,2) ≤ 254`.**

### The footnote on the #403 page (the useful clue)

> *"In fact Lin showed that the largest power of 2 which can divide a sum of distinct factorials
> containing 2 is `2²⁵⁴`, and that there are only 5 solutions to `3^m = a₁! + ⋯ + aₖ!`
> (when `m = 0,1,2,3,6`)."*

Two facts, both from Lin's 1976 memo (titled *"On **Two** Problems of Erdős Concerning Sums of
Distinct Factorials"* — the two problems are #403 and #404):

- **`f(2,2) = 254` exactly, and it is *attained*.** The page understates it as `≤ 254`; the footnote
  says the largest power *is* `2²⁵⁴`. So the sup is achieved by a concrete extremal set, and there
  is a hard wall at digit 254.
- **`3^m = ∑ aᵢ!` has exactly 5 solutions**, `m ∈ {0,1,2,3,6}`. This is the #403-analog for `p = 3`.
  Satisfying to check:
  - `3¹ = 1!+2!`
  - `3² = 1!+2!+3!`
  - `3³ = 1!+2!+4!`  (`1+2+24`)
  - `3⁶ = 1!+2!+3!+6!`  (`729 = 720+9`)

So the entire literature on #404 is that one unpublished Bell Labs memo (Shen Lin, 1976 — the
Busy-Beaver / Lin–Kernighan one), plus the Erdős–Graham problem book. A 2026 web sweep turned up no
modern treatment; searches collide with the unrelated *distinct residues of factorials* problem.
Bloom's "OPEN, no progress" is accurate.

---

## Structural reduction (same engine as #403)

Fix `a, p`. Every admissible sum factors out the smallest factorial:

```
∑ aᵢ! = a! · (1 + ∑_{i≥2} (a+1)(a+2)⋯aᵢ) = a! · M
```

so `f(a,p) = v_p(a!) + sup_S v_p(M)`, where `M = 1 + (integers, each a product of a run of
consecutive integers above a)`. The smallest factorial leaves a **forced unit "1"**; divisibility
means cancelling it digit-by-digit in base `p`.

The engine is **identical to this repo's #403 machinery**: Legendre `v_p(n!) = (n − s_p(n))/(p−1)`
and the factorial-number-system digit `factDigit i n = (n / i!) % (i+1)` (`src/Erdos403/FactBase.lean`,
`src/Erdos403/Basic.lean`). To zero the lowest surviving base-`p` digit of a partial sum (sitting at
position `= ` current valuation `m`), you must add a factorial with `v_p(aᵢ!) = m` **exactly** —
because `aᵢ! = pᵐ·u` (`u` a unit) touches digit `m` and above, nothing below. You climb a
**carry tower**, one digit at a time.

### Why #404 is harder than #403 (confidence ~80%)

#403 fixed a *clean target* (`2^m`), so it reduced to "is `2^m mod 12!` ever a sum of distinct
factorials" — a **fixed modulus** `12!` + a period-1620 `decide`. Finite check wins.

#404 has **no clean target**. `f(a,p) < ∞` is a statement over an *unbounded* set of arbitrarily
large factorials, each with arbitrarily large valuation, so a single-period argument cannot close it
directly. The constraint "keep digits `0..k` all zero *while* reaching digit `k`" is **global**, not
local. That is why Lin had to *compute* `254` rather than write a formula, and why no fixed modulus
cracks it the way `12!` cracked #403.

---

## The key observation: the two ends of #404 are one question 🔑

The opening question (Q1, finiteness) and the closing question (Q3, infinite climb) are the same
question viewed from two ends. The **necessary direction is airtight** (confidence ~97%):

Every partial sum `S_k = ∑_{i≤k} aᵢ!` of a Q3 sequence has smallest element `a₁`, so
`{a₁,…,a_k}` is **exactly an admissible set in the definition of `f(a₁,p)`.** Therefore

```
m_k = v_p(S_k) ≤ f(a₁, p)   for all k.
```

**If `f(a₁,p) < ∞`, the climb is capped — `m_k` cannot diverge.** Consequences:

- Lin's `f(2,2) = 254` directly says **no 2-adic infinite climb can start at `a₁ = 2`**: every such
  sequence has `m_k ≤ 254` forever.
- **Q3 (infinite climb for `p`) requires `f(a,p) = ∞` for some starting `a`.** If `f(a,p) < ∞`
  always — which `254` and Erdős's framing both suggest — then **no infinite climb exists, for any
  prime.**

### The one gap: the converse

`f(a,p) = ∞  ⟹  a single infinite climbing sequence` is **not** immediate. High-valuation witness
sets at different `K` need not nest, and Q3 only lets you *append larger* factorials (which touch
higher digits only). So literal-Q3 may be formally a hair stronger than "`∃(a,p): f(a,p)=∞`." The
necessary direction (above) is the one that matters for reading the `254`, and it is clean. Pinning
the converse (a greedy/diagonal construction, or a proof it can fail) is itself a small open sub-question.

---

## Tractability ranking (my bets)

| Question | Read | Confidence |
|---|---|---|
| `f(a,p)` finite for each **fixed** `(a,p)` | Likely true, **attackable**. Mechanism: at valuation level `ℓ` only finitely many `n` have `v_p(n!) = ℓ` (a block of length ≤ `p`), so only a bounded set of available unit residues `{(n!/p^ℓ) mod p}` can cancel each digit. If at some level the *required* cancelling residue is never available, valuation can't climb past it → finite, with a pin-able bound. | 65% provable, bounded effort |
| Behavior/asymptotics of `f(a,p)` | Soft, fuzzy. No conjecture even *stated*. `254` is an ugly computer-found number → no clean formula expected. | open, no handle |
| Infinite climb `m_k → ∞` for some `p` | The deep heart. Equivalent (necessary dir.) to `f = ∞` somewhere; I bet **never** (~75%), i.e. `f` always finite. | really hard |

**Headline:** #404 is "really hard" only in its general/asymptotic form. The **finiteness backbone is
tractable and badly under-computed**, and the footnote shows the two end-questions are one.

---

## Reframing Q3 (the prettiest lens, ~90% right)

Since `v_p(n!) → ∞`, *any* infinite sum of distinct factorials **converges in `ℤ_p`**. So Q3 is exactly:

> Is there a prime `p` and distinct `a₁ < a₂ < ⋯` with `∑_{i=1}^∞ aᵢ! = 0` in `ℤ_p`?

A p-adic "factorial-base representation of zero" via an infinite index set. The residue you must hit
at each level is determined by *all prior choices* (self-referential), which is why naive greedy
dead-ends and why it is open rather than secretly easy.

---

## Concrete investigation targets

1. **Reproduce Lin's `f(2,2) = 254`** with a p-adic carry search (digit-by-digit greedy + backtrack
   over which factorials to include, maximizing `v₂` of the partial sum). Validates the tool; would
   be the only public reproduction. Sandbox script, not Lean.
2. **Tabulate `f(a,p)`** for small `a,p` — `f(1,2)`, `f(3,2)`, `f(2,3)`, `f(2,5)`, … These values are
   **nowhere published.** Pure new data; a legitimate comment to add to the #404 page.
3. **Lean: prove `f(a,p) < ∞` for fixed `(a,p)`** via residue-saturation (the available unit
   `(n!/p^{v_p}) mod p` runs out at some level — a Wilson-quotient characterization). `p = 2` is
   cleanest: the odd part mod 2 is always 1, so it is pure carry combinatorics. Finiteness is the
   theorem; the exact `254` is a `decide`/computation on top. **New beyond Lin**, and squarely in
   this repo's `Basic.lean` / Legendre wheelhouse.

### Caution carried over from #403

Do not trust "`f` is bounded" or "the climb can't continue" until the search has **computed past the
threshold** — this is exactly the `heuristic-negative-needs-compute-past-threshold` lesson that solved
#403 (the "no fixed modulus" belief was a heuristic-extrapolation error). `254` is the warning that
"finite" can be large and irregular with no obvious cap. Reproduce and extend the computation *first*.
