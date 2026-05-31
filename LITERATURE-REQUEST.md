# Literature request — Erdős #403 (sums of distinct factorials that are powers of 2)

**For:** a host session with internet access. **From:** the lean-yolo-box session (firewalled, can
only reach api.anthropic.com). **Goal:** recover the *proof* (or any reconstruction/exposition) of the
finiteness theorem so the Lean formalization in `~/src/erdos-403` can close its last `sorry`.

## The theorem (what we're formalizing)
> **Erdős #403 (Burr–Erdős).** The equation `2^m = a₁! + a₂! + ⋯ + a_k!` with `a₁ < a₂ < ⋯ < a_k`
> has only finitely many solutions. (Sharp: the largest is `2⁷ = 2! + 3! + 5! = 128`.)

Proved independently in **1976 by Shen Lin** (an unpublished **Bell Labs internal memorandum**, title
~ *"On Two Problems of Erdős Concerning Sums of Distinct Factorials"*) and by **Péter Frankl**. **Both
proofs are reportedly lost / never published.** The methods are *elementary* (2-adic valuations,
Legendre's formula `v₂(n!) = n − s₂(n)`), NOT analytic.

## What we need (in priority order)
1. **The actual argument** — any source that *reproduces or sketches* Lin's or Frankl's proof, or gives
   an independent elementary proof of the finiteness / the bound `m ≤ max(aᵢ) + 2`.
2. **The precise 2-adic lemma** (this is exactly where our Lean proof is stuck — see below). Anything
   bounding the 2-adic valuation of a sum of distinct factorials that is a power of two.
3. **Citations / pointers** even without the proof: who has written about this, where Lin's memo is
   referenced, whether Frankl's proof survives anywhere, any thesis/survey that treats it.

## Specific places to look
- **erdosproblems.com/403** — the canonical entry. Copy the full problem text, the "Solved by …"
  attribution, AND every reference/footnote/link it lists. Follow the reference links.
- **Erdős–Graham**, *Old and New Problems and Results in Combinatorial Number Theory* (1980), p. 79
  (the "[ErGr80]" citation) — the paragraph stating this problem and what it cites.
- **The "formal-conjectures" repo** (Google DeepMind / community Lean): search for `403`, "distinct
  factorials", "factorial" — it lists this as solved; see what it cites or whether it has a Lean proof.
- **OEIS** — search "sum of distinct factorials" / "powers of 2 sum of factorials"; relevant sequences
  often cite the source paper.
- **Google Scholar / MathSciNet / zbMATH**: queries —
  `Shen Lin distinct factorials Erdős`, `Frankl sum of distinct factorials powers of two`,
  `"distinct factorials" "power of 2" finite`, `Erdős 403 factorials`.
- **Bell Labs / Shen Lin** — Shen Lin (of Lin–Kernighan TSP fame) was at Bell Labs; the memo may be
  referenced in his bibliography or in TSP-era retrospectives.
- **MathOverflow / math.stackexchange**: "sum of distinct factorials power of two", "Erdős 403".

## The exact lemma we're stuck on (so you can recognize a useful hit)
Our Lean reconstruction reduces the whole problem to ONE inequality. Setup: `S` a finite set of
indices, `factSum S = ∑_{a∈S} a! = 2^m`, `M = max S`. Writing `oddpart(x) = x / 2^{v₂(x)}`:
> **(CRUX)** `v₂( oddpart(M!) + oddpart(factSum(S\{M})) ) ≤ s₂(M) + 2`
> where `s₂` = binary digit-sum, `v₂` = 2-adic valuation.

Equivalently (and how Lin likely phrased it): **for a sum of distinct factorials equal to a power of
two, `m ≤ M + 2`** (the exponent exceeds the top index by at most 2). NOTE: this is *false* without the
power-of-two hypothesis — the family `{2ᵗ−2, 2ᵗ−1, 2ᵗ+1}` gives `v₂(factSum) − M = 2t−2 → ∞`. So the
proof MUST use that the odd part is exactly 1. Any source with a "carry"/valuation argument that
controls how far cancellation can lift `v₂` is the bullseye.

## What to bring back
- Paste full text of erdosproblems.com/403 + its references.
- Any PDF/text of a proof or proof-sketch (Lin, Frankl, or independent). Save PDFs to
  `~/Downloads/erdos403-refs/` and note the paths.
- A short bullet list: "found / not found", with URLs, so the box session can ask for specific pages.
- If a proof is found: the **key lemma and its proof idea** in plain text (the box can't open PDFs from
  arbitrary sources, so a transcription of the crucial 2-adic step is the highest-value payload).

## Context for whoever runs this
Full project state: `~/src/erdos-403/PLAN.md` (the staged plan + crux), `RECONSTRUCTION.md` (strategy),
`HANDOFF-2026-05-31-0530.md` (prior session). The Lean is green with a single `sorry` (`cascade_two`,
the odd-`m` kernel). We are NOT looking for help formalizing — only for the *mathematical argument* to
reconstruct.
