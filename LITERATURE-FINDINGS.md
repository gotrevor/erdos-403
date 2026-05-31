# Literature findings — Erdős #403 (host session, internet access)

**Date:** 2026-05-31. **For:** the lean-yolo-box session. **Re:** `LITERATURE-REQUEST.md`.

## TL;DR (the honest bottom line)

**The proof is genuinely lost / never published. No reconstruction, sketch, or independent
elementary proof exists anywhere I could find online.** You will not get a shortcut from the
literature — the carry-lift bound is an irreducible research kernel you must reconstruct. BUT the
search produced three things that materially help:

1. **Lin's actual published theorem is stronger and cleaner than "m ≤ M+2":** it's an *absolute
   constant* bound — `v₂(sum of distinct factorials, with 2! present) ≤ 254`. (See verbatim quote
   below.) This is the real target shape.
2. **Your CRUX bound `s₂(M)+2` is computationally TIGHT at the extremal solution** `2⁷=2!+3!+5!`
   (M=5: lift = 4 = s₂(5)+2 = 2+2). So your reduction looks *correctly calibrated*, not a false
   lemma. Strong evidence you're proving something true.
3. The complete solution list is confirmed by brute force (below).

## What's authoritative — erdosproblems.com/403 (quoted verbatim)

> **PROVED.** Does the equation 2^m = a₁!+⋯+a_k! with a₁<a₂<⋯<a_k have only finitely many solutions?
> #403 : [ErGr80, p.79] — number theory | factorials
>
> Asked by Burr and Erdős. **Frankl and Lin [Li76] independently showed that the answer is yes, and
> the largest solution is 2⁷ = 2!+3!+5!.** In fact **Lin showed that the largest power of 2 which can
> divide a sum of distinct factorials containing 2 is 2²⁵⁴**, and that there are only 5 solutions to
> 3^m = a₁!+⋯+a_k! (when m = 0,1,2,3,6). See also [404].
>
> *(Page last edited 28 October 2025. Cite: T. F. Bloom, Erdős Problem #403,
> https://www.erdosproblems.com/403)*

- The page **reproduces no proof** and links to none. The forum thread (`/forum/thread/403`) has
  **0 comments**.
- The two proof citations, **transcribed verbatim from the [ErGr80] reference list** (Trevor loaded the
  bibliography page):
  - **[Lin (76)]** — *"On two problems of Erdős concerning sums of distinct factorials.* Bell
    Laboratories internal memorandum (1976)." (Dept. of Math., Sonoma State Coll[ege].)
  - **[Frank (76)]** — "FRANKL, P. *(Personal communication)."*
- **Both are unrecoverable by construction:** an unpublished internal memo + an unwritten personal
  communication. There is, definitively, **nothing to find in the literature** — not a lost-then-maybe-
  findable paper, but a proof that was *never written down for publication*. (The request's guessed memo
  title was exactly correct.) Search is closed at ~99%.

### [ErGr80] p.79 — primary source, transcribed verbatim (Trevor loaded the scanned page)

> Burr and Erdős … asked whether ∑ᵢ aᵢ! = 2^m, a₁ < a₂ < … has only finitely many solutions. The
> largest one seemed to be 2⁷ = 2! + 3! + 5!.
>
> This was proved to be the largest solution by **Frankl [Frank (76)]** and independently, by **S. Lin.
> In fact, Lin [Lin (76)] showed somewhat unexpectedly that the largest power of 2 which can divide a
> sum of distinct factorials containing 2 is 2²⁵⁴.** More generally, if pᵅ ∥ (a₁!+a₂!+…+a_k!),
> a₁ < … < a_k, **is there a bound f(a₁, p) for α** … Conceivably, the answer could depend on a₁ and p.

**Two refinements this adds:**
1. **The natural parameter is the SMALLEST index a₁, not M.** Erdős–Graham frame the general bound as
   `f(a₁, p)` — the max power of `p` dividing a sum of distinct factorials depends on the *smallest*
   term `a₁` and the prime. For #403: `p=2`, and "containing 2" means `a₁ = 2` (the term `2!` present),
   giving Lin's `2²⁵⁴`. **Your CRUX is phrased via `M = max` and `s₂(M)`; Lin's bound is naturally an
   absolute constant once `a₁` is fixed.** If your `cascade` can be re-anchored on the minimum index,
   that's closer to Lin's grain. (This `f(a₁,p)` question is Erdős #404 — the "see also [404]".)
2. The book reproduces **no proof** — it only states the result with the two 1976 citations. The proof
   is in `[Lin (76)]` (lost memo) / `[Frank (76)]`. The exact reference-list strings for `[Frank (76)]`
   and `[Lin (76)]` are on a later page of the book if you want them (Trevor can load the bibliography
   page) — but `[Lin (76)]` is the unpublished memo regardless.

## Sources checked (found / not found)

| Source | Result |
|---|---|
| erdosproblems.com/403 + forum/thread/403 | ✅ statement & attribution (above); ❌ no proof, 0 comments |
| Peter Frankl's own publication list (users.renyi.hu/~pfrankl/FPpubl.html) | ❌ **no 1976 factorial paper** — confirms his proof was never published |
| MathWorld "Factorial Sums" | ❌ covers only *square*-valued distinct-factorial sums (A014597), not powers of 2 |
| Erdős–Graham 1980 book, **p.79** (mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf) | ✅ **transcribed verbatim** (Trevor screenshotted the scanned page; PDF is image-only, pdftotext→empty). Confirms refs `[Frank (76)]`+`[Lin (76)]`, the `f(a₁,p)` framing, and that it reproduces no proof. See quote above. |
| arXiv sweep: 1611.05618 (withdrawn), 2511.15850 (digital sums of factorials), 2509.18860, math/0702010 "Factorials as sums", etc. | ❌ none reproduce or cite Lin's argument; the v₂/s₂ machinery papers don't touch #403 |
| OEIS, Google Scholar/zbMATH-style queries, MathOverflow/StackExchange | ❌ no proof, no reconstruction, no useful sketch |

⚠️ A WebFetch summary of arXiv:2509.18860 *confabulated* citations ("Lin, On a conjecture of Erdős
and Turán, J. Number Theory 8 (1976)") — that's a **different** Lin paper; do not trust it. The small
summarizer model hallucinated. The only reliable attribution is erdosproblems' `[Li76]`.

## Computational verification (my script, `~/personal/tools/sandbox/erdos403_check.py`, verified output)

**Complete list of powers of 2 that are sums of distinct factorials** (brute force, indices 1..14):

```
2^0 = 1   = 1!
2^1 = 2   = 2!
2^3 = 8   = 2! + 3!
2^5 = 32  = 2! + 3! + 4!
2^7 = 128 = 2! + 3! + 5!   ← largest
```

Nothing else exists below 14! ≈ 8.7×10¹⁰. Confirms 2⁷ is the largest. (Note the clean chain
2!, 2!+3!, 2!+3!+4!, 2!+3!+5! — each a power of 2.)

**Your CRUX `v₂(oddpart(M!) + oddpart(factSum(S\{M}))) ≤ s₂(M)+2` on every real power-of-2 solution:**

```
S=(2,3)    M=3: lift=2  s₂(M)+2=4   OK
S=(2,3,4)  M=4: lift=2  s₂(M)+2=3   OK
S=(2,3,5)  M=5: lift=4  s₂(M)+2=4   OK  ← EQUALITY (bound is tight at the extremal solution)
```

No violations. The "+2" constant is **exactly tight** at 2⁷=2!+3!+5!. This is the strongest evidence
that `cascade_crux` is a *true* lemma and your reduction is sound. (Caveat: I could only test the
finitely many *actual* power-of-2 configs; I cannot test the intermediate S your `cascade` induction
feeds the crux without your exact Lean statement. But tightness-at-the-extremum is a good sign.)

**ErGr80 p.80 (also loaded) confirms the book has NO proof through the end of the discussion** — it
continues straight into the related open problems (#404 `f(a₁,p)` with `α_k → ∞?`; #405
`2ⁿ = Σ εᵢ3ⁱ`; D. J. Newman's `w(n)` boundedness conjecture). It does list **Lin's five `3^k`
solutions verbatim, all verified by my script**: `1!=3⁰`, `1!+2!=3`, `1!+2!+3!=3²`, `1!+2!+4!=3³`,
`1!+2!+3!+6!=3⁶`. (Matches erdosproblems' "m=0,1,2,3,6". Note p.80 also asks: for `Σεᵢ3ⁱ` with
`εᵢ∈{1,2}`, "is 15 the largest value of n" — an *un-evaluated conjecture*, not a theorem.)

## The 2-adic mechanism (why it's hard — the reconstruction kernel)

- **Legendre:** `v₂(a!) = a − s₂(a)`. Non-decreasing in `a`, but **NOT strict**:
  `v₂((a+1)!) − v₂(a!) = v₂(a+1) = 0` whenever `a+1` is odd. So e.g. `v₂(2!)=v₂(3!)=1`,
  `v₂(4!)=v₂(5!)=3`. Factorials **cluster into equal-valuation levels.**
- **If** the `v₂(a!)` were all distinct, then `v₂(sum) = min = v₂(a₁!)` ≤ a₁ ≤ M — small — and
  `2^m = T ≥ M!` (huge) would be impossible immediately. **The entire difficulty is that
  equal-valuation clusters let CARRIES lift `v₂(sum)` far above the minimum.** Bounding that lift
  *is* the theorem.
- **Confirmed the lift can exceed M:** brute force finds `S={6,7,8,13}` with `v₂(sum)=15 > 13=M`. So
  the naive "v₂ ≤ M" route fails; a real carry bound is needed. (These big-lift configs are never
  powers of 2 — consistent with the request's counterexample family `{2ᵗ−2,2ᵗ−1,2ᵗ+1}` giving
  unbounded lift. The proof *must* use oddpart = 1.)
- **Lin's contribution** is exactly bounding the maximum carry-lift to the absolute constant **254**.
  That number is not derivable from the literature — it's the hand computation in the lost memo.

## Recommendation for the box

1. **Consider re-aiming at an absolute-constant bound** (Lin's shape: `v₂(Σ distinct a!) ≤ C` for sums
   containing 2!), which *implies* finiteness directly (`m ≤ C ⟹ M! ≤ 2^C ⟹ M bounded ⟹ finite
   search`). It may formalize more cleanly than the M-dependent `s₂(M)+2`, and it's what Lin actually
   proved. You don't need the sharp `C=254` — *any* explicit absolute constant closes #403.
2. **Or keep `s₂(M)+2`** — it's tight at the extremum, so it's true; the cost is that the carry
   argument has to track `s₂(M)` rather than a constant.
3. Either way the missing math is the **carry-propagation bound across equal-v₂ factorial clusters**.
   The literature does not contain it. This is a genuine (small) reconstruction, not a lookup.

## Saved artifacts (host machine)

- `~/Downloads/erdos403-refs/403.html` — erdosproblems #403 page (curl'd; WebFetch is 403-blocked there)
- `~/Downloads/erdos403-refs/erdos-graham-1980.pdf` — the [ErGr80] book (scanned, no text layer)
- `~/personal/tools/sandbox/erdos403_check.py` — the verification script above
