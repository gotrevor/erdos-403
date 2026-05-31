# Aristotle race — the `cascade_crux` kernel

**Date:** 2026-05-31. **Branch:** `tier1-finiteness`. **Why:** the sole `sorry`
(`cascade_crux`, `Basic.lean:482`) is Lin's lost 1976 carry-bound estimate. The
literature search (`LITERATURE-FINDINGS.md`) confirmed the proof was never published, so
this is a genuine reconstruction. Independent re-analysis this session reconfirmed the
kernel is **irreducible**: the size sandwich forces the odd-part *lift* to be large
(`lift = bit-length of oddpart(M!) ≈ log₂ M! − v₂(M!)`), so any sub-`log₂ M!` upper bound
on the lift requires the real carry-cancellation argument — native-decide on small `M` and
crude linear bounds do **not** reduce it. So it was handed to the auto-formalizer.

## Submitted projects

| Project UUID | Target | Statement | Angle in prompt |
|---|---|---|---|
| `3b3dcf5b-5a3c-4f01-882a-4232788452b2` | `cascade` | `min'=2 ∧ 3∈S ∧ ∑a!=2^m → m ≤ max'+2` | 2-adic carry cascade |
| `75f16403-b7ba-467b-887d-50f3a05b9e19` | `lin_sharp` | `min'=2 ∧ 3∈S ∧ ∑a!=2^m → m ≤ 7` | carry **and** FNS doubling-transducer |

Both statements are self-contained (mathlib only) and match the repo's `cascade_two`
signature (modulo unfolding `factSum S = ∑ a ∈ S, a !`). Problem files:
`/tmp/erdos403-aristotle/Problem.lean`, `/tmp/erdos403-fns/Problem.lean`.

## Poll / collect

```
aristotle list                                   # fast one-shot (NOT `show` — that's a live TUI)
aristotle download <uuid> --destination /tmp/sol.tar.gz && tar -xzf /tmp/sol.tar.gz -C /tmp/sol
```

## If a proof returns

- A proof of `cascade` ⟹ replace the body of `cascade_two` (`Basic.lean:494`) wholesale and
  delete `cascade_crux` + its `sorry`. (`cascade_two` currently dispatches its `5∈S` branch
  through `cascade_crux`; a direct proof of `m ≤ max'+2` short-circuits all of that.)
- A proof of `lin_sharp` ⟹ even stronger; feed it directly where `erdos_403_sharp` needs the
  tied case, and derive `cascade_two` from it (`m ≤ 7 ≤ max'+2` once `max' ≥ 5`; handle
  `max' ∈ {3,4}` by the existing `M ≤ 5` sandwich branch).
- **Verify before trusting:** rebuild green and `#print axioms erdos_403_finite erdos_403_sharp`
  — must be the standard three (`propext`, `Classical.choice`, `Quot.sound`), no `sorryAx`,
  no new Aristotle-introduced axioms. Aristotle pins Lean v4.28.0; repo is v4.29.1 — re-check
  any lemma names it used still resolve.
- If both fail / time out: this is genuinely Lin's hard estimate. The documented next grind is
  the **doubling-transducer invariant** (RECONSTRUCTION.md, Session-6 note): find the invariant
  on `2^m ↦ 2^(m+1)` FNS-digit evolution that forbids returning to all-digits-`≤1` for odd
  `m ≥ 9`. Do **not** fabricate a carry argument.
