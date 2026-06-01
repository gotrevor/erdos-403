# Erdős #403 — formalization handoff

> **✅ SOLVED 2026-05-31 (commit `aedfc35`). Fully sorry-free.** Both `erdos_403_finite` and
> `erdos_403_sharp` (`m ≤ 7`) are proven in `Sharp.lean`. The lost Lin/Frankl carry estimate was
> **never needed** — a fixed modulus `12!` (FNS digits, period 1620) closes it; the prior
> "no fixed modulus" belief was a heuristic extrapolation error. **Read `SOLVED.md`** for the full
> story. The carry-route notes below are historical. Only remaining: host `git push` (no egress in
> the box) + optional stale-comment cleanup in `Basic.lean`.

---

**Repo**: `~/src/erdos-403/` · **Started**: 2026-05-30 · **mathlib**: v4.29.1 (cache-shared with
`binomial-thresholds`/`sum-product`, instant `lake exe cache get`). **Build**: green (8248 jobs),
witness verified.

**Session 2 (2026-05-31) — major progress.** Steps 1–4 + ties + finiteness assembly (step 6) all
landed and axiom-clean. **`erdos_403_finite` is fully proven modulo a single `sorry`,
`tied_carry_ceiling`** — the bounded-carry kernel. `#print axioms erdos_403_finite` = standard three
+ `sorryAx`. Remaining sorries: `tied_carry_ceiling` (the gate, §5) and `erdos_403_sharp` (§7).
See `RECONSTRUCTION.md` for the full ordered status + the "`v₂(K)` bounded" next-attack reduction.

## The problem ([ErGr80, p.79], Burr–Erdős)

`2^m = a₁! + ⋯ + aₖ!`, `a₁ < ⋯ < aₖ`, has only finitely many solutions. Largest: `2⁷ = 2!+3!+5!`.

## ⚠️ The original proofs are LOST — this is a reconstruction, not a transcription

- **[Li76] = Shen Lin**, "On Two Problems of Erdős Concerning Sums of Distinct Factorials,"
  **Bell Labs internal memorandum, 1976, unpublished.** (Yes — *that* Shen Lin: Busy-Beaver
  Lin–Rado, Lin–Kernighan TSP. Nice [[collatz-cryptid]] / BB resonance.) Citation pinned via the
  bib of Grossman–Luca, *J. Number Theory* 93 (2002). Frankl's independent 1976 proof is *also*
  unpublished. Not in Guy's UPINT B44, not on MO/SE, erdosproblems forum thread #403 has 0 comments.
- **Consequence:** we must **re-derive** the bounded-carry estimate. Upside: genuine reconstruction
  (more interesting + better blog fodder than transcription); downside: the crux lemma is on us.
- Verified elementary — **no PNT / no sieve / no Baker**. (Baker's method only enters the *modern*
  binary-recurrence generalizations, Grossman–Luca; the bare `2^m`/`3^m` result does not need it.)

## Statements (src/Erdos403/Basic.lean)

- `factSum (S : Finset ℕ) : ℕ := ∑ a ∈ S, a !` — sum of distinct factorials (indices = `Finset`,
  distinctness automatic; `0!=1!=1` so `{0,1}↦2`).
- `witness : factSum {2,3,5} = 2^7` — ✅ proven (`native_decide`; `decide` gets stuck on
  `Finset.sum` through `Quot`).
- `erdos_403_finite : {S | ∃ m, factSum S = 2^m}.Finite` — **Tier 1**, *exactly what #403 asks*.
- `erdos_403_sharp : factSum S = 2^m → m ≤ 7` — **Tier 2**, the sharp "largest is 2⁷".

## Proof architecture (reconstructed)

Engine = Legendre at `p=2`: **`v₂(n!) = n − s₂(n)`** (mathlib `sub_one_mul_padicValNat_factorial`;
`padicValNat_factorial_le : v_p(n!) ≤ n`). Three moves:
1. **Size sandwich**: for `aₖ ≥ 1`, `∑_{j≤aₖ} j! < 2·aₖ!`, so `aₖ! ≤ 2^m < 2·aₖ!` ⟹ `m ≈ log₂(aₖ!) ≈ aₖ log₂ aₖ` (large).
2. **Valuation ceiling**: `m = v₂(S)`. Factorials have gappy, mostly-distinct 2-adic valuations
   (ties only in pairs `{2j,2j+1}`). Generic (unique-min) case ⟹ `v₂(S) = min v₂(aᵢ!)` = small.
   Tension (large vs small) bounds `aₖ` ⟹ **finiteness**.
3. **Bounded carry (THE crux to reconstruct)**: ties `{2j,2j+1}` carry (`2!+3!=8` bumps `v₂` 1→3)
   and can chain, but only boundedly — Lin's max is `2²⁵⁴` for sums containing `2!`. Need an
   explicit ceiling lemma `v₂(S) ≤ (explicit bound)`.

**Finite endgame is tractable** (corrects the "2⁵⁷ subsets" worry): a sum of distinct factorials is
exactly a **factorial-base numeral with all digits ≤ 1**. So given `m ≤ B`, checking which `2^m` are
such sums is a per-`m` factorial-base digit check (~`B` fast/decidable checks), NOT subset
enumeration. (Wrinkle: `0!=1!` makes the bottom digit slightly non-standard — handle by hand.)

## Verified facts (by an agent, exact bigint enumeration)
- `v₂(n!) = n − s₂(n)` (n=1..11). Valuations `1!..`: `0,1,1,3,3,4,4,7,7,8,8,10,10,…`.
- `max v₂(subset-sum of {1!..N!})` for N=2..15: `1,3,5,7,7,8,10,13,13,13,13,15,15,18` — climbs then
  **plateaus** (the bounded-carry signature); global sup (with `2!` present) = **254**.
- `3^m = ∑ distinct aᵢ!` has exactly `m=0,1,2,3,6` (= `1!`, `1!+2!`, `1!+2!+3!`, `1!+2!+4!`,
  `1!+2!+3!+6!`). [See sibling problem #404 — a cheap follow-on once the machinery exists.]

## Plan / next steps
1. ✅ **Tier 1 skeleton DONE** — size sandwich, Legendre engine, unique-min half, ties dichotomy,
   and the `.Finite` assembly are all green/axiom-clean. **Only `tied_carry_ceiling` remains** to
   close #403. Attack it via the `v₂(K)` reduction in `RECONSTRUCTION.md` (bound `v₂(factSum/a₀!)`
   absolutely; crude `B` suffices for finiteness). This is the Aristotle-race target.
2. **Tier 2** (`m ≤ 7`, `erdos_403_sharp`): the factorial-base digit check over `m ≤ B`.
3. **#404 / `3^m`** as a follow-on (same engine, `p=3`, tiny finite check).

## Confidence (revised after the gate)
Tier 1 ~60%, Tier 2 ~45%, hard-wall risk ~10% (danger is tedium/reconstruction, not missing mathlib).
The bounded-carry lemma is the swing factor — being unpublished, it's a real derivation, not a port.
