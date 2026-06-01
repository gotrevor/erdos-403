# Erdős #403 — SOLVED (fully sorry-free)

**Date:** 2026-05-31 · **Branch:** `tier1-finiteness`

## Result

Both headline theorems are proven with **no `sorry`**, in `src/Erdos403/Sharp.lean`:

- `Erdos403.erdos_403_finite : {S : Finset ℕ | ∃ m, factSum S = 2^m}.Finite`
- `Erdos403.erdos_403_sharp : factSum S = 2^m → m ≤ 7`  (sharp; `2⁷ = 2!+3!+5!` attained)

`#print axioms` (both): **exactly `[propext, Classical.choice, Quot.sound]` — nothing else.**
No `sorryAx`, **no `native_decide` trust axioms**. The proof is fully **kernel-pure** (passes
`lean4checker`, mathlib-admissible). The original solve (commit `aedfc35`) used `native_decide`;
a later trust-elimination pass (7 → 3 → 2 → 0 axioms, commits `2eadf8e`/`eb0fe97`/`756c62f`)
replaced every `native_decide` with kernel `decide` over a residue fold + a CRT argument. See
`history/HANDOFF-2026-06-01-0133.md` for that journey.

## How — the fixed modulus the literature/prior sessions thought impossible

The whole problem reduces to: **for every `m ≥ 8`, `2^m` is not a sum of distinct factorials.**
In the factorial number system (FNS), "`n` is a sum of distinct factorials (indices ≥ 1)" ⟺
"every digit `factDigit i n = (n / i!) % (i+1)` is `≤ 1`" (`FactBase.factDigit_factSum_le_one`).

**Key fact (verified 3 ways — full period exhaustion, modexp to 4·10⁶, full big-int to 6·10⁴):**
for every `m ≥ 8`, both `2^m` and `2^m − 1` have an FNS digit `≥ 2` at some index `≤ 11`.

Why this is a *fixed-modulus* fact: `factDigit i n` depends only on `n mod (i+1)!`, hence for
`i ≤ 11` only on `n mod 12!`; and `2^m mod 12!` is periodic in `m` with period **1620**
(`12! = 1024 · 467775`, `ord_{467775}(2) = 1620`). So the claim is a finite check over one period
`[10, 1630)` (+ `m = 8, 9`), discharged by a kernel-pure `decide`. The Lean proof (`Sharp.lean`, Phase C):

1. `factDigit_mod` / `factDigit_mod_twelve` — digit `i ≤ 11` depends only on `n mod 12!`.
2. `two_pow_1620_odd` (`2^1620 ≡ 1 mod 467775`, **kernel-pure CRT proof**) → `two_pow_period` →
   `two_pow_drop` → `two_pow_reduce` (any `m ≥ 10` ↦ base window mod 12!).
3. `base_offending`, `base_offending_sub` — the period exhaustion, as a **kernel-pure `decide`**
   over a `List`/`Nat` residue fold (`adv r = (2r) % 12!`, proved equal to the true residue by
   `res_pow`); `decide` reduces `checkAll 1620 1024 = true` in ~3s without `native_decide`.
4. `two_pow_offending`, `two_pow_sub_one_offending` → `factSum_ne_of_ge_eight` → the headline theorems.

## Why the prior "no fixed modulus" belief was wrong

`RECONSTRUCTION.md` (Session 6) asserted the offending index grows like `~log m/log log m` and that
"no fixed modulus / finite digit-set closes the odd case." That was a **heuristic extrapolation**: a
random-digit model gives `P(all digits ≤ K) ≈ 2^K/(K+1)!`, predicting a first survivor past index 11
near `m ≈ 12!/2^11 ≈ 234 000`. The prior search only reached index 11 (at `m = 223`) and trusted the
heuristic. But `2^m`'s FNS digits are **not** random — the period-1620 structure happens to cover
every residue with an offending digit at index `≤ 11`. Direct search to `m = 4·10⁶` finds **zero**
survivors past index 11. The general-tied-pair carry *is* unbounded (`{2ᵗ−2,2ᵗ−1,2ᵗ+1}`), but that
never implied the **power-of-two** case needs an unbounded modulus — the two were conflated.

## What changed in the repo

- `Sharp.lean`: added Phase C (the fixed-modulus kill) + the canonical `erdos_403_finite` /
  `erdos_403_sharp` (FNS route).
- `Basic.lean`: **deleted** the contaminated carry chain that carried the `sorry`
  (`cascade_crux`, `cascade_two`, `tied_sharp_ceiling`, `tied_carry_ceiling`, `carry_ceiling`, and the
  old Basic `erdos_403_finite`/`erdos_403_sharp`). Kept the axiom-clean helpers (descent, lift,
  size sandwich, unique-min, `min'_le_two`, `factDigit` infra, `witness`, `exists_factorial_gt_two_pow`,
  `sharp_of_unique_min`). A few of those are now unused; some `Step 5/6` comments are now stale (a
  comment-cleanup pass is the only remaining tidy-up — the math is done).

## Provenance / honesty

The finite checks are independently confirmed by `tools`-style Python (`/tmp/fns*.py` during the
session): the complete solution list, the period 1620, the index-11 cap for both `2^m` and `2^m−1`.
The headline theorems are sorry-free and depend on **only the standard three axioms**
(`propext`, `Classical.choice`, `Quot.sound`) — no `native_decide`, no compiler-trust axiom.
