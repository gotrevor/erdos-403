import Mathlib

/-!
# The factorial number system (for Erdős #403)

The unique mixed-radix representation `n = ∑_{i≥1} dᵢ·i!` with `0 ≤ dᵢ ≤ i`, where
`dᵢ = (n / i!) mod (i+1)`. A number is a **sum of distinct factorials** (indices `≥ 1`) iff every
digit is `≤ 1`. This is the engine for the sharp form `m ≤ 7` of #403: the question becomes a
digit condition on `2^m`.

This file builds the infrastructure (Phase A of `PLAN.md`):
* `factDigit` and its bound,
* the reconstruction `n = ∑ dᵢ·i!` (telescoping div/mod),
* (later) the distinct-factorials criterion and decidability.
-/

namespace Erdos403

open Finset
open scoped Nat

/-- The `i`-th factorial-base digit of `n`: `dᵢ(n) = ⌊n / i!⌋ mod (i+1)`. -/
def factDigit (i n : ℕ) : ℕ := (n / i !) % (i + 1)

/-- Digits are bounded: `dᵢ(n) ≤ i`. -/
theorem factDigit_le (i n : ℕ) : factDigit i n ≤ i := by
  have : factDigit i n < i + 1 := Nat.mod_lt _ (Nat.succ_pos i)
  omega

/-- **Reconstruction with remainder.** For every cutoff `B`,
`(∑_{1 ≤ i ≤ B} dᵢ(n)·i!) + ⌊n/(B+1)!⌋·(B+1)! = n`. The trailing term telescopes away once
`(B+1)! > n`. -/
theorem factDigit_recon (n : ℕ) :
    ∀ B, (∑ i ∈ Finset.Ico 1 (B + 1), factDigit i n * i !) + n / (B + 1)! * (B + 1)! = n := by
  intro B
  induction B with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ k + 1)]
    -- reduce the new top term + new remainder to the old remainder, then apply `ih`
    have hfac : (k + 1 + 1)! = (k + 2) * (k + 1)! := by
      rw [Nat.factorial_succ]
    have hdiv : n / (k + 1 + 1)! = n / (k + 1)! / (k + 2) := by
      rw [hfac, Nat.div_div_eq_div_mul, Nat.mul_comm]
    set q := n / (k + 1)! with hq
    have key : factDigit (k + 1) n * (k + 1)! + n / (k + 1 + 1)! * (k + 1 + 1)!
        = q * (k + 1)! := by
      rw [hdiv, hfac, factDigit, ← hq]
      have hmd : q % (k + 2) + q / (k + 2) * (k + 2) = q := Nat.mod_add_div' q (k + 2)
      calc q % (k + 2) * (k + 1)! + q / (k + 2) * ((k + 2) * (k + 1)!)
          = (q % (k + 2) + q / (k + 2) * (k + 2)) * (k + 1)! := by ring
        _ = q * (k + 1)! := by rw [hmd]
    rw [add_assoc, key]
    exact ih

/-- **Reconstruction.** If `n < (B+1)!` then `n = ∑_{1 ≤ i ≤ B} dᵢ(n)·i!`. -/
theorem factDigit_sum (n B : ℕ) (hB : n < (B + 1)!) :
    n = ∑ i ∈ Finset.Ico 1 (B + 1), factDigit i n * i ! := by
  have h := factDigit_recon n B
  have : n / (B + 1)! = 0 := Nat.div_eq_of_lt hB
  rw [this, Nat.zero_mul, Nat.add_zero] at h
  exact h.symm

end Erdos403
