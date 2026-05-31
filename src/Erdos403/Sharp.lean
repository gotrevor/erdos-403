import Mathlib
import Erdos403.Basic
import Erdos403.FactBase

/-!
# Erdős #403 — the sharp bound `m ≤ 7` (Phases B–D)

Using the factorial number system (`FactBase`), `factSum S = 2^m` is impossible once `2^m` and
`2^m − 1` both carry a factorial digit `≥ 2` (`not_factSum_of_digits`).

* **Phase B (this file, done):** `m` even `≥ 4` is killed cleanly — `2^m ≡ 16 (mod 24)` forces the
  `3!`-digit of *both* `2^m` and `2^m − 1` to be `2` (and `3! = 6` has no factorial degeneracy, so
  the `0!` carry cannot fix it).
* **Phase C (todo):** `m` odd `≥ 9` — the residual Lin kernel (a middle digit `≥ 2`).
* **Phase D (todo):** assemble `erdos_403_sharp` (`decide` the small `m`).
-/

namespace Erdos403

open scoped Nat

/-- `2^(2t+4) ≡ 16 (mod 24)` — the period-2 cycle `…,16,8,16,8,…` of `2^m mod 24` (`m ≥ 3`),
on the even branch. -/
theorem two_pow_mod_24_even : ∀ t, 2 ^ (2 * t + 4) % 24 = 16 := by
  intro t
  induction t with
  | zero => decide
  | succ k ih =>
    have he : 2 * (k + 1) + 4 = (2 * k + 4) + 2 := by ring
    rw [he, pow_add, Nat.mul_mod, ih]
    decide

/-- `2^m ≡ 16 (mod 24)` for even `m ≥ 4`. -/
theorem two_pow_mod_24_of_even {m : ℕ} (he : Even m) (hm : 4 ≤ m) : 2 ^ m % 24 = 16 := by
  obtain ⟨r, rfl⟩ := he
  have hrw : r + r = 2 * (r - 2) + 4 := by omega
  rw [hrw]; exact two_pow_mod_24_even (r - 2)

/-- For even `m ≥ 4`, the `3!`-digit of `2^m` is `2`. -/
theorem factDigit_three_two_pow_even {m : ℕ} (he : Even m) (hm : 4 ≤ m) :
    factDigit 3 (2 ^ m) = 2 := by
  have h := two_pow_mod_24_of_even he hm
  obtain ⟨q, hq⟩ : ∃ q, 2 ^ m = 24 * q + 16 := ⟨2 ^ m / 24, by omega⟩
  show (2 ^ m / 6) % 4 = 2
  rw [hq]; omega

/-- For even `m ≥ 4`, the `3!`-digit of `2^m − 1` is also `2` (so the `0!` carry can't rescue it). -/
theorem factDigit_three_two_pow_sub_one_even {m : ℕ} (he : Even m) (hm : 4 ≤ m) :
    factDigit 3 (2 ^ m - 1) = 2 := by
  have h := two_pow_mod_24_of_even he hm
  obtain ⟨q, hq⟩ : ∃ q, 2 ^ m = 24 * q + 16 := ⟨2 ^ m / 24, by omega⟩
  show ((2 ^ m - 1) / 6) % 4 = 2
  rw [hq]; omega

/-- **Phase B result.** No sum of distinct factorials equals `2^m` for even `m ≥ 4`. -/
theorem factSum_ne_of_even {m : ℕ} (he : Even m) (hm : 4 ≤ m) (S : Finset ℕ) :
    factSum S ≠ 2 ^ m := by
  refine not_factSum_of_digits (2 ^ m) ⟨3, by omega, ?_⟩ ⟨3, by omega, ?_⟩ S
  · rw [factDigit_three_two_pow_even he hm]
  · rw [factDigit_three_two_pow_sub_one_even he hm]

end Erdos403
