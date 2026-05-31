import Mathlib

/-!
# Erdős Problem #403 — sums of distinct factorials that are powers of 2

**Problem (Burr–Erdős; [ErGr80, p.79]).** Does
`2^m = a₁! + a₂! + ⋯ + aₖ!` with `a₁ < a₂ < ⋯ < aₖ` have only finitely many solutions?

**Answer: yes** (Frankl and Shen Lin, independently, 1976 — both proofs *unpublished*;
Lin's was a Bell Labs internal memorandum, "On Two Problems of Erdős Concerning Sums of
Distinct Factorials"). The largest solution is `2⁷ = 2! + 3! + 5! = 128`. Lin further showed
the largest power of `2` dividing a sum of distinct factorials *containing* `2!` is `2²⁵⁴`.

Because the original proofs are lost to the literature, this is a **reconstruction**, not a
transcription. The engine is Legendre's formula at `p = 2`: `v₂(n!) = n − s₂(n)` (mathlib:
`sub_one_mul_padicValNat_factorial`), the size sandwich `aₖ! ≤ S < 2·aₖ!`, and a bounded-carry
argument controlling `v₂` of the sum. The finite endgame is decidable via the factorial number
system (a sum of distinct factorials is exactly a factorial-base numeral with all digits ≤ 1).

A "sum of distinct factorials" is modelled by a `Finset ℕ` of indices (distinctness of the
`aᵢ` is automatic). Note `0! = 1! = 1`, so e.g. `{0,1}` sums to `2`.
-/

namespace Erdos403

open Finset
open scoped Nat

/-- The sum of distinct factorials indexed by `S`: `∑_{a ∈ S} a!`. -/
def factSum (S : Finset ℕ) : ℕ := ∑ a ∈ S, a !

/-! ## Step 1 — the size sandwich

For nonempty `S` with top element `M = max' S`:  `M! ≤ factSum S ≤ 2·M!`.
(The doc's strict upper `< 2·M!` is false at `M ∈ {1,2}`, e.g. `{0,1} ↦ 2 = 2·1!`; the
non-strict bound is what the downstream contradiction uses — the real work is the lower bound
combined with `2^{M-1} < M!` for `M ≥ 3`.) -/

/-- The partial factorial sum is bounded by the top factorial: `∑_{a<n} a! ≤ n!`. Tight at
`n = 0,1,2`. -/
theorem sum_range_factorial_le (n : ℕ) : ∑ a ∈ Finset.range n, a ! ≤ n ! := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · calc ∑ a ∈ Finset.range k, a ! + k ! ≤ k ! + k ! := Nat.add_le_add_right ih _
        _ = 2 * k ! := by ring
        _ ≤ (k + 1) * k ! := by gcongr; omega
        _ = (k + 1)! := (Nat.factorial_succ k).symm

/-- Lower bound of the sandwich: the top factorial is one of the summands. -/
theorem factorial_max_le_factSum {S : Finset ℕ} (h : S.Nonempty) :
    (S.max' h)! ≤ factSum S :=
  Finset.single_le_sum (f := fun a => a !) (fun _ _ => Nat.zero_le _) (S.max'_mem h)

/-- Upper bound of the sandwich. -/
theorem factSum_le_two_mul_factorial_max {S : Finset ℕ} (h : S.Nonempty) :
    factSum S ≤ 2 * (S.max' h)! := by
  set M := S.max' h with hM
  have hsub : S ⊆ Finset.range (M + 1) := fun a ha =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (S.le_max' a ha))
  calc factSum S ≤ ∑ a ∈ Finset.range (M + 1), a ! :=
        Finset.sum_le_sum_of_subset hsub
    _ = ∑ a ∈ Finset.range M, a ! + M ! := Finset.sum_range_succ _ _
    _ ≤ M ! + M ! := Nat.add_le_add_right (sum_range_factorial_le M) _
    _ = 2 * M ! := by ring

/-- `2^M < M!` for `M ≥ 4` (the "factorial outruns powers of two" fact; tight: `3! = 6 ≤ 8`,
`4! = 24 > 16`). Used to turn `M! ≤ 2^M` into `M ≤ 3`. -/
theorem two_pow_lt_factorial {M : ℕ} (hM : 4 ≤ M) : 2 ^ M < M ! := by
  induction M, hM using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ < 2 * k ! := by omega
      _ ≤ (k + 1) * k ! := by gcongr; omega
      _ = (k + 1)! := (Nat.factorial_succ k).symm

/-! ## Step 2 — 2-adic valuation of factorials (Legendre engine)

`v₂ := padicValNat 2`. The wrapper records Legendre at `p = 2`; monotonicity and the divisibility
characterization (via mathlib `padicValNat_dvd_iff_le`) are what the carry analysis needs. -/

/-- Binary digit sum (popcount). -/
def s₂ (n : ℕ) : ℕ := (Nat.digits 2 n).sum

/-- **Legendre at `p = 2`**: `v₂(n!) = n − s₂(n)`. -/
theorem padicValNat_two_factorial (n : ℕ) : padicValNat 2 (n !) = n - s₂ n := by
  have h := sub_one_mul_padicValNat_factorial (p := 2) n
  simpa [s₂] using h

/-- `v₂(n!) ≤ n`. -/
theorem padicValNat_two_factorial_le (n : ℕ) : padicValNat 2 (n !) ≤ n :=
  padicValNat_factorial_le 2 n

/-- `v₂(·!)` is monotone: bigger factorials are at least as 2-divisible. -/
theorem padicValNat_two_factorial_mono {a b : ℕ} (hab : a ≤ b) :
    padicValNat 2 (a !) ≤ padicValNat 2 (b !) := by
  set k := padicValNat 2 (a !) with hk
  have h1 : (2 : ℕ) ^ k ∣ a ! :=
    (padicValNat_dvd_iff_le (p := 2) (Nat.factorial_ne_zero a)).mpr le_rfl
  have h2 : (2 : ℕ) ^ k ∣ b ! := h1.trans (Nat.factorial_dvd_factorial hab)
  exact (padicValNat_dvd_iff_le (p := 2) (Nat.factorial_ne_zero b)).mp h2

/-! ## Step 3 — the generic (unique-minimum) case

If the smallest element `a₀ = min' S` has strictly-smallest `v₂(a₀!)` (the "unique minimum"
case — everything else is more 2-divisible), then `v₂(factSum S) = v₂(a₀!)`: the unique minimal
power survives, the rest cancels into an even cofactor. -/

theorem v2_factSum_of_unique_min {S : Finset ℕ} (h : S.Nonempty)
    (huniq : ∀ a ∈ S, a ≠ S.min' h → padicValNat 2 ((S.min' h)!) < padicValNat 2 (a !)) :
    padicValNat 2 (factSum S) = padicValNat 2 ((S.min' h)!) := by
  set a₀ := S.min' h with ha₀
  set k := padicValNat 2 (a₀ !) with hk
  -- factSum splits as the bottom factorial plus the rest.
  have hsplit : factSum S = a₀ ! + ∑ a ∈ S.erase a₀, a ! :=
    (Finset.add_sum_erase S _ (S.min'_mem h)).symm
  -- exact divisibility of the bottom term
  have hdvd_a₀ : (2 : ℕ) ^ k ∣ a₀ ! :=
    (padicValNat_dvd_iff_le (p := 2) (Nat.factorial_ne_zero a₀)).mpr le_rfl
  have hnotdvd_a₀ : ¬ (2 : ℕ) ^ (k + 1) ∣ a₀ ! := by
    rw [padicValNat_dvd_iff_le (p := 2) (Nat.factorial_ne_zero a₀)]; omega
  -- every other term is divisible by 2^{k+1}
  have hdvd_rest : (2 : ℕ) ^ (k + 1) ∣ ∑ a ∈ S.erase a₀, a ! := by
    refine Finset.dvd_sum ?_
    intro a ha
    rw [Finset.mem_erase] at ha
    have hlt : k < padicValNat 2 (a !) := huniq a ha.2 ha.1
    exact (padicValNat_dvd_iff_le (p := 2) (Nat.factorial_ne_zero a)).mpr (by omega)
  -- 2^k divides the whole sum, 2^{k+1} does not
  have hpos : factSum S ≠ 0 := by
    have : a₀ ! ≤ factSum S :=
      Finset.single_le_sum (f := fun a => a !) (fun _ _ => Nat.zero_le _) (S.min'_mem h)
    have := Nat.factorial_pos a₀; omega
  have hdvd_sum : (2 : ℕ) ^ k ∣ factSum S := by
    rw [hsplit]
    exact Dvd.dvd.add hdvd_a₀ (dvd_trans (pow_dvd_pow 2 (Nat.le_succ k)) hdvd_rest)
  have hnotdvd_sum : ¬ (2 : ℕ) ^ (k + 1) ∣ factSum S := by
    rw [hsplit]
    intro hc
    exact hnotdvd_a₀ ((Nat.dvd_add_left hdvd_rest).mp hc)
  -- conclude v₂(factSum) = k
  have hle : k ≤ padicValNat 2 (factSum S) :=
    (padicValNat_dvd_iff_le (p := 2) hpos).mp hdvd_sum
  have hlt : padicValNat 2 (factSum S) < k + 1 := by
    by_contra hc
    exact hnotdvd_sum ((padicValNat_dvd_iff_le (p := 2) hpos).mpr (by omega))
  omega

/-! ## Step 4 — the unique-minimum case is bounded

Combining the size sandwich (`M! ≤ factSum`) with Step 3 (`v₂(factSum) = v₂(a₀!) ≤ a₀ ≤ M`):
a power-of-two solution in the unique-min case forces `M! ≤ 2^M`, hence `M ≤ 3`. -/

theorem unique_min_bound {S : Finset ℕ} (h : S.Nonempty) {m : ℕ}
    (huniq : ∀ a ∈ S, a ≠ S.min' h → padicValNat 2 ((S.min' h)!) < padicValNat 2 (a !))
    (hpow : factSum S = 2 ^ m) : S.max' h ≤ 3 := by
  set a₀ := S.min' h with ha₀
  set M := S.max' h with hM
  -- m = v₂(factSum) = v₂(a₀!) ≤ a₀ ≤ M
  have hm : m = padicValNat 2 (a₀ !) := by
    have h1 : padicValNat 2 (factSum S) = padicValNat 2 (a₀ !) := v2_factSum_of_unique_min h huniq
    rw [hpow, padicValNat.prime_pow] at h1
    exact h1
  have ha₀M : a₀ ≤ M := S.min'_le M (S.max'_mem h)
  have hmM : m ≤ M := by
    have := padicValNat_two_factorial_le a₀
    omega
  -- M! ≤ factSum = 2^m ≤ 2^M
  have hsand : M ! ≤ 2 ^ m := by rw [← hpow]; exact factorial_max_le_factSum h
  have hMM : M ! ≤ 2 ^ M := hsand.trans (Nat.pow_le_pow_right (by norm_num) hmM)
  -- 2^M < M! for M ≥ 4, so M ≤ 3
  by_contra hc
  exact absurd hMM (Nat.not_le.mpr (two_pow_lt_factorial (by omega)))

/-- The extremal witness: `2! + 3! + 5! = 2 + 6 + 120 = 128 = 2⁷`.
(`native_decide` because `Finset.sum` reduces through `Quot` and the kernel `decide` gets
stuck; this is isolated to the witness and doesn't touch the main theorems.) -/
theorem witness : factSum {2, 3, 5} = 2 ^ 7 := by native_decide

/-- **Erdős #403 (finiteness)** — this is exactly what the problem asks.
Only finitely many sums of distinct factorials are powers of `2`. -/
theorem erdos_403_finite :
    {S : Finset ℕ | ∃ m : ℕ, factSum S = 2 ^ m}.Finite := by
  sorry

/-- **Erdős #403 (sharp form)** — the largest such power of `2` is `2⁷`.
Equivalently every solution has `m ≤ 7`, and `m = 7` is attained by `witness`. -/
theorem erdos_403_sharp {S : Finset ℕ} {m : ℕ} (h : factSum S = 2 ^ m) : m ≤ 7 := by
  sorry

end Erdos403
