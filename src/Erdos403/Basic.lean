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

/-- The single-step valuation increment: `v₂((n+1)!) = v₂(n!) + v₂(n+1)`. -/
theorem v2_factorial_succ (n : ℕ) :
    padicValNat 2 ((n + 1)!) = padicValNat 2 (n !) + padicValNat 2 (n + 1) := by
  rw [Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero n)]
  omega

/-- **Ties only come in consecutive pairs.** Crossing a span of two strictly increases `v₂`,
because of the two consecutive integers `n+1, n+2` one is even. -/
theorem v2_factorial_lt_factorial_add_two (n : ℕ) :
    padicValNat 2 (n !) < padicValNat 2 ((n + 2)!) := by
  have h1 : padicValNat 2 ((n + 2)!) = padicValNat 2 ((n + 1)!) + padicValNat 2 (n + 2) :=
    v2_factorial_succ (n + 1)
  have h2 : padicValNat 2 ((n + 1)!) = padicValNat 2 (n !) + padicValNat 2 (n + 1) :=
    v2_factorial_succ n
  have hone : 1 ≤ padicValNat 2 (n + 1) + padicValNat 2 (n + 2) := by
    rcases (by omega : (2 : ℕ) ∣ (n + 1) ∨ (2 : ℕ) ∣ (n + 2)) with hd | hd
    · have := one_le_padicValNat_of_dvd (p := 2) (by omega) hd; omega
    · have := one_le_padicValNat_of_dvd (p := 2) (by omega) hd; omega
  omega

/-- Distance ≥ 2 gives strict growth (combine the span-of-two jump with monotonicity). -/
theorem v2_factorial_lt_of_add_two_le {a b : ℕ} (h : a + 2 ≤ b) :
    padicValNat 2 (a !) < padicValNat 2 (b !) :=
  lt_of_lt_of_le (v2_factorial_lt_factorial_add_two a) (padicValNat_two_factorial_mono h)

/-- Stepping past an **odd** `a` strictly increases `v₂` (the successor `a+1` is even). -/
theorem v2_factorial_lt_succ_of_odd {a : ℕ} (ho : Odd a) :
    padicValNat 2 (a !) < padicValNat 2 ((a + 1)!) := by
  rw [v2_factorial_succ]
  have hd : (2 : ℕ) ∣ (a + 1) := by rcases ho with ⟨t, rfl⟩; omega
  have := one_le_padicValNat_of_dvd (p := 2) (by omega) hd
  omega

/-- **The unique-minimum dichotomy.** If the bottom is *not* a tied pair (`a₀` even with
`a₀+1 ∈ S`), then `a₀ = min' S` is the unique `v₂`-minimum — the hypothesis Step 3 needs.
Conversely, by `v2_factorial_lt_factorial_add_two`, a tie can *only* be this bottom pair. -/
theorem unique_min_of_not_tied {S : Finset ℕ} (h : S.Nonempty)
    (hnt : ¬ (Even (S.min' h) ∧ S.min' h + 1 ∈ S)) :
    ∀ a ∈ S, a ≠ S.min' h → padicValNat 2 ((S.min' h)!) < padicValNat 2 (a !) := by
  set a₀ := S.min' h with ha₀
  intro a ha hne
  have hgt : a₀ < a := lt_of_le_of_ne (S.min'_le a ha) (Ne.symm hne)
  rcases Nat.lt_or_ge a (a₀ + 2) with hlt | hge2
  · have heq : a = a₀ + 1 := by omega
    have hmem : a₀ + 1 ∈ S := heq ▸ ha
    have hodd : Odd a₀ := by
      rcases Nat.even_or_odd a₀ with he | ho
      · exact absurd ⟨he, hmem⟩ hnt
      · exact ho
    rw [heq]; exact v2_factorial_lt_succ_of_odd hodd
  · exact v2_factorial_lt_of_add_two_le hge2

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

/-- In the unique-min case the exponent never exceeds the top index: `m = v₂(a₀!) ≤ a₀ ≤ M`.
This is the half of the carry ceiling that is *fully proven*. -/
theorem m_le_max_of_unique_min {S : Finset ℕ} (h : S.Nonempty) {m : ℕ}
    (huniq : ∀ a ∈ S, a ≠ S.min' h → padicValNat 2 ((S.min' h)!) < padicValNat 2 (a !))
    (hpow : factSum S = 2 ^ m) : m ≤ S.max' h := by
  have hm : m = padicValNat 2 ((S.min' h) !) := by
    have h1 : padicValNat 2 (factSum S) = padicValNat 2 ((S.min' h) !) :=
      v2_factSum_of_unique_min h huniq
    rw [hpow, padicValNat.prime_pow] at h1
    exact h1
  have ha₀M : S.min' h ≤ S.max' h := S.min'_le _ (S.max'_mem h)
  have := padicValNat_two_factorial_le (S.min' h)
  omega

theorem unique_min_bound {S : Finset ℕ} (h : S.Nonempty) {m : ℕ}
    (huniq : ∀ a ∈ S, a ≠ S.min' h → padicValNat 2 ((S.min' h)!) < padicValNat 2 (a !))
    (hpow : factSum S = 2 ^ m) : S.max' h ≤ 3 := by
  set M := S.max' h with hM
  have hmM : m ≤ M := m_le_max_of_unique_min h huniq hpow
  -- M! ≤ factSum = 2^m ≤ 2^M, and 2^M < M! for M ≥ 4, so M ≤ 3.
  have hsand : M ! ≤ 2 ^ m := by rw [← hpow]; exact factorial_max_le_factSum h
  have hMM : M ! ≤ 2 ^ M := hsand.trans (Nat.pow_le_pow_right (by norm_num) hmM)
  by_contra hc
  exact absurd hMM (Nat.not_le.mpr (two_pow_lt_factorial (by omega)))

/-- **The bottom index is at most 2.** Since `a₀ = min' S` divides every `a!` (`a ∈ S`), `a₀!`
divides `factSum S = 2^m`, so `a₀!` is a power of two — which fails once `a₀ ≥ 3` (then `3 ∣ a₀!`
but `3 ∤ 2^m`). So `min' S ∈ {0,1,2}` for *every* solution. (Enumeration: the only solutions are
`m ∈ {0,1,2,3,5,7}`, values `1,2,4,8,32,128`; each `min=2` solution has a `min=0` twin via
`0!+1! = 2 = 2!`.) -/
theorem min'_le_two {S : Finset ℕ} (h : S.Nonempty) {m : ℕ} (hpow : factSum S = 2 ^ m) :
    S.min' h ≤ 2 := by
  by_contra hc
  have hge : 3 ≤ S.min' h := by omega
  have hdvd : (S.min' h)! ∣ 2 ^ m := by
    rw [← hpow, factSum]
    exact Finset.dvd_sum fun a ha => Nat.factorial_dvd_factorial (S.min'_le a ha)
  have h3 : (3 : ℕ) ∣ 2 ^ m := (Nat.dvd_factorial (by norm_num) hge).trans hdvd
  have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) h3
  omega

/-! ## Step 5 — the carry ceiling (research kernel)

The single remaining gap. In the unique-min case Step 4 already gives `m ≤ M`; the content is
the **tied-pair** case, where a bottom pair `{a₀, a₀+1}` carries. The claim is that the carry is
*bounded*: `v₂(factSum S) = m` exceeds the bottom index `max' S` by at most an absolute constant
`B`. This is exactly the bounded-carry estimate Lin/Frankl proved and never published. -/

/-- `8 ∣ a!` for `a ≥ 4` (since `8 ∣ 4! = 24` and `4! ∣ a!`). -/
theorem eight_dvd_factorial {a : ℕ} (ha : 4 ≤ a) : (8 : ℕ) ∣ a ! :=
  (by decide : (8 : ℕ) ∣ 4 !).trans (Nat.factorial_dvd_factorial ha)

/-- **The `a₀ = 0`-with-`2` case dies by parity mod 8.** If `{0,1,2} ⊆ S` then `factSum S ≢ 0
(mod 8)`: the bottom three contribute `0!+1!+2! = 4`, an optional `3!` adds `6`, and every `a ≥ 4`
term is `≡ 0`. So `factSum S ≡ 4` or `2 (mod 8)`, never `0`; hence no such sum is `2^m` with
`m ≥ 3`. (This is what lets the tied case `a₀ = 0, 2 ∈ S` collapse to `m ≤ 2`.) -/
theorem not_eight_dvd_factSum_of_mem_012 {S : Finset ℕ}
    (h0 : 0 ∈ S) (h1 : 1 ∈ S) (h2 : 2 ∈ S) : ¬ (8 : ℕ) ∣ factSum S := by
  by_cases h3 : 3 ∈ S
  · -- `{0,1,2,3} ⊆ S`; `factSum = 10 + (multiple of 8)`, and `8 ∤ 10`.
    have hsub : ({0, 1, 2, 3} : Finset ℕ) ⊆ S := by intro x hx; fin_cases hx <;> assumption
    have hrest : (8 : ℕ) ∣ ∑ a ∈ S \ {0, 1, 2, 3}, a ! := by
      refine Finset.dvd_sum fun a ha => eight_dvd_factorial ?_
      have hns : a ∉ ({0, 1, 2, 3} : Finset ℕ) := (Finset.mem_sdiff.mp ha).2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hns; omega
    have hsplit : factSum S = (∑ a ∈ S \ {0, 1, 2, 3}, a !) + ∑ a ∈ ({0, 1, 2, 3} : Finset ℕ), a ! :=
      (Finset.sum_sdiff hsub).symm
    have hval : (∑ a ∈ ({0, 1, 2, 3} : Finset ℕ), a !) = 10 := by decide
    intro hdvd; rw [hsplit, hval] at hdvd; omega
  · -- `{0,1,2} ⊆ S`, `3 ∉ S`; `factSum = 4 + (multiple of 8)`, and `8 ∤ 4`.
    have hsub : ({0, 1, 2} : Finset ℕ) ⊆ S := by intro x hx; fin_cases hx <;> assumption
    have hrest : (8 : ℕ) ∣ ∑ a ∈ S \ {0, 1, 2}, a ! := by
      refine Finset.dvd_sum fun a ha => eight_dvd_factorial ?_
      have hmem := Finset.mem_sdiff.mp ha
      have hns : a ∉ ({0, 1, 2} : Finset ℕ) := hmem.2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hns
      have h3a : a ≠ 3 := by rintro rfl; exact h3 hmem.1
      omega
    have hsplit : factSum S = (∑ a ∈ S \ {0, 1, 2}, a !) + ∑ a ∈ ({0, 1, 2} : Finset ℕ), a ! :=
      (Finset.sum_sdiff hsub).symm
    have hval : (∑ a ∈ ({0, 1, 2} : Finset ℕ), a !) = 4 := by decide
    intro hdvd; rw [hsplit, hval] at hdvd; omega

/-- **The cascade kernel — the sole remaining `sorry`, now bottom-pinned to `a₀ = 2`.** With the
bottom *exactly* the tied pair `{2,3}` (`min' S = 2`, `3 ∈ S`) and `factSum S = 2^m`, the carry
cascades to `m ≤ max' S + 2`. `tied_sharp_ceiling` reduces its whole `Even (min' S)` hypothesis to
this one statement: `min'_le_two` pins `a₀ ∈ {0,2}`, the `a₀ = 0 ∧ 2 ∈ S` case dies by
`not_eight_dvd_factSum_of_mem_012`, and the `a₀ = 0 ∧ 2 ∉ S` case maps to here by the `0!+1! = 2!`
twin surgery. So this is the genuine, irreducible Lin/Frankl carry estimate — everything else in the
file is reconstructed and axiom-clean. The cascade: `2^m = 8 + ∑_{a≥4∈S} a!`, i.e.
`2^{m-3} = 1 + ∑_{a≥4} a!/8`; `a!/8` is odd iff `a ∈ {4,5}`, so parity pins membership one pair up
and recurses, terminating at `m ≤ max' S + 2` (`{2,3,5} ↦ 2⁷` extremal). -/
theorem cascade_two {S : Finset ℕ} (h : S.Nonempty) {m : ℕ}
    (hmin : S.min' h = 2) (hmem3 : 3 ∈ S) (hpow : factSum S = 2 ^ m) :
    m ≤ S.max' h + 2 := by
  sorry

/-- **The sharp tied-pair carry ceiling (Step 5).** When the
bottom is a tied pair (`a₀ = min' S` even, `a₀+1 ∈ S`) and `factSum S = 2^m`, the carry from
`(2j)!+(2j+1)! = (2j)!·2·(j+1)` cascades only to `m ≤ max' S + 2` (explicit `B = 2`, attained by
`{2,3,5} ↦ 2⁷`). This lone statement is the entire unpublished Lin/Frankl estimate; everything else
in this file is reconstructed and axiom-clean.

`B = 2` is the *empirical sharp value*: exhaustive search shows every power-of-two factorial sum has
`m − max' S ≤ 2`. (The general gap `v₂(factSum S) − max' S` is *unbounded* — `{2ᵗ−2,2ᵗ−1,2ᵗ+1}` gives
gap `2t−2` — so the odd-part-`1` hypothesis `factSum S = 2^m` is essential; no constant `B` works
without it.) With `B = 2` explicit, this single kernel discharges **both** `erdos_403_finite` (via
`tied_carry_ceiling` below) and the sharp `erdos_403_sharp` (`m ≤ 7`). -/
theorem tied_sharp_ceiling (S : Finset ℕ) (h : S.Nonempty) (m : ℕ)
    (he : Even (S.min' h)) (hmem : S.min' h + 1 ∈ S) (hpow : factSum S = 2 ^ m) :
    m ≤ S.max' h + 2 := by
  -- Base case `max' S ≤ 2`: `factSum S ≤ 0!+1!+2! = 4 ⟹ m ≤ 2`.
  rcases Nat.lt_or_ge (S.max' h) 3 with hM2 | hM3
  · have hsub : S ⊆ ({0, 1, 2} : Finset ℕ) := by
      intro a ha
      have := S.le_max' a ha
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have hle4 : factSum S ≤ 4 :=
      le_trans (Finset.sum_le_sum_of_subset hsub) (by decide)
    have hm2 : m ≤ 2 := by
      by_contra hc
      have : (2 : ℕ) ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [hpow] at hle4; omega
    omega
  · -- `max' S ≥ 3`. With `min'_le_two` and `Even`, the bottom is `a₀ ∈ {0, 2}`.
    have hle2 := min'_le_two h hpow
    rcases (by omega : S.min' h = 0 ∨ S.min' h = 1 ∨ S.min' h = 2) with hm0 | hm1 | hm2
    · -- `a₀ = 0`: `0 ∈ S` and (from `hmem`) `1 ∈ S`.
      have h0 : (0 : ℕ) ∈ S := hm0 ▸ S.min'_mem h
      have h1 : (1 : ℕ) ∈ S := by have := hmem; rw [hm0] at this; simpa using this
      by_cases h2 : (2 : ℕ) ∈ S
      · -- `2 ∈ S`: mod-8 parity forbids `8 ∣ factSum`, so `m ≤ 2`.
        have hnd := not_eight_dvd_factSum_of_mem_012 h0 h1 h2
        have hm2 : m ≤ 2 := by
          by_contra hc
          exact hnd (by rw [hpow]; exact (by norm_num : (8 : ℕ) = 2 ^ 3) ▸ pow_dvd_pow 2 (by omega))
        omega
      · -- `2 ∉ S`: twin surgery `{0,1} ↦ {2}` (since `0!+1! = 2 = 2!`), preserving `factSum`,
        -- `max'` (as `max' S ≥ 3`) and landing `min' = 2`; then dispatch via `cascade_two`.
        set T := (S.erase 0).erase 1 with hT
        set S' := insert 2 T with hS'
        have hT_ge : ∀ a ∈ T, 3 ≤ a := by
          intro a ha
          rw [hT, Finset.mem_erase, Finset.mem_erase] at ha
          obtain ⟨ha1, ha0, haS⟩ := ha
          have : a ≠ 2 := fun hc => h2 (hc ▸ haS)
          omega
        have h2T : (2 : ℕ) ∉ T := fun hc => by have := hT_ge 2 hc; omega
        have e1 : factSum S = 0 ! + ∑ a ∈ S.erase 0, a ! := by
          rw [factSum]; exact (Finset.add_sum_erase S _ h0).symm
        have h1e : (1 : ℕ) ∈ S.erase 0 := Finset.mem_erase.mpr ⟨one_ne_zero, h1⟩
        have e2 : ∑ a ∈ S.erase 0, a ! = 1 ! + ∑ a ∈ (S.erase 0).erase 1, a ! :=
          (Finset.add_sum_erase _ _ h1e).symm
        have hfs_S : factSum S = 2 + ∑ a ∈ T, a ! := by
          rw [e1, e2, ← hT, Nat.factorial_zero, Nat.factorial_one]; ring
        have hfs_S' : factSum S' = 2 + ∑ a ∈ T, a ! := by
          rw [hS', factSum, Finset.sum_insert h2T, Nat.factorial_two]
        have hpow' : factSum S' = 2 ^ m := by rw [hfs_S', ← hfs_S, hpow]
        have h' : S'.Nonempty := ⟨2, by rw [hS']; exact Finset.mem_insert_self 2 T⟩
        have hmin' : S'.min' h' = 2 := by
          refine le_antisymm (S'.min'_le 2 (by rw [hS']; exact Finset.mem_insert_self 2 T)) ?_
          refine S'.le_min' h' 2 (fun a ha => ?_)
          rw [hS', Finset.mem_insert] at ha
          rcases ha with rfl | ha
          · rfl
          · have := hT_ge a ha; omega
        have hMmem : S.max' h ∈ T := by
          rw [hT, Finset.mem_erase, Finset.mem_erase]
          exact ⟨by omega, by omega, S.max'_mem h⟩
        have hmax' : S'.max' h' = S.max' h := by
          refine le_antisymm (S'.max'_le h' _ (fun a ha => ?_)) ?_
          · rw [hS', Finset.mem_insert] at ha
            rcases ha with rfl | ha
            · omega
            · exact S.le_max' a (by rw [hT, Finset.mem_erase, Finset.mem_erase] at ha; exact ha.2.2)
          · exact S'.le_max' (S.max' h) (by rw [hS']; exact Finset.mem_insert_of_mem hMmem)
        by_cases h3' : (3 : ℕ) ∈ S'
        · have := cascade_two h' hmin' h3' hpow'; rw [hmax'] at this; exact this
        · -- not tied (`min' = 2` even but `3 ∉ S'`) ⟹ unique-min ⟹ `m ≤ 3 ≤ max' + 2`.
          have hnt : ¬ (Even (S'.min' h') ∧ S'.min' h' + 1 ∈ S') := by
            rw [hmin']; rintro ⟨_, hc⟩; exact h3' hc
          have hm3 := m_le_max_of_unique_min h' (unique_min_of_not_tied h' hnt) hpow'
          omega
    · -- `a₀ = 1` is impossible: `Even 1` is false.
      rw [hm1] at he; exact absurd he (by decide)
    · -- `a₀ = 2`: `3 ∈ S` (from `hmem`); apply the cascade kernel directly.
      have hmem3 : (3 : ℕ) ∈ S := by have := hmem; rw [hm2] at this; simpa using this
      exact cascade_two h hm2 hmem3 hpow

/-- **Tied-pair carry ceiling.** The existential form `carry_ceiling`/`erdos_403_finite` consume,
now *proven* from the sharp kernel with the explicit witness `B = 2`. -/
theorem tied_carry_ceiling :
    ∃ B : ℕ, ∀ (S : Finset ℕ) (h : S.Nonempty) (m : ℕ),
      Even (S.min' h) → S.min' h + 1 ∈ S → factSum S = 2 ^ m → m ≤ S.max' h + B :=
  ⟨2, fun S h m he hmem hpow => tied_sharp_ceiling S h m he hmem hpow⟩

/-- **Carry ceiling.** Assembled from the (fully proven) unique-min half and the tied-pair
kernel: every power-of-two factorial sum has `m ≤ max' S + B`. -/
theorem carry_ceiling :
    ∃ B : ℕ, ∀ (S : Finset ℕ) (h : S.Nonempty) (m : ℕ), factSum S = 2 ^ m → m ≤ S.max' h + B := by
  obtain ⟨B, hB⟩ := tied_carry_ceiling
  refine ⟨B, fun S h m hpow => ?_⟩
  by_cases ht : Even (S.min' h) ∧ S.min' h + 1 ∈ S
  · exact hB S h m ht.1 ht.2 hpow
  · have hmM := m_le_max_of_unique_min h (unique_min_of_not_tied h ht) hpow
    omega

/-! ## Step 6 — finiteness (assembly)

Given the ceiling `m ≤ M + B` and the sandwich `M! ≤ 2^m`, we get `M! ≤ 2^{M+B}`. Since `M!`
outgrows `2^{M+B}` (the `4·(M-1)!` step beats the doubling once `M ≥ 4`), `M` is bounded, so every
solution lives in `(range (N+1)).powerset` — a finite family. -/

/-- For each `B`, eventually `M! > 2^B · 2^M`: factorials outrun powers of two by any fixed factor.
The recursion ratio `(k+1)/2 ≥ 2` (for `k ≥ 3`) lets one factor of `(k+1)!` absorb each doubling. -/
theorem exists_factorial_gt_two_pow (B : ℕ) :
    ∃ N, ∀ M, N ≤ M → 2 ^ B * 2 ^ M < M ! := by
  induction B with
  | zero => exact ⟨4, fun M hM => by simpa using two_pow_lt_factorial hM⟩
  | succ b ih =>
    obtain ⟨N, hN⟩ := ih
    refine ⟨max (N + 1) 4, fun M hM => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
    have hk4 : 4 ≤ k + 1 := le_trans (le_max_right _ _) hM
    have hNk : N ≤ k := by have := le_trans (le_max_left _ _) hM; omega
    have hrec : 2 ^ b * 2 ^ k < k ! := hN k hNk
    calc 2 ^ (b + 1) * 2 ^ (k + 1) = 4 * (2 ^ b * 2 ^ k) := by ring
      _ ≤ (k + 1) * (2 ^ b * 2 ^ k) := by gcongr
      _ < (k + 1) * k ! := Nat.mul_lt_mul_of_pos_left hrec (by omega)
      _ = (k + 1)! := (Nat.factorial_succ k).symm

/-- The extremal witness: `2! + 3! + 5! = 2 + 6 + 120 = 128 = 2⁷`.
(`native_decide` because `Finset.sum` reduces through `Quot` and the kernel `decide` gets
stuck; this is isolated to the witness and doesn't touch the main theorems.) -/
theorem witness : factSum {2, 3, 5} = 2 ^ 7 := by native_decide

/-- **Erdős #403 (finiteness)** — this is exactly what the problem asks.
Only finitely many sums of distinct factorials are powers of `2`. -/
theorem erdos_403_finite :
    {S : Finset ℕ | ∃ m : ℕ, factSum S = 2 ^ m}.Finite := by
  obtain ⟨B, hB⟩ := carry_ceiling
  obtain ⟨N, hN⟩ := exists_factorial_gt_two_pow B
  -- Every solution `S` is a subset of `range (N+1)`; that family is finite.
  apply Set.Finite.subset ((Finset.range (N + 1)).powerset : Finset (Finset ℕ)).finite_toSet
  intro S hS
  obtain ⟨m, hm⟩ := hS
  -- `S` is nonempty: `factSum ∅ = 0 ≠ 2^m`.
  have hne : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with rfl | h
    · rw [factSum, Finset.sum_empty] at hm
      exact absurd hm.symm (pow_ne_zero m two_ne_zero)
    · exact h
  set M := S.max' hne with hM
  -- Ceiling + sandwich pin `M ≤ N`.
  have hmle : m ≤ M + B := hB S hne m hm
  have hMle : M ≤ N := by
    by_contra hc
    have hgt : 2 ^ B * 2 ^ M < M ! := hN M (by omega)
    have hfac : M ! ≤ 2 ^ m := by rw [← hm]; exact factorial_max_le_factSum hne
    have hpow : 2 ^ m ≤ 2 ^ B * 2 ^ M := by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  -- Hence `S ⊆ range (N+1)`.
  refine Finset.mem_coe.mpr (Finset.mem_powerset.mpr (fun a ha => ?_))
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (le_trans (S.le_max' a ha) hMle))

/-- Size helper: `2^(M+2) < M!` for `M ≥ 6` (so the sandwich `M! ≤ 2^m ≤ 2^{M+2}` forces `M ≤ 5`). -/
theorem four_two_pow_lt_factorial {M : ℕ} (hM : 6 ≤ M) : 2 ^ (M + 2) < M ! := by
  induction M with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 6 with hk | hk
    · have : k = 5 := by omega
      subst this; decide
    · have hrec : 2 ^ (k + 2) < k ! := ih hk
      calc 2 ^ (k + 1 + 2) = 2 * 2 ^ (k + 2) := by ring
        _ < 2 * k ! := by omega
        _ ≤ (k + 1) * k ! := Nat.mul_le_mul_right _ (by omega)
        _ = (k + 1)! := (Nat.factorial_succ k).symm

/-- **Sharp, unique-min half (unconditional).** A unique-min solution has `m = v₂(a₀!) ≤ a₀ ≤ M ≤ 3`.
So any `m ∈ {5,7}` solution must be tied-pair — the sharp content lives entirely in the kernel. -/
theorem sharp_of_unique_min {S : Finset ℕ} (h : S.Nonempty) {m : ℕ}
    (huniq : ∀ a ∈ S, a ≠ S.min' h → padicValNat 2 ((S.min' h)!) < padicValNat 2 (a !))
    (hpow : factSum S = 2 ^ m) : m ≤ 3 := by
  have hb := unique_min_bound h huniq hpow
  have hmM := m_le_max_of_unique_min h huniq hpow
  omega

/-- **Erdős #403 (sharp form)** — the largest such power of `2` is `2⁷`.
Every solution has `m ≤ 7` (`m = 7` attained by `witness`). Proven from the single kernel
`tied_sharp_ceiling`: the unique-min case gives `m ≤ 3` (`sharp_of_unique_min`); the tied case gives
`m ≤ max' S + 2`, and the sandwich `M! ≤ 2^m ≤ 2^{M+2}` then forces `M ≤ 5`, hence `m ≤ 7`. -/
theorem erdos_403_sharp {S : Finset ℕ} {m : ℕ} (h : factSum S = 2 ^ m) : m ≤ 7 := by
  have hne : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with rfl | hh
    · rw [factSum, Finset.sum_empty] at h; exact absurd h.symm (pow_ne_zero m two_ne_zero)
    · exact hh
  by_cases ht : Even (S.min' hne) ∧ S.min' hne + 1 ∈ S
  · -- tied: kernel ⟹ m ≤ M+2; sandwich ⟹ M ≤ 5
    have hmM : m ≤ S.max' hne + 2 := tied_sharp_ceiling S hne m ht.1 ht.2 h
    rcases Nat.lt_or_ge (S.max' hne) 6 with h5 | h6
    · omega
    · exfalso
      have hfac : (S.max' hne)! ≤ 2 ^ m := by rw [← h]; exact factorial_max_le_factSum hne
      have hup : 2 ^ m ≤ 2 ^ (S.max' hne + 2) := Nat.pow_le_pow_right (by norm_num) hmM
      have hgt := four_two_pow_lt_factorial h6
      omega
  · -- unique-min: m ≤ 3
    have := sharp_of_unique_min hne (unique_min_of_not_tied hne ht) h
    omega

end Erdos403
