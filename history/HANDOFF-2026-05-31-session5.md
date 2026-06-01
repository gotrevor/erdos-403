# Handoff: Erdős #403 — kernel bottom-pinned to `cascade_two` (M ≥ 6)

**Date**: 2026-05-31 (session 5) · **Branch**: `tier1-finiteness` · **HEAD** `596180c`

## 🎯 What we're doing
Discharging the sorries in `~/src/erdos-403` to prove Erdős #403 (only finitely many sums of distinct
factorials are powers of 2; sharp: `m ≤ 7`). The whole problem still reduces to a **single `sorry`**,
but this session **pinned that sorry's bottom to `a₀ = 2` and scoped it to `M ≥ 6`**. `tied_sharp_ceiling`
is no longer the sorry — it's fully proven. The lone open lemma is now `cascade_two`, M≥6 branch.

## 🧠 Context to carry forward
- **The kernel, verbatim** (`Basic.lean`, the `sorry` is the `M ≥ 6` branch):
  ```
  theorem cascade_two {S : Finset ℕ} (h : S.Nonempty) {m : ℕ}
      (hmin : S.min' h = 2) (hmem3 : 3 ∈ S) (hpow : factSum S = 2 ^ m) :
      m ≤ S.max' h + 2
  ```
  Inside it, `M = max' S ≤ 5` is **already proven** (pure sandwich: `M! < 2^{M+2}` for `M ≤ 5` by
  `decide`, so `2^m ≤ 2·M! < 2^{M+3}`). **The `sorry` is only the `M ≥ 6` case.**
- **This session's restructure (session 5).** Previously `tied_sharp_ceiling` (covering `a₀ ∈ {0,2}`
  via `Even (min')`) was the sorry. Now it is *proven* by case-splitting the bottom:
  - `a₀ = 0 ∧ 2 ∈ S` → **dies** via `not_eight_dvd_factSum_of_mem_012` (NEW, axiom-clean): `{0,1,2}⊆S`
    ⟹ `factSum ≡ 4` or `2 (mod 8)`, never `0`, so `8 ∤ factSum` ⟹ `m ≤ 2`.
  - `a₀ = 0 ∧ 2 ∉ S` → **twin surgery** `{0,1} ↦ {2}` (because `0!+1! = 2 = 2!`):
    `S' = insert 2 ((S.erase 0).erase 1)` has the same `factSum`, the same `max'` (uses `max' S ≥ 3`),
    and `min' = 2`; then dispatch by `cascade_two` (if `3∈S'`) or `m_le_max_of_unique_min` (if not).
  - base `max' S ≤ 2` → `factSum ≤ 0!+1!+2! = 4` ⟹ `m ≤ 2`.
  So **everything funnels into `cascade_two`**, and `cascade_two`'s only gap is `M ≥ 6`.
- **Why `M ≥ 6` is the irreducible core (don't chase a sandwich/mod shortcut).** For `M ≤ 5` the
  sandwich suffices (done). For `M ≥ 6`, `four_two_pow_lt_factorial` gives `2^{M+2} < M!`, so the
  sandwich permits `m` up to `~M log M` — it does **not** bound `m ≤ M+2`. And **no fixed modulus
  works**: elements `a ≥ 8` are `≡ 0 (mod 2^7)` so are invisible to any bounded-modulus parity
  argument, yet they blow up the value. Only the odd-part-`1` constraint (`factSum = 2^m`) ties value
  to valuation. Confirmed independently this session: `{6,7,9}` is tied-bottom with `v₂ = 13 > M+2`
  but isn't a power of 2 — the general gap `v₂(factSum) − M` is unbounded; only `=2^m` tames it.
- **The cascade descent (the path to prove the `M ≥ 6` case).** With `a₀ = 2`:
  `2^m = 8 + ∑_{a≥4,a∈S} a!`, i.e. `2^{m-3} = 1 + ∑_{a≥4} a!/8`, where `a!/8` is **odd iff `a∈{4,5}`**.
  Parity forces exactly one of `{4,5}` in `S`, and the equation recurses one pair up with the exponent
  shifted, terminating at `m ≤ M+2` (`{2,3,5} ↦ 2⁷` extremal). Formalizing this finite-depth descent
  needs a **generalized inductive predicate** (the `2^t = carry + ∑ a!/divisor` form changes shape each
  level — you cannot recurse `cascade_two` itself). Likely strong induction on a "tail set." Multi-session.
- **DON'T re-derive the valuation framework** — it's all in `Basic.lean`. `rg` the names first:
  `v2_factorial_succ`, `v2_factorial_lt_of_add_two_le`, `padicValNat_two_factorial`,
  `v2_factSum_of_unique_min`, `unique_min_of_not_tied`, `min'_le_two`, `m_le_max_of_unique_min`,
  `factorial_max_le_factSum`, `factSum_le_two_mul_factorial_max`, `eight_dvd_factorial`.

## ✅ State
- **Build green, verified** this session from real rebuilds: `lake build Erdos403.Basic Erdos403.Sharp`
  → 8250 jobs, "Build completed successfully", one `sorry` warning (the `M ≥ 6` branch of `cascade_two`).
- **Exactly one sorry:** `cascade_two`, the `M ≥ 6` branch (`Basic.lean:323`). `#print axioms` of
  `erdos_403_finite`, `erdos_403_sharp`, `tied_sharp_ceiling`, `cascade_two` all = `propext, sorryAx,
  Classical.choice, Quot.sound`. `not_eight_dvd_factSum_of_mem_012` is **axiom-clean** (no sorryAx).
- 2 commits on `tier1-finiteness` this session: `59c7ccc` (bottom-pin + a₀=0 discharge) and `596180c`
  (scope cascade_two sorry to M≥6). RECONSTRUCTION.md updated.

## 🎬 Next actions
1. **Prove the `M ≥ 6` branch of `cascade_two`.** This is the lost Lin/Frankl estimate — genuinely
   hard, plan for multiple sessions. Formalize the cascade descent (above) as a strong induction over a
   generalized "tail" predicate (the `2^t = carry + ∑ a!/divisor` form). *Or* state that descent as a
   clean ℕ-only termination lemma and hand to **Aristotle** (needs the host — no GitHub/Aristotle egress
   in the box). Good first sub-steps that are clean and reusable: the `/8` reduction
   (`8 ∣ factSum`, then `2^{m-3} = 1 + ∑ a!/8`) and the parity step "exactly one of `{4,5} ∈ S`".
2. If not attacking the kernel: repo is in an excellent stopping state — **host should push
   `tier1-finiteness`** (the box has no GitHub egress; local commits only). Then refresh the master
   `HANDOFF.md` and trash the per-session snapshots.

## ⚠️ Gotchas
- **`lake build` "0 jobs" lie:** a build right after an Edit can report "0 jobs" without recompiling.
  Edits via the tool tick mtime, but if you `touch`/script, confirm a *real job count*.
- **Box OOM:** `lake build`/`lake env lean` intermittently die "Cannot allocate memory" — re-run; `pkill
  -9 lean lake` if wedged.
- **`min'_le`/`le_max'` vs `le_min'`/`max'_le`:** the first pair take `(s)(x)(H2)` (nonempty derived as
  `⟨x,H2⟩`); the second pair take the nonempty **explicitly** — `s.le_min' H x H2`, `s.max'_le H x H2`.
- **`le_or_lt` is absent** in this mathlib build; use `Nat.lt_or_ge`.
- Pre-commit hook prints "Could not locate a lakefile — skipping build gate" (cwd) — harmless; build
  manually before committing. lean-yolo-box: local commits only, host pushes.

## 📁 Key files
- `src/Erdos403/Basic.lean` — the live track: valuation framework + assembly + `tied_sharp_ceiling`
  (proven) + the kernel `cascade_two` (lone sorry, `M ≥ 6`) + `not_eight_dvd_factSum_of_mem_012`
  (new, axiom-clean) + `eight_dvd_factorial` + `erdos_403_finite` + `erdos_403_sharp`.
- `src/Erdos403/Sharp.lean` — FNS track (even-`m` kill, `factSum_ne_of_leading_two`).
- `RECONSTRUCTION.md` — Lin strategy + plan table; **updated this session** (step-5 row + bottom-pinning
  section). `PLAN.md` — FNS map + kernel analysis.
- `HANDOFF-2026-05-31-0357.md` — prior snapshot (this session-5 doc supersedes it).
  `HANDOFF.md` (master) — sessions 1-2 narrative; **don't overwrite.**

---
**→ Next session: start at Next action #1 — prove the `M ≥ 6` branch of `cascade_two` (the irreducible
Lin/Frankl carry cascade), or state that descent for Aristotle. The bottom is fully pinned to `a₀ = 2`
and `M ≥ 6`; everything else is reconstructed and axiom-clean.**
