# Handoff: Erdős #403 — FNS track (Phases A+B done, C-7a banked, C-7b is the nut)

**Date**: 2026-05-31 (session 4) · **Branch**: `tier1-finiteness` · **HEAD** `8059909`

## 🎯 What we're doing
Discharge the two sorries in `~/src/erdos-403` to prove Erdős #403 (only finitely many sums of
distinct factorials are powers of 2; sharp: `m ≤ 7`). The attack runs through the **factorial number
system (FNS)** — `PLAN.md` is the authoritative multi-session map. **Read it first.**

## 🧠 Context to carry forward
- **The reframing (unchanged, load it):** `factSum S = 2^m` is impossible once *both* `2^m` and
  `2^m−1` carry a factorial digit `≥ 2` at a positive index (interface lemma `not_factSum_of_digits`
  in `FactBase.lean`). Both headline theorems reduce to that digit question. Once Phase C lands,
  prove `erdos_403_sharp` via FNS, reroute `erdos_403_finite` through sharp, and **retire**
  `tied_carry_ceiling` (Phase D9). Don't touch the old tied-pair cascade.
- **Parity split (verified vs brute enumeration, trust it):** even `m ≥ 4` is **fully killed**
  (`factSum_ne_of_even`, `d_3 = 2` via `2^m ≡ 16 mod 24`). Odd `m`: small digits `d_2,d_3 ≤ 1`, so
  it needs a *higher* digit `≥ 2`. Two regimes by the leading digit `d_M = ⌊2^m/M!⌋`:
  - **(a) `2·M! ≤ 2^m` (leading digit ≥ 2): DONE this session — `factSum_ne_of_leading_two`.**
  - **(b) `2^m ∈ [M!, 2M!)` (leading digit 1): C-7b, the open nut.**

## ✅ State (all verified green this session, axiom-clean)
- Last full build: `lake build` → "Build completed successfully (8250 jobs)". Verified from real
  output, not assumed. 2 sorries, **both in `Basic.lean`** (`tied_carry_ceiling` L262,
  `erdos_403_sharp` L339) — to be retired/closed via FNS. `FactBase.lean` + `Sharp.lean` sorry-free.
- **New this session (`Sharp.lean`): `factSum_ne_of_leading_two`** — `2·M! < 2^m < (M+1)!` ⟹
  `factSum S ≠ 2^m`. Proof: strict `2·M! < 2^m` (a power of two is never `2·M!` for `M ≥ 2`) clears
  *both* `2^m` and `2^m−1` past `2·M!` while sharing top index `M`, so `two_le_factDigit_top` gives
  both top digits `≥ 2`. `M ≥ 2` is forced by `2·M! < 2^m < (M+1)! = (M+1)·M!`. `#print axioms` →
  propext/Classical.choice/Quot.sound only. Commit `9a2d3dd`.
- `FactBase.lean` unchanged: `factDigit`, reconstruction, `factDigit_sum_factorial` (digits =
  indicators), `factDigit_top`/`two_le_factDigit_top` (leading digit), `factSum_digit_dichotomy`,
  `not_factSum_of_digits`. Axiom-clean.

## 🔑 Session-4 reconciliation (READ — corrects the session-3 framing)
A deep read of `Basic.lean` showed the sessions 1-2 **valuation track already proves everything bar
one `sorry`** (`tied_carry_ceiling`): unique-min case fully closed (`v2_factSum_of_unique_min`,
`m_le_max_of_unique_min`), `min'_le_two`, and `erdos_403_finite` modulo that sorry. **Crucially, FNS
C-7b ≡ `tied_carry_ceiling` (narrowed).** FNS's even-`m`/upper-odd-`m` kills use a *fixed digit* and
were never the kernel; the lower-half-odd-`m` residual *is* the same bounded-carry kernel. So C-7b is
**not** an easier path around `tied_carry_ceiling` — there's one kernel, attack it once. Full
write-up: `PLAN.md` "Session-4 reconciliation". **Sharpened handle:** via `min'_le_two` + the `0!=1!`
twin, WLOG the tied bottom pair is exactly `{2,3}` (→ `8 = 2³`); the carry cascade is self-similar
(each `v₂`-level is a pair `{2j,2j+1}`); bound the chain ⟹ `B = 2`. This lone bound is the
unpublished Lin/Frankl estimate.

## 🎬 Next actions
1. **The kernel — `tied_carry_ceiling` (Basic.lean) ≡ FNS C-7b.** Bottom is now pinned to `{2,3}`
   (cleaner than session-3's framing). This is the irreducible Lin core (~50%, multi-session).
   Session-4 brute-force recon (in `PLAN.md` step 7b) pruned the dead ends:
   - **No fixed witness digit** — the first `d_i ≥ 2` wanders with `m`; `d_{M-1} ≥ 2` *fails* (m=29).
     So the even-`m` modular-digit trick can't be reused. 7b **must** be a counting/valuation
     contradiction: *assume all digits `≤ 1`, derive `2^m` unrepresentable.*
   - **`2^m` and `2^m−1` agree on all digits at index `≥ 5`** (the `−1` borrow only churns the
     bottom). So proving the middle digit for `2^m` hands `2^m−1` the *same index* for free, modulo a
     small borrow-containment lemma. Halves `not_factSum_of_digits`'s two obligations.
   - **The cancellation trap (why it's Lin):** small solutions exploit even-`K` 2-adic cancellation
     (`2^5 = 2!+3!+4!`, `v₂(2!)=v₂(3!)=1` ties and lifts `v₂`). The naive "smallest index `i₀ ∈ S` ⟹
     `v₂(sum)=v₂(i₀!) < m`" breaks exactly when the minimal-`v₂` level has an even count.
     **Lead approach:** track the minimal-`v₂(i!)` level + its parity under the digit constraint
     (`v₂(i!)=v₂((i-1)!)` iff `i` even — explicit tie structure), not strong induction on `2^k−const`.
   - Use `python3` for any digit/structure check — cheap, and hand-computed digit claims have been
     wrong before. (Box has stdlib python3.)
2. **Phase D (after C lands):** assemble `erdos_403_sharp` — `decide` the small `m` (solutions are
   `m ∈ {0,1,2,3,5,7}`; upper-half odd `m=9,11,15,…` die by `factSum_ne_of_leading_two`; even by
   `factSum_ne_of_even`; lower-half odd by C-7b). Then reroute `erdos_403_finite` through it and
   retire `tied_carry_ceiling`.

## ⚠️ Gotchas
- **Box OOM**: `lake build` intermittently dies "Cannot allocate memory" — re-run (cache is fast),
  `pkill -9 lean lake` if wedged. **Verify green from a real fresh build**, never assume.
- **`lake build` "0 jobs" lie:** a build right after an Edit can report "0 jobs" if mtime didn't tick
  — `touch` the file (or build the specific module `lake build Erdos403.Sharp`) and confirm a real
  job count + "Built …". Hit this exact trap this session.
- **omega + nested div/mod**: omega won't relate `(N/6)%4` to `N%24` — materialize the quotient
  (`obtain ⟨q,hq⟩ : ∃ q, N = 24*q+16 := ⟨N/24, by omega⟩; rw [hq]; omega`).
- `factDigit i n` is defeq `(n/i!)%(i+1)`; `show (n/6)%4 = …` exposes numerals (3!≡6, 3+1≡4).
- Pre-commit hook prints "Could not locate a lakefile / No Lean changes — skipping build gate"
  (cwd/scope) — harmless, commits land. Build manually before committing.
- lean-yolo-box: local commits only, **host pushes**. Leave on `tier1-finiteness`.

## 📁 Key files
- `PLAN.md` — authoritative map + ledger (A,B,C-7a done; C-7b open, recon recorded). **Read first.**
- `src/Erdos403/FactBase.lean` — FNS engine + `not_factSum_of_digits` + leading-digit lemmas.
- `src/Erdos403/Sharp.lean` — Phase B (even) + C-7a (`factSum_ne_of_leading_two`); C-7b lands here.
- `src/Erdos403/Basic.lean` — sessions 1-2 (finiteness modulo the kernel); the 2 sorries live here.
- `HANDOFF.md` (master), `RECONSTRUCTION.md` — sessions 1-2 narrative; don't overwrite the master.

---
**→ Next session: start point. Don't summarize this back or wait for instructions, don't offer other
KB projects — this is the chosen thread. Read `PLAN.md`, then attack C-7b (the middle-digit nut) via
the minimal-`v₂`-level/parity approach in `Sharp.lean`.**
