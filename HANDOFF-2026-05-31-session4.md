# Handoff: Erdős #403 — ONE kernel left (`tied_sharp_ceiling`)

**Date**: 2026-05-31 (session 4, final) · **Branch**: `tier1-finiteness` · **HEAD** ≈ `c77caab`+docs

## 🎯 Status — both headlines reduce to a single `sorry`
`~/src/erdos-403` proves Erdős #403. **Sorry count is now 1** (was 2). Both
`erdos_403_finite` *and* `erdos_403_sharp` (`m ≤ 7`) reduce to the lone kernel **`tied_sharp_ceiling`**
(`Basic.lean:269`). `#print axioms` of both headlines = `propext, sorryAx, Classical.choice,
Quot.sound`. Build green (`lake build` → 8248 jobs, verified). C-7a (`factSum_ne_of_leading_two`,
Sharp.lean) is fully axiom-clean (no sorryAx).

## 🔑 The one kernel
```
theorem tied_sharp_ceiling (S : Finset ℕ) (h : S.Nonempty) (m : ℕ)
    (he : Even (S.min' h)) (hmem : S.min' h + 1 ∈ S) (hpow : factSum S = 2 ^ m) :
    m ≤ S.max' h + 2
```
"A power-of-two factorial sum with a *tied* bottom pair exceeds its top index by at most 2." Explicit
`B = 2`. Everything else is proven *from* it:
- `tied_carry_ceiling` = `⟨2, tied_sharp_ceiling⟩` → feeds `carry_ceiling` → `erdos_403_finite`.
- `erdos_403_sharp`: unique-min case `m ≤ 3` (`sharp_of_unique_min`, unconditional); tied case
  `m ≤ M+2` (kernel) + sandwich `M! ≤ 2^m ≤ 2^{M+2}` + `four_two_pow_lt_factorial` (`2^{M+2}<M!` for
  `M≥6`) ⟹ `M ≤ 5` ⟹ `m ≤ 7`. No factorial-base / `decide` needed.

## 🧠 Context to carry forward
- **`B = 2` is sharp; the constraint is essential.** Exhaustive: every power-of-two factorial sum has
  `m − max'S ≤ 2` (extremal `{2,3,5}↦2⁷`). The *general* gap `v₂(factSum S) − max'S` is **unbounded**
  (`{2ᵗ−2,2ᵗ−1,2ᵗ+1}` → gap `2t−2`: `{6,7,9}`→4, `{14,15,17}`→6, `{30,31,33}`→8). So no constant `B`
  works without `factSum = 2^m`. Carry jumps are set by *odd-part ratios* of factorials
  (`oddpart(9!)/oddpart(6!·7!)=2835/45=63=2⁶−1` → +6). This is *why* it's Lin's hard estimate.
- **Bottom is pinned.** `min'_le_two` (proven) + tied (even min) ⟹ `min'S ∈ {0,2}`. The `a₀=0` case
  reduces to `a₀=2` (via `0!+1!=2!` twin; the `{0,1,2}⊆S` sub-case dies by a mod-8 parity: for `m≥3`,
  `4+6·[3∈S] ≢ 0 mod 8`). So the live core is **`a₀=2`, `{2,3}⊆S`, bottom `= 8`.**
- **Concrete cascade (the proof strategy for the kernel).** For `a₀=2`: `2^m = 8 + ∑_{a≥4,a∈S}a!`;
  divide by 8: `2^{m-3} = 1 + ∑_{a≥4} a!/8`, and `a!/8` is *odd* iff `a∈{4,5}` (=3,15), even for
  `a≥6`. Parity ⟹ **exactly one of `{4,5}` in S**, and the equation *recurses one pair up* with the
  target exponent shifted: take `4` → `2^{m-5}=1+∑_{a≥6}a!/32` (advance 2 levels); take `5` →
  `2^{m-7}=1+∑_{a≥6}a!/128` (jump). Each step consumes the pair `{2j,2j+1}` and decreases the target;
  it terminates when S is exhausted, at `m ≤ max'S + 2`. **Formalizing this finite-depth descent is
  the kernel** — it IS Lin's argument. Likely a strong induction on a "tail set"; multi-session.
- **DON'T** chase a crude/general bound (additive is false; multiplicative `v₂ ≤ C·M` is true but
  still needs the cascade — the size sandwich alone only gives the useless `v₂ ≤ log₂M! ≈ M log M`).
  **DON'T** re-derive the valuation framework — it's all in `Basic.lean` (`v2_factorial_*`,
  `padicValNat_two_factorial`, `v2_factSum_of_unique_min`, `min'_le_two`).

## 🎬 Next actions
1. **Prove `tied_sharp_ceiling`** (the only sorry). Reduce to `a₀=2` (twin + mod-8), then formalize
   the cascade descent above as strong induction. This is the lost Lin/Frankl estimate — genuinely
   hard, multi-session. Clean self-contained pure-`ℕ` target → good **Aristotle** candidate
   (no powers of two visible once stated as the cascade-termination lemma).
2. If not attacking the kernel: the repo is in an excellent stopping state — 1 sorry, both headlines
   wired, axiom-clean otherwise. Host should push `tier1-finiteness` (box can't push).

## ⚠️ Gotchas
- **Box OOM / `lake build` "0 jobs" lie**: a build right after an Edit can report "0 jobs" if mtime
  didn't tick — `touch` the file or `lake build Erdos403.Basic` and confirm a real job count + "Built".
- **omega + nested div/mod**: materialize the quotient (`obtain ⟨q,hq⟩ : ∃q, N=24*q+16`).
- Pre-commit hook prints "Could not locate a lakefile — skipping build gate" — harmless; build manually.
- lean-yolo-box: local commits only, **host pushes**. Leave on `tier1-finiteness`.

## 📁 Key files
- `src/Erdos403/Basic.lean` — the live track: valuation framework + assembly + the **one kernel**
  (`tied_sharp_ceiling`, L269) + `erdos_403_finite` + `erdos_403_sharp`.
- `src/Erdos403/Sharp.lean` — FNS track (even-`m` kill, C-7a `factSum_ne_of_leading_two`); parallel,
  its C-7b residual = the same kernel.
- `src/Erdos403/FactBase.lean` — factorial-number-system engine (Phase A); not needed for sharp now.
- `RECONSTRUCTION.md` — Lin strategy + plan table (steps 1–7 status). `PLAN.md` — FNS map + kernel
  analysis. **Read both.**

---
**→ Next session: ONE sorry (`tied_sharp_ceiling`). Either formalize the cascade descent (the Lin
kernel, multi-session) or hand it to Aristotle. The whole problem is now this single clean lemma.**
