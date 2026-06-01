# Erdős Problem #403 in Lean 4 🔢

A complete, **kernel-pure** Lean 4 formalization of [Erdős problem #403](https://www.erdosproblems.com/403).

## The problem

> Write `2^m = a₁! + a₂! + ⋯ + aₖ!` as a sum of **distinct** factorials (`a₁ < a₂ < ⋯ < aₖ`).
> Erdős (attributed to Burr–Erdős [ErGr80, p.79]) asks: this has only **finitely many** solutions,
> and the largest is `2⁷ = 2! + 3! + 5!`.

## What is proven

Both headline theorems live in [`src/Erdos403/Sharp.lean`](src/Erdos403/Sharp.lean) and are **fully
`sorry`-free**:

```lean
-- Finiteness (Erdős's question, "Tier 1"):
theorem Erdos403.erdos_403_finite : {S : Finset ℕ | ∃ m, factSum S = 2 ^ m}.Finite

-- Sharp bound ("Tier 2", the "largest is 2⁷"):
theorem Erdos403.erdos_403_sharp : factSum S = 2 ^ m → m ≤ 7
```

where `factSum S = ∑ a ∈ S, a!` (a `Finset ℕ` of indices gives distinct factorials automatically;
note `0! = 1! = 1`). The witness `factSum {2,3,5} = 2⁷` is verified, and `2⁷` is attained, so the
bound is sharp.

### Kernel-pure 🔒

`#print axioms` for both theorems shows **exactly**:

```
[propext, Classical.choice, Quot.sound]
```

No `sorryAx`, and **no `native_decide`** (no `Lean.ofReduceBool` / compiler-trust axiom). The proof
passes `lean4checker` and is mathlib-admissible. See [`Audit.lean`](Audit.lean) to reproduce the
check, and [`SOLVED.md`](SOLVED.md) for the trust-elimination story (`native_decide` was eliminated
in a `7 → 3 → 2 → 0` axiom pass).

## How it works (one paragraph)

The whole problem reduces to: *for every `m ≥ 8`, `2^m` is not a sum of distinct factorials.* In the
factorial number system, "`n` is a sum of distinct factorials" ⟺ "every digit
`factDigit i n = (n / i!) % (i+1)` is `≤ 1`." The key fact is that for every `m ≥ 8`, both `2^m` and
`2^m − 1` have an FNS digit `≥ 2` at some index `≤ 11`. Because `factDigit i n` for `i ≤ 11` depends
only on `n mod 12!`, and `2^m mod 12!` is periodic in `m` with period 1620, this is a **finite
check over one period**, done by a kernel-pure `decide` over a residue fold. Full writeup:
[`SOLVED.md`](SOLVED.md) and [`RECONSTRUCTION.md`](RECONSTRUCTION.md).

## Build & verify

```bash
lake exe cache get          # prebuilt mathlib oleans
lake build Erdos403.Sharp   # builds the proof (~8250 jobs)
lake env lean Audit.lean    # prints the axiom lists for both theorems
```

Lean toolchain `v4.29.1`, mathlib `v4.29.1` (pinned in `lean-toolchain` / `lake-manifest.json`).

## Repo layout

| Path | Contents |
|------|----------|
| `src/Erdos403/Basic.lean`   | `factSum`, the `witness`, the size sandwich |
| `src/Erdos403/FactBase.lean`| factorial-number-system digit infrastructure (`factDigit`) |
| `src/Erdos403/Sharp.lean`   | the fixed-modulus kill + both headline theorems |
| `src/Erdos403/Superseded.lean`| earlier, unused 2-adic approach + FNS reconstruction lemmas (not part of the proof) |
| `Audit.lean`                | `#print axioms` regression check |
| `SOLVED.md`                 | how the proof works + the kernel-purity journey |
| `RECONSTRUCTION.md`         | the full reconstructed argument |
| `LITERATURE-FINDINGS.md`    | why the original proofs are lost (see below) |
| `history/`                  | session-by-session development handoffs (kept as a record) |

## Provenance & honesty 📝

The original proofs are **lost by construction** — [Lin (1976)] is an unpublished Bell Labs internal
memorandum and [Frankl (1976)] was a personal communication; neither was ever written for
publication, and no source reproduces the argument. So this is a **reconstruction**, not a
transcription. (Pleasingly, that Shen Lin is the Busy-Beaver Lin–Rado / Lin–Kernighan one.) Notably,
the reconstruction did **not** need the lost carry estimate: a fixed modulus `12!` closes the
power-of-two case. See [`LITERATURE-FINDINGS.md`](LITERATURE-FINDINGS.md).

This formalization was produced by Trevor Morris with Claude Code (Anthropic), following
[Mathlib's AI-usage conventions](https://leanprover-community.github.io/contribute/index.html).

## License

Apache License 2.0 — see [`LICENSE`](LICENSE).
