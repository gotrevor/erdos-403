# Erdős Problem #403 — moved to lean-gallery ➡️

This repository held a complete, kernel-pure Lean 4 formalization of
[Erdős problem #403](https://www.erdosproblems.com/403): only finitely many powers of two are sums
of distinct factorials, and the largest is `2⁷ = 2! + 3! + 5!`.

**It now lives in [gotrevor/lean-gallery](https://github.com/gotrevor/lean-gallery).**

| What | Where |
|---|---|
| The Lean proof | [`LeanGallery/NumberTheory/Erdos403/`](https://github.com/gotrevor/lean-gallery/tree/main/LeanGallery/NumberTheory/Erdos403) |
| The headline theorems | `LeanGallery.NumberTheory.Erdos403.erdos_403_finite` and `…erdos_403_sharp` |
| How the proof works, the literature findings, the development record | [`docs/Erdos403/`](https://github.com/gotrevor/lean-gallery/tree/main/docs/Erdos403) |

Everything that was here moved there, including the session-by-session handoffs. Nothing was
dropped, and this repository's git history remains the original record.

## Why move it

In the gallery the result is **maintained and independently checkable**, which it was not here:

- it builds against current Mathlib (this repo was pinned to an old toolchain and would eventually
  stop compiling, which reads to a visitor as a broken formalization);
- CI gates it on `#print axioms` asserting the exact triple `[propext, Classical.choice, Quot.sound]`
  — no `sorry`, no `native_decide`, no custom axioms;
- [`comparator`](https://github.com/leanprover/comparator) verifies the statements against a
  Mathlib-only rendering, replaying the proofs through the Lean kernel **and** the independent
  [`nanoda`](https://github.com/ammkrn/nanoda_lib) kernel inside a sandbox — so a stranger can check
  the result without trusting, or running, this author's code.

## Why the repo is still here

The URL is stable, and its git history holds the full development record including the route that
did not work. Both are worth more than the disk they occupy.

## License

Apache License 2.0 — see [`LICENSE`](LICENSE).
