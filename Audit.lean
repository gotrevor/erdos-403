import Erdos403.Sharp

-- Independent audit of the trusted base for Erdős #403.
-- Build this file and read the axiom lists below.
-- A SOLID proof shows ONLY: propext, Classical.choice, Quot.sound.
-- This proof is fully kernel-pure: no native_decide compiler-trust axiom
-- (Lean.ofReduceBool / Lean.trustCompiler) and no sorryAx. Anything beyond
-- the standard three (e.g. sorryAx, an `axiom` we declared) is a red flag.

#print axioms Erdos403.erdos_403_finite
#print axioms Erdos403.erdos_403_sharp
