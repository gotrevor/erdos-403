import Erdos403.Sharp

-- Independent audit of the trusted base for Erdős #403.
-- Build this file and read the axiom lists below.
-- A SOLID proof shows ONLY: propext, Classical.choice, Quot.sound,
-- plus Lean.ofReduceBool / Lean.trustCompiler (the native_decide compiler-trust).
-- Anything else (e.g. sorryAx, an `axiom` we declared) is a red flag.

#print axioms Erdos403.erdos_403_finite
#print axioms Erdos403.erdos_403_sharp
