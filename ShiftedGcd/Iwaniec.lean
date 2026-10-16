import ShiftedGcd.Defs
import IwaniecLinearSieve.Jacobsthal

/-!
# Iwaniec's interval bound

Lemma 6 of the paper is Iwaniec's theorem on Jacobsthal's problem
(H. Iwaniec, *On the problem of Jacobsthal*, Demonstratio Math. 11 (1978)), proved in the
`iwaniec-linear-sieve` library from his linear sieve at the sifting limit and the prime number
theorem with de la Vallée Poussin error term.
-/

namespace ShiftedGcd

/-- The interval-covering bound used in Theorem 2 and the uniform-shift theorem. -/
theorem iwaniecBound : IwaniecBound :=
  IwaniecLinearSieve.iwaniecBound

end ShiftedGcd
