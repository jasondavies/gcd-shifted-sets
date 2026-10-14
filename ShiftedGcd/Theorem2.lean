import ShiftedGcd.Defs

/-!
# Theorem 2: small shifts making a vector pairwise coprime

Conditional on Lemma 6 (Iwaniec's bound for the Jacobsthal function), given as the hypothesis
`IwaniecBound`.

The bound `L(a) ≪ log² 𝔥(a)` needs `𝔥(a) ≥ 2`: for `a = 0 ∈ ℤ²` we have `L(a) = 1`. The implied
constant depends on `n`.

The paper's construction (`h₁ = 0`, then each `hᵢ ≥ 0` minimal with `aᵢ + hᵢ` coprime to
`∏_{j<i} (aⱼ + hⱼ)`) needs a small repair when some `aⱼ + hⱼ = 0`. The shifted entries must be
kept nonzero.
-/

open Finset

namespace ShiftedGcd

/-- **Theorem 2** (existence form). -/
theorem theorem2 (hI : IwaniecBound) (n : ℕ) :
    ∃ C : ℝ, ∀ a : Fin n → ℤ, 2 ≤ height a →
      ∃ h : Fin n → ℤ, PairwiseCoprimeVec (a + h) ∧
        (height h : ℝ) ≤ C * Real.log (height a) ^ 2 := by
  sorry

/-- **Theorem 2**: `L(a) ≪ log² 𝔥(a)`. -/
theorem theorem2_L (hI : IwaniecBound) (n : ℕ) :
    ∃ C : ℝ, ∀ a : Fin n → ℤ, 2 ≤ height a → (L a : ℝ) ≤ C * Real.log (height a) ^ 2 := by
  sorry

end ShiftedGcd
