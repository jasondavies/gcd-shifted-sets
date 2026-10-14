import ShiftedGcd.Defs

/-!
# Theorem 4: gcd of random linear combinations

Unconditional. The `(h 𝔥(a))^{o(1)}` factor is formalised in its usual uniform sense. For
every `δ > 0` the bound holds with factor `(h 𝔥(a))^δ` and a constant depending only on
`n` and `δ`.

Corrections to the paper's argument:
* The identity `R(a,h) = ∑_d μ(d) U_d(a,h)²` fails when `a · x = 0` has solutions with
  positive `x`, which can happen when `a` has entries of both signs. Those `x` must be
  discarded first; they contribute only `O(h^{2n-1})` pairs.
* In (14), `D^{2n-1}` should be `D^{n-1}`.
* In the evaluation of `M`, the tail term is `O(n/h)`, not `O(D⁻¹)`.
-/

open Finset

namespace ShiftedGcd

/-- **Theorem 4**. -/
theorem theorem4 {n : ℕ} (hn : 2 ≤ n) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ a : Fin n → ℤ, a ≠ 0 → ∀ h : ℕ, 1 ≤ h →
      |(R a h : ℝ) - (riemannZeta 2).re⁻¹ * (h : ℝ) ^ (2 * n)| ≤
        C * (h : ℝ) ^ ((2 * n : ℝ) - n / (n ^ 2 - n + 1)) * ((h : ℝ) * height a) ^ δ := by
  sorry

end ShiftedGcd
