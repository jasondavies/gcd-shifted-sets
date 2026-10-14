import ShiftedGcd.Defs

/-!
# Theorem 1: large gcd after small shifts

Conditional on Lemma 5 (Baker–Harman), given as the hypothesis `BakerHarman n (kappa n ε)`.

The paper states: for `H ≥ 𝔥(a)^ε` there is `h` with `𝔥(h) ≤ H` and
`gcd(a + h) ≫ 𝔥(h) H^ϑ`. Read literally this is trivial (take `h = 0`). The proof actually
gives a modulus `r ∣ aᵢ + hᵢ` with `r ≫ 𝔥(h) H^ϑ` and also `r ≥ R ≫ H^{1/(εκ)}`. We formalise
this stronger form (`theorem1`). We then derive the gcd form in the range `H < 𝔥(a)`, where
`a + h ≠ 0` automatically (`theorem1_gcd`).

We also check the claims about `κ` made in the introduction. Note that the paper's
"`εκ(n,ε) < 1`" should read `εκ(n,ε) > 1`; that is what makes `ϑ > 0`.
-/

open Finset

namespace ShiftedGcd

/-- Equation (2) has a unique positive solution. -/
theorem kappa_existsUnique {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃! κ, IsKappa n ε κ := by
  sorry

theorem isKappa_kappa {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    IsKappa n ε (kappa n ε) := by
  sorry

theorem one_lt_eps_mul_kappa {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    1 < ε * kappa n ε := by
  sorry

theorem theta_pos {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    0 < theta n ε := by
  sorry

/-- **Theorem 1** (strong form, as actually proved in the paper). -/
theorem theorem1 {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hBH : BakerHarman n (kappa n ε)) :
    ∃ c > 0, ∀ (a : Fin n → ℤ) (H : ℝ), 1 ≤ H → (height a : ℝ) ^ ε ≤ H →
      ∃ h : Fin n → ℤ, (height h : ℝ) ≤ H ∧ ∃ r : ℕ, (∀ i, (r : ℤ) ∣ a i + h i) ∧
        c * height h * H ^ theta n ε ≤ r ∧ c * H ^ (1 / (ε * kappa n ε)) ≤ r := by
  sorry

/-- **Theorem 1** (gcd form): for `𝔥(a)^ε ≤ H < 𝔥(a)` there is a shift `h` with `𝔥(h) ≤ H` and
`gcd(a + h) ≫ 𝔥(h) H^ϑ`, and moreover `gcd(a + h) ≫ H^{1/(εκ)}`. -/
theorem theorem1_gcd {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hBH : BakerHarman n (kappa n ε)) :
    ∃ c > 0, ∀ (a : Fin n → ℤ) (H : ℝ), 1 ≤ H → (height a : ℝ) ^ ε ≤ H → H < height a →
      ∃ h : Fin n → ℤ, (height h : ℝ) ≤ H ∧
        c * height h * H ^ theta n ε ≤ vgcd (a + h) ∧
        c * H ^ (1 / (ε * kappa n ε)) ≤ vgcd (a + h) := by
  sorry

end ShiftedGcd
