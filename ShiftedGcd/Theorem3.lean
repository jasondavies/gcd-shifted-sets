import ShiftedGcd.Defs

/-!
# Theorem 3: vectors that need large shifts to become coprime

Unconditional. The construction uses the Chinese Remainder Theorem together with Chebyshev's
lower bound for `π(x)`.

The congruences in the paper should read `a_k ≡ -i_k (mod p_{i₁,…,iₙ})`, not `+i_k`.
-/

open Finset

namespace ShiftedGcd

/-- **Theorem 3**. There are vectors `a` of arbitrarily large height such that every `h` with
`gcd(a + h) = 1` has `𝔥(h) ≫ (log 𝔥(a) / log log 𝔥(a))^{1/n}`. -/
theorem theorem3 {n : ℕ} (hn : 1 ≤ n) :
    ∃ c > 0, ∀ N : ℕ, ∃ a : Fin n → ℤ, N ≤ height a ∧
      ∀ h : Fin n → ℤ, vgcd (a + h) = 1 →
        c * (Real.log (height a) / Real.log (Real.log (height a))) ^ ((1 : ℝ) / n) ≤
          height h := by
  sorry

/-- **Theorem 3**: `ℓ(a) ≫ (log 𝔥(a) / log log 𝔥(a))^{1/n}` for infinitely many `a`. -/
theorem theorem3_ell {n : ℕ} (hn : 1 ≤ n) :
    ∃ c > 0, Set.Infinite {a : Fin n → ℤ |
      c * (Real.log (height a) / Real.log (Real.log (height a))) ^ ((1 : ℝ) / n) ≤ ell a} := by
  sorry

end ShiftedGcd
