import Mathlib

/-!
# Definitions for "On the Greatest Common Divisor of Shifted Sets"

Formalisation of R. Heyman and I. E. Shparlinski, *On the greatest common divisor of shifted
sets*, arXiv:1402.1208 (J. Number Theory 154 (2015), 63–73).

Vectors `a ∈ ℤⁿ` are functions `Fin n → ℤ`; `a + h` is the pointwise sum.
-/

open Finset

namespace ShiftedGcd

variable {n : ℕ}

/-- The height `𝔥(x) = max |xᵢ|` of an integer vector (`0` for the empty vector). -/
def height (x : Fin n → ℤ) : ℕ := univ.sup fun i => (x i).natAbs

/-- `gcd(x) = gcd(x₁, …, xₙ)`, with the convention `gcd(0, …, 0) = 0`. -/
def vgcd (x : Fin n → ℤ) : ℕ := univ.gcd fun i => (x i).natAbs

/-- The dot product `a · x = ∑ aᵢ xᵢ`. -/
def dot (a x : Fin n → ℤ) : ℤ := ∑ i, a i * x i

/-- `‖ξ‖`: the distance from a real number to the nearest integer. -/
noncomputable def distNearestInt (ξ : ℝ) : ℝ := |ξ - round ξ|

/-! ### Theorem 1 -/

/-- The Baker–Harman exponent `γ(K) = 1 / (2^{2 + max{1,K}} - 4)`. -/
noncomputable def gammaBH (K : ℝ) : ℝ := 1 / ((2 : ℝ) ^ (2 + max 1 K) - 4)

/-- `κ` solves equation (2): `n(εκ - 1)/(n - 1) = γ(κ)`, `κ > 0`. -/
def IsKappa (n : ℕ) (ε κ : ℝ) : Prop :=
  0 < κ ∧ (n : ℝ) * (ε * κ - 1) / ((n : ℝ) - 1) = gammaBH κ

open Classical in
/-- `κ(n, ε)`: the unique positive solution of (2) (junk value `0` if there is none; for
`n ≥ 2` and `0 < ε < 1` existence and uniqueness are proved in `ShiftedGcd.Theorem1`). -/
noncomputable def kappa (n : ℕ) (ε : ℝ) : ℝ :=
  if h : ∃ κ, IsKappa n ε κ then h.choose else 0

/-- `ϑ(n, ε) = (1 - 1/(εκ(n,ε))) / (n - 1)`. -/
noncomputable def theta (n : ℕ) (ε : ℝ) : ℝ := (1 - 1 / (ε * kappa n ε)) / ((n : ℝ) - 1)

/-- **Lemma 5** (Baker–Harman, Math. Z. 221 (1996), Theorem 1), for dimension `n` and exponent
`K`, exactly as quoted in the paper. This deep result is not proved here; it is taken as a
hypothesis of Theorem 1. To keep the hypothesis as weak as possible all constants are
existentially quantified, "sufficiently large `Q` and `R`" is `C₁ ≤ Q`, `R₀ ≤ R`, and the vector
is required to have positive entries. -/
def BakerHarman (n : ℕ) (K : ℝ) : Prop :=
  ∃ C₁ c₂ R₀ : ℝ, 0 < c₂ ∧
    ∀ (a : Fin n → ℕ), (∀ i, 0 < a i) → ∀ Q R : ℝ, R₀ ≤ R →
      Real.sqrt (∑ i, ((a i : ℝ)) ^ 2) ≤ R ^ K → C₁ ≤ Q → Q ≤ R ^ gammaBH K →
      ∀ ψ : Fin n → ℝ, (∀ i, 0 < ψ i) → (∀ i, ψ i ≤ c₂ * (Real.log Q)⁻¹ ^ n) →
        ∏ i, ψ i = Q⁻¹ →
        ∃ r : ℕ, R ≤ r ∧ (r : ℝ) ≤ 2 * Q * R ∧ ∀ i, distNearestInt ((a i : ℝ) / r) ≤ ψ i

/-! ### Theorem 2 -/

/-- The entries of `x` are pairwise coprime. -/
def PairwiseCoprimeVec (x : Fin n → ℤ) : Prop := ∀ i j, i ≠ j → Int.gcd (x i) (x j) = 1

/-- `L(a)`: the smallest `H` such that `𝔥(h) = H` for some `h` with `a + h` pairwise coprime. -/
noncomputable def L (a : Fin n → ℤ) : ℕ :=
  sInf {H | ∃ h : Fin n → ℤ, height h = H ∧ PairwiseCoprimeVec (a + h)}

/-- **Lemma 6** (Iwaniec, *On the problem of Jacobsthal*, 1978): if `m` consecutive integers are
each divisible by one of `r ≥ 2` given primes, then `m ≪ (r log r)²`. This deep result is not
proved here; it is taken as a hypothesis of Theorem 2. -/
def IwaniecBound : Prop :=
  ∃ C : ℝ, ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → 2 ≤ S.card →
    ∀ (x : ℤ) (m : ℕ), (∀ k < m, ∃ p ∈ S, (p : ℤ) ∣ x + k) →
      (m : ℝ) ≤ C * ((S.card : ℝ) * Real.log S.card) ^ 2

/-! ### Theorem 3 -/

/-- `ℓ(a)`: the smallest `H` such that `𝔥(h) = H` for some `h` with `gcd(a + h) = 1`. -/
noncomputable def ell (a : Fin n → ℤ) : ℕ :=
  sInf {H | ∃ h : Fin n → ℤ, height h = H ∧ vgcd (a + h) = 1}

/-! ### Theorem 4 -/

/-- Vectors in `ℤⁿ` with positive components and height at most `h`. -/
def boxVecs (n h : ℕ) : Finset (Fin n → ℤ) := Fintype.piFinset fun _ => Icc (1 : ℤ) h

/-- `R(a, h)`: the number of pairs `x, y ∈ ℤⁿ` with positive components and height `≤ h` with
`gcd(a) = gcd(a · x, a · y)`. -/
def R (a : Fin n → ℤ) (h : ℕ) : ℕ :=
  ((boxVecs n h ×ˢ boxVecs n h).filter fun p => vgcd a = Int.gcd (dot a p.1) (dot a p.2)).card

end ShiftedGcd
