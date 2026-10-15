import ShiftedGcd.Defs
import OAI.NumberTheory.Jacobsthal.Conclusions.QuadraticBound

/-!
# Iwaniec's interval bound from a quadratic Jacobsthal bound

The imported theorem is the quadratic bound from `openai/math`, pinned and vendored with
its dependencies in `vendor/jacobsthal`. For a set of `r ≥ 2` primes, the stronger `O(r²)`
bound implies the paper's `O((r log r)²)` interval-covering statement.
-/

open Finset
namespace ShiftedGcd

/-- A quadratic Jacobsthal bound implies the interval-covering form of Iwaniec's bound. -/
theorem iwaniecBound_of_jacobsthalQuadratic
    (h : OAI.Erdos970.NumberTheoryLean.Targets.JacobsthalQuadratic) : IwaniecBound := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨4 * C, ?_⟩
  intro S hS hcard x m hcover
  obtain ⟨M, hM, hMC⟩ := h S.card (by omega)
  have hN : 0 < ∏ p ∈ S, p := Finset.prod_pos (fun p hp => (hS p hp).pos)
  obtain ⟨i, hi, hcop⟩ := hM (∏ p ∈ S, p) hN (by rw [Nat.primeFactors_prod hS]) x
  have hm : m < M := by
    by_contra! hle
    obtain ⟨p, hp, hpi⟩ := hcover i (hi.trans_le hle)
    have hpN : p ∣ ∏ q ∈ S, q := Finset.dvd_prod_of_mem (fun q => q) hp
    have hpa : p ∣ (x + i).natAbs := Int.natCast_dvd.1 hpi
    have : p ∣ 1 := by
      simpa [hcop.gcd_eq_one] using Nat.dvd_gcd hpa hpN
    exact (hS p hp).ne_one (Nat.dvd_one.mp this)
  have hcardR : (2 : ℝ) ≤ S.card := by exact_mod_cast hcard
  have hlog : (1 : ℝ) / 2 ≤ Real.log S.card := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hcardR
    have := Real.log_two_gt_d9
    linarith
  have hsq : (S.card : ℝ) ^ 2 ≤ 4 * ((S.card : ℝ) * Real.log S.card) ^ 2 := by
    have h : (S.card : ℝ) ≤ 2 * ((S.card : ℝ) * Real.log S.card) := by
      nlinarith
    nlinarith [sq_nonneg ((S.card : ℝ) * Real.log S.card)]
  calc
    (m : ℝ) ≤ M := by exact_mod_cast hm.le
    _ ≤ C * (S.card : ℝ) ^ 2 := hMC
    _ ≤ 4 * C * ((S.card : ℝ) * Real.log S.card) ^ 2 := by nlinarith

/-- The interval-covering bound used in Theorem 2 and the uniform-shift theorem. -/
theorem iwaniecBound : IwaniecBound :=
  iwaniecBound_of_jacobsthalQuadratic OAI.Erdos970.Erdos970Final.erdos_970_quadratic

end ShiftedGcd
