import Mathlib

/-!
# The divisor bound `τ(m) ≪_δ m^δ`

For every `δ > 0` there is a constant `C` with `#m.divisors ≤ C * m ^ δ` for all `m ≥ 1`.
-/

open Finset

namespace ShiftedGcd

/-- `e + 1 ≤ K * 2 ^ (δ e)` with `K = max 1 (1 / (δ log 2))`. -/
lemma add_one_le_mul_two_rpow {δ : ℝ} (hδ : 0 < δ) (e : ℕ) :
    (e : ℝ) + 1 ≤ max 1 (1 / (δ * Real.log 2)) * (2 : ℝ) ^ (δ * e) := by
  have hc : 0 < δ * Real.log 2 := mul_pos hδ (Real.log_pos one_lt_two)
  have he : (0 : ℝ) ≤ e := e.cast_nonneg
  have h2 : 1 + δ * Real.log 2 * e ≤ (2 : ℝ) ^ (δ * e) := by
    rw [Real.rpow_def_of_pos two_pos]
    have := Real.add_one_le_exp (Real.log 2 * (δ * e))
    linarith [show Real.log 2 * (δ * e) = δ * Real.log 2 * e by ring]
  rcases le_total 1 (δ * Real.log 2) with h | h
  · calc (e : ℝ) + 1 ≤ 1 + δ * Real.log 2 * e := by nlinarith
      _ ≤ (2 : ℝ) ^ (δ * e) := h2
      _ ≤ _ := le_mul_of_one_le_left (by positivity) (le_max_left _ _)
  · have hK : 1 ≤ 1 / (δ * Real.log 2) := by rw [le_div_iff₀ hc]; linarith
    calc (e : ℝ) + 1 ≤ 1 / (δ * Real.log 2) * (1 + δ * Real.log 2 * e) := by
          rw [mul_add, ← mul_assoc, one_div_mul_cancel hc.ne', mul_one, one_mul]; linarith
      _ ≤ 1 / (δ * Real.log 2) * (2 : ℝ) ^ (δ * e) := by gcongr
      _ ≤ _ := by gcongr; exact le_max_right _ _

/-- **Divisor bound**: `τ(m) ≤ C_δ m^δ`. -/
theorem divisor_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, m ≠ 0 → ((m.divisors.card : ℕ) : ℝ) ≤ C * (m : ℝ) ^ δ := by
  set K : ℝ := max 1 (1 / (δ * Real.log 2)) with hKdef
  have hK1 : 1 ≤ K := le_max_left _ _
  set N : ℕ := ⌈(2 : ℝ) ^ (1 / δ)⌉₊
  refine ⟨K ^ N, by positivity, fun m hm => ?_⟩
  rw [Nat.card_divisors hm]
  push_cast
  have hm' : (m : ℝ) ^ δ = ∏ p ∈ m.primeFactors, ((p : ℝ) ^ δ) ^ (m.factorization p) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hm]
    rw [Nat.prod_factorization_eq_prod_primeFactors]
    push_cast
    rw [← Real.finsetProd_rpow _ _ (fun i _ => by positivity)]
    refine prod_congr rfl fun p _ => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      ← Real.rpow_mul (by positivity), mul_comm]
  have key : ∀ p ∈ m.primeFactors, ((m.factorization p : ℝ) + 1) ≤
      (if p < N then K else 1) * ((p : ℝ) ^ δ) ^ (m.factorization p) := by
    intro p hp
    have hpp := (Nat.mem_primeFactors.mp hp).1
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    set e := m.factorization p
    split_ifs with hpN
    · calc (e : ℝ) + 1 ≤ K * (2 : ℝ) ^ (δ * e) := add_one_le_mul_two_rpow hδ e
        _ = K * ((2 : ℝ) ^ δ) ^ e := by rw [Real.rpow_mul_natCast (by norm_num)]
        _ ≤ K * ((p : ℝ) ^ δ) ^ e := by gcongr
    · have hNp : (2 : ℝ) ^ (1 / δ) ≤ p := by
        calc (2 : ℝ) ^ (1 / δ) ≤ N := Nat.le_ceil _
          _ ≤ p := by exact_mod_cast not_lt.mp hpN
      have h2p : (2 : ℝ) ≤ (p : ℝ) ^ δ := by
        calc (2 : ℝ) = ((2 : ℝ) ^ (1 / δ)) ^ δ := by
              rw [one_div, Real.rpow_inv_rpow (by norm_num) hδ.ne']
          _ ≤ (p : ℝ) ^ δ := by gcongr
      have : (e : ℝ) + 1 ≤ 2 ^ e := by exact_mod_cast (Nat.lt_two_pow_self (n := e))
      calc (e : ℝ) + 1 ≤ 2 ^ e := this
        _ ≤ ((p : ℝ) ^ δ) ^ e := by gcongr
        _ = _ := (one_mul _).symm
  calc ∏ p ∈ m.primeFactors, ((m.factorization p : ℝ) + 1)
      ≤ ∏ p ∈ m.primeFactors, ((if p < N then K else 1) * ((p : ℝ) ^ δ) ^ (m.factorization p)) :=
        Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i hi => key i hi)
    _ = (∏ p ∈ m.primeFactors, (if p < N then K else 1)) * (m : ℝ) ^ δ := by
        rw [prod_mul_distrib, hm']
    _ ≤ K ^ N * (m : ℝ) ^ δ := by
        gcongr
        rw [prod_ite, prod_const_one, mul_one, prod_const]
        apply pow_le_pow_right₀ hK1
        calc #({p ∈ m.primeFactors | p < N}) ≤ #(range N) :=
              card_le_card fun p hp => by simp at hp ⊢; exact hp.2
          _ = N := card_range N

end ShiftedGcd
