import ShiftedGcd.Theorem2

/-!
# Uniform shifts (Heyman's thesis, Section 3.2)

R. Heyman, *Topics in divisibility: pairwise coprimality, the GCD of shifted sets and polynomial
irreducibility*, PhD thesis, UNSW, 2015, doi:10.26190/unsworks/18489, Section 3.2 (joint work
with I. E. Shparlinski; not in the journal paper).

All entries are shifted by the same `j ≥ 0`. `t(a)` is the least `j` with
`gcd(a₁ + j, …, aₙ + j) = 1`. Theorem 3.2.1: if `a` has two distinct entries then
`t(a) ≪ log² 𝔥(a)`.

As for Theorem 2 this is conditional on Iwaniec's bound (`IwaniecBound`). The proof uses
`gcd(a + j) ∣ gcd(aₛ + j, aᵣ - aₛ)` and the Jacobsthal bound for `aᵣ - aₛ`. The thesis bounds
`ω(aᵣ - aₛ) log ω(aᵣ - aₛ)` by `ω(𝔥(a)) log ω(𝔥(a))`, which does not follow since `ω` is not
monotone. We instead use `ω(m) log ω(m) ≪ log m` with `m = |aᵣ - aₛ| ≤ 2𝔥(a)`.
-/

open Finset

namespace ShiftedGcd

variable {n : ℕ}

/-- `t(a)`: the least `j ≥ 0` with `gcd(a₁ + j, …, aₙ + j) = 1`. -/
noncomputable def tShift (a : Fin n → ℤ) : ℕ := sInf {j : ℕ | vgcd (fun i => a i + j) = 1}

private lemma natAbs_le_height' (x : Fin n → ℤ) (i : Fin n) : (x i).natAbs ≤ height x :=
  Finset.le_sup (f := fun i => (x i).natAbs) (mem_univ i)

private lemma vgcd_dvd' (x : Fin n → ℤ) (i : Fin n) : (vgcd x : ℤ) ∣ x i :=
  Int.natCast_dvd.2 (Finset.gcd_dvd (mem_univ i))

/-- If some entry is `±1` then `gcd(a) = 1`. -/
private lemma vgcd_eq_one_of_unit (x : Fin n → ℤ) (i : Fin n) (hi : (x i).natAbs = 1) :
    vgcd x = 1 :=
  Nat.eq_one_of_dvd_one (hi ▸ Finset.gcd_dvd (mem_univ i))

/-- **Thesis, Theorem 3.2.1** (existence form). -/
theorem uniformShift_exists (hI : IwaniecBound) (n : ℕ) :
    ∃ C : ℝ, ∀ a : Fin n → ℤ, (∃ r s, a r ≠ a s) →
      ∃ j : ℕ, vgcd (fun i => a i + j) = 1 ∧ (j : ℝ) ≤ C * Real.log (height a) ^ 2 := by
  obtain ⟨C0, hC0⟩ := hI
  set C := max C0 0 with hCdef
  have hC0' : 0 ≤ C := le_max_right _ _
  have hC : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → 2 ≤ S.card →
      ∀ (x : ℤ) (m : ℕ), (∀ k < m, ∃ p ∈ S, (p : ℤ) ∣ x + k) →
        (m : ℝ) ≤ C * ((S.card : ℝ) * Real.log S.card) ^ 2 :=
    fun S hS hS2 x m hm => (hC0 S hS hS2 x m hm).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  refine ⟨36 * C + 5, fun a ⟨r, s, hrs⟩ => ?_⟩
  set x := height a with hx
  have hr := natAbs_le_height' a r
  have hs := natAbs_le_height' a s
  -- `𝔥(a) = 1`: entries lie in `{-1, 0, 1}` and two differ, so one of them is `±1`
  rcases Nat.lt_or_ge x 2 with hx2 | hx2
  · refine ⟨0, ?_, by simp only [Nat.cast_zero]; positivity⟩
    simp only [Nat.cast_zero, add_zero]
    by_cases har : (a r).natAbs = 1
    · exact vgcd_eq_one_of_unit a r har
    · exact vgcd_eq_one_of_unit a s (by omega)
  -- `𝔥(a) ≥ 2`
  set P := a r - a s with hP
  have hP0 : P ≠ 0 := sub_ne_zero.2 hrs
  have hPx : P.natAbs ≤ 2 * x := by omega
  have hx1 : (2 : ℝ) ≤ x := by exact_mod_cast hx2
  have hlogx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx1
  have hT : Real.log P.natAbs ≤ 2 * Real.log x := by
    have hP1 : (1 : ℝ) ≤ P.natAbs := by exact_mod_cast Int.natAbs_pos.2 hP0
    calc Real.log P.natAbs ≤ Real.log (2 * x) :=
          Real.log_le_log (by linarith) (by exact_mod_cast hPx)
      _ = Real.log 2 + Real.log x := Real.log_mul (by norm_num) (by linarith)
      _ ≤ 2 * Real.log x := by linarith
  obtain ⟨k, -, hkB, -, hgcd⟩ := Thm2.exists_good_shift C hC0' hC P hP0 (a s) _ hT
  refine ⟨k, ?_, ?_⟩
  · -- `gcd(a + k)` divides `a s + k` and `(a r + k) - (a s + k) = P`
    have h1 : (vgcd (fun i => a i + k) : ℤ) ∣ a s + k := vgcd_dvd' _ s
    have h2 : (vgcd (fun i => a i + k) : ℤ) ∣ P := by
      have := dvd_sub (vgcd_dvd' (fun i => a i + k) r) h1
      simpa [hP] using this
    have := Int.dvd_gcd h1 h2
    rw [hgcd] at this
    exact Nat.eq_one_of_dvd_one this
  · have hL : (0.69 : ℝ) ≤ Real.log x := by linarith
    have h2 : (2 : ℝ) ≤ 5 * Real.log x ^ 2 := by nlinarith
    calc (k : ℝ) ≤ C * (3 * (2 * Real.log x)) ^ 2 + 2 := hkB
      _ ≤ C * (36 * Real.log x ^ 2) + 5 * Real.log x ^ 2 := by nlinarith
      _ = (36 * C + 5) * Real.log x ^ 2 := by ring

/-- **Thesis, Theorem 3.2.1**: if `a` has two distinct entries then `t(a) ≪ log² 𝔥(a)`. -/
theorem tShift_le (hI : IwaniecBound) (n : ℕ) :
    ∃ C : ℝ, ∀ a : Fin n → ℤ, (∃ r s, a r ≠ a s) →
      (tShift a : ℝ) ≤ C * Real.log (height a) ^ 2 := by
  obtain ⟨C, hC⟩ := uniformShift_exists hI n
  refine ⟨C, fun a ha => ?_⟩
  obtain ⟨j, hj, hb⟩ := hC a ha
  have : tShift a ≤ j := Nat.sInf_le (show j ∈ {j : ℕ | vgcd (fun i => a i + j) = 1} from hj)
  exact (Nat.cast_le.2 this).trans hb

end ShiftedGcd
