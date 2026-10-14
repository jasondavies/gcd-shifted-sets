import ShiftedGcd.Defs
import ShiftedGcd.Theorem4Aux

/-!
# Theorem 4: gcd of random linear combinations

Unconditional. The `(h 𝔥(a))^{o(1)}` factor is formalised in its usual uniform sense. For
every `δ > 0` the bound holds with factor `(h 𝔥(a))^δ` and a constant depending only on
`n` and `δ`.

Correction to the paper's argument: the identity `R(a,h) = ∑_d μ(d) U_d(a,h)²` fails when
`a · x = 0` has solutions with positive `x`, which can happen when `a` has entries of both
signs. Those `x` must be discarded first; they contribute only `O(h^{2n-1})` pairs.

Outline of the formal proof (see `ShiftedGcd.Theorem4Count`, `ShiftedGcd.Theorem4Aux`):
reduce to `gcd(a) = 1`; write `R = ∑_{d ≤ T} μ(d) V_d` with `T = n h 𝔥(a)` and
`V_d = U_d² - Z²`; for `d ≤ h` use `(h - d)ⁿ ≤ d U_d ≤ (h + d)ⁿ`; for `h < d ≤ D` use
`U_d ≤ 2ⁿ D^{n-1}`; for `d > D` squarefree use `U_d ≤ (h D^{-1/n} + 1) h^{n-1}`; in the last two
ranges `|V_d| ≤ 2 U'_d U_d` and `∑ U'_d ≤ hⁿ τ-bound`. Here `D = h^{n²/(n²-n+1)}` and, unlike
in the paper, the first range is `d ≤ h` (rather than `d ≤ 2h/(3n)`).
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace ShiftedGcd

/-! ### Elementary real inequalities -/

lemma pow_succ_sub_pow_succ_le {y z : ℝ} (hy : 0 ≤ y) (hyz : y ≤ z) (m : ℕ) :
    z ^ (m + 1) - y ^ (m + 1) ≤ (m + 1) * (z - y) * z ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hz : 0 ≤ z := hy.trans hyz
    have h1 : y ^ (m + 1) ≤ z ^ (m + 1) := pow_le_pow_left₀ hy hyz _
    have h2 : z ^ (m + 1 + 1) - y ^ (m + 1 + 1) =
        z * (z ^ (m + 1) - y ^ (m + 1)) + (z - y) * y ^ (m + 1) := by ring
    rw [h2]
    calc z * (z ^ (m + 1) - y ^ (m + 1)) + (z - y) * y ^ (m + 1)
        ≤ z * ((m + 1) * (z - y) * z ^ m) + (z - y) * z ^ (m + 1) := by
          gcongr
      _ = ((m + 1 : ℕ) + 1 : ℝ) * (z - y) * z ^ (m + 1) := by push_cast; ring

variable {n : ℕ}

/-- (11): for `1 ≤ d ≤ h`, `|U_d² - h^{2n}/d²| ≤ 2n (2h)^{2n-1} / d`. -/
lemma abs_sq_Ucount_sub {a : Fin n → ℤ} (hn : 1 ≤ n) (ha : vgcd a = 1) {h d : ℕ} (hd : 0 < d)
    (hdh : d ≤ h) :
    |(Ucount a h d : ℝ) ^ 2 - (h : ℝ) ^ (2 * n) / (d : ℝ) ^ 2| ≤
      2 * n * (2 * (h : ℝ)) ^ (2 * n - 1) / d := by
  set x : ℝ := (h : ℝ) with hxdef
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hdx : (d : ℝ) ≤ x := by rw [hxdef]; exact_mod_cast hdh
  set u : ℝ := (Ucount a h d : ℝ) * d
  have hup : u ≤ (x + d) ^ n := by
    have := Ucount_mul_le ha h hd
    simp only [u, x]; exact_mod_cast this
  have hlow : (x - d) ^ n ≤ u := by
    have h1 := le_Ucount_mul ha h hd
    have h2 : x - d ≤ ((d * (h / d) : ℕ) : ℝ) := by
      have := Nat.lt_mul_div_succ h hd
      have h3 : h + 1 ≤ d * (h / d) + d := by rw [mul_add, mul_one] at this; omega
      have h4 : (h : ℝ) + 1 ≤ ((d * (h / d) : ℕ) : ℝ) + d := by exact_mod_cast h3
      simp only [x]; linarith
    calc (x - d) ^ n ≤ ((d * (h / d) : ℕ) : ℝ) ^ n :=
          pow_le_pow_left₀ (by linarith) h2 _
      _ ≤ u := by simp only [u]; exact_mod_cast h1
  obtain ⟨m, hm⟩ : ∃ m, 2 * n = m + 1 := ⟨2 * n - 1, by omega⟩
  have hm' : 2 * n - 1 = m := by omega
  have hu0 : 0 ≤ u := by positivity
  have hsq_up : u ^ 2 ≤ (x + d) ^ (m + 1) := by
    rw [← hm, mul_comm, pow_mul]; exact pow_le_pow_left₀ hu0 hup 2
  have hsq_low : (x - d) ^ (m + 1) ≤ u ^ 2 := by
    rw [← hm, mul_comm, pow_mul]; exact pow_le_pow_left₀ (by positivity) hlow 2
  have hA : (x + d) ^ (m + 1) - x ^ (m + 1) ≤ (m + 1) * d * (2 * x) ^ m := by
    have := pow_succ_sub_pow_succ_le (by positivity : (0 : ℝ) ≤ x) (by linarith : x ≤ x + d) m
    calc _ ≤ _ := this
      _ = (m + 1) * d * (x + d) ^ m := by ring
      _ ≤ _ := by gcongr; linarith
  have hB : x ^ (m + 1) - (x - d) ^ (m + 1) ≤ (m + 1) * d * (2 * x) ^ m := by
    have := pow_succ_sub_pow_succ_le (by linarith : (0 : ℝ) ≤ x - d) (by linarith : x - d ≤ x) m
    calc _ ≤ _ := this
      _ = (m + 1) * d * x ^ m := by ring
      _ ≤ _ := by gcongr; linarith
  have hkey : (Ucount a h d : ℝ) ^ 2 - x ^ (2 * n) / (d : ℝ) ^ 2 = (u ^ 2 - x ^ (m + 1)) / d ^ 2 := by
    rw [hm]; simp only [u]; field_simp
  rw [hkey, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (d : ℝ) ^ 2), div_le_div_iff₀
    (by positivity) hd', hm', show (2 * n : ℝ) = (m + 1 : ℝ) by exact_mod_cast hm]
  have habs : |u ^ 2 - x ^ (m + 1)| ≤ (m + 1) * d * (2 * x) ^ m :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  calc |u ^ 2 - x ^ (m + 1)| * d ≤ ((m + 1) * d * (2 * x) ^ m) * d := by gcongr
    _ = _ := by ring

/-- For `d ≥ h`: `U_d ≤ 2ⁿ d^{n-1}`. -/
lemma Ucount_le_large {a : Fin n → ℤ} (hn : 1 ≤ n) (ha : vgcd a = 1) {h d : ℕ} (hd : 0 < d)
    (hdh : h ≤ d) : (Ucount a h d : ℝ) ≤ 2 ^ n * (d : ℝ) ^ (n - 1) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : (Ucount a h d : ℝ) * d ≤ ((h : ℝ) + d) ^ n := by exact_mod_cast Ucount_mul_le ha h hd
  have h2 : ((h : ℝ) + d) ^ n ≤ (2 ^ n * (d : ℝ) ^ (n - 1)) * d := by
    rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hn, ← mul_pow]
    gcongr
    have : (h : ℝ) ≤ d := by exact_mod_cast hdh
    linarith
  exact le_of_mul_le_mul_right (h1.trans h2) hd'

lemma one_le_height {a : Fin n → ℤ} (ha : vgcd a = 1) : 1 ≤ height a := by
  by_contra h0
  have h0' : height a = 0 := by omega
  have hz : ∀ i, a i = 0 := by
    intro i
    have : (a i).natAbs ≤ height a := Finset.le_sup (f := fun i => (a i).natAbs) (mem_univ i)
    omega
  have : vgcd a = 0 := Finset.gcd_eq_zero_iff.mpr fun i _ => by simp [hz i]
  omega

/-! ### Exponent bookkeeping -/

section Exponents

variable (n : ℕ) (x : ℝ)

/-- The exponent `2n - n/(n²-n+1)` of the theorem. -/
noncomputable def expE : ℝ := (2 * n : ℝ) - n / (n ^ 2 - n + 1)

/-- The cut-off `D = h^{n²/(n²-n+1)}`. -/
noncomputable def cutD : ℝ := x ^ ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - n + 1))

variable {n x}

lemma denom_pos (hn : 2 ≤ n) : (0 : ℝ) < (n : ℝ) ^ 2 - n + 1 := by
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

lemma cutD_pow_mul (hn : 2 ≤ n) (hx : 0 < x) :
    cutD n x ^ (n - 1) * x ^ n = x ^ expE n := by
  have hq := (denom_pos hn).ne'
  rw [cutD, ← Real.rpow_mul_natCast hx.le, ← Real.rpow_natCast x n, ← Real.rpow_add hx, expE]
  congr 1
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one, div_mul_eq_mul_div, div_add' _ _ _ hq,
    eq_sub_iff_add_eq, ← add_div, div_eq_iff hq]
  ring

lemma pow_div_cutD_mul (hn : 2 ≤ n) (hx : 0 < x) :
    x ^ n / cutD n x ^ ((1 : ℝ) / n) * x ^ n = x ^ expE n := by
  have hq := (denom_pos hn).ne'
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [cutD, ← Real.rpow_mul hx.le, ← Real.rpow_natCast x n, ← Real.rpow_sub hx,
    ← Real.rpow_add hx, expE]
  congr 1
  have : (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - n + 1) * (1 / n) = n / ((n : ℝ) ^ 2 - n + 1) := by
    field_simp
  rw [this]; ring

lemma pow_le_pow_expE (hn : 2 ≤ n) (hx : 1 ≤ x) : x ^ (2 * n - 1) ≤ x ^ expE n := by
  rw [← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le hx
  have hq := denom_pos hn
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Nat.cast_sub (by omega), expE]
  push_cast
  have : (n : ℝ) / ((n : ℝ) ^ 2 - n + 1) ≤ 1 := by
    rw [div_le_one hq]; nlinarith
  linarith

end Exponents

/-! ### The main estimate for primitive vectors -/

theorem main_primitive (hn : 2 ≤ n) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ a : Fin n → ℤ, vgcd a = 1 → ∀ h : ℕ, 1 ≤ h →
      |(R a h : ℝ) - (riemannZeta 2).re⁻¹ * (h : ℝ) ^ (2 * n)| ≤
        C * (h : ℝ) ^ expE n * ((h : ℝ) * height a) ^ δ := by
  obtain ⟨Cτ, hCτ0, hCτ⟩ := divisor_bound hδ
  have hn1 : 1 ≤ n := by omega
  set A : ℝ := 2 * n * 2 ^ (2 * n - 1) with hA
  refine ⟨A * (1 + 1 / δ) + 2 + 2 * (2 ^ n + 2) * (Cτ * (n : ℝ) ^ δ), fun a ha h hh => ?_⟩
  have ha0 : a ≠ 0 := fun h0 => by
    have := one_le_height ha
    simp [h0, height] at this
  have hH : 1 ≤ height a := one_le_height ha
  have hhT : h ≤ n * h * height a := by
    calc h = 1 * h * 1 := by ring
      _ ≤ n * h * height a := by gcongr
  have hx1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hx0 : (0 : ℝ) < h := by linarith
  have hH1 : (1 : ℝ) ≤ height a := by exact_mod_cast hH
  have hP : 1 ≤ ((h : ℝ) * height a) ^ δ := Real.one_le_rpow (by nlinarith) hδ.le
  have hD0 : 0 < cutD n h := Real.rpow_pos_of_pos hx0 _
  have hxn : (h : ℝ) ^ n = (h : ℝ) * (h : ℝ) ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hc : (riemannZeta 2).re⁻¹ = ∑' d : ℕ, (μ d : ℝ) / (d : ℝ) ^ 2 :=
    tsum_moebius_div_sq.symm
  rw [hc]
  set c := ∑' d : ℕ, (μ d : ℝ) / (d : ℝ) ^ 2 with hcdef
  set K : ℝ := 2 ^ n * cutD n h ^ (n - 1) + (h : ℝ) ^ n / cutD n h ^ ((1 : ℝ) / n) +
    (h : ℝ) ^ (n - 1) with hKdef
  have hK0 : 0 ≤ K := by positivity
  /- Step 1: decomposition. -/
  have hR : (R a h : ℝ) = ∑ d ∈ Ioc 0 (n * h * height a), (μ d : ℝ) * (Vcount a h d : ℝ) := by
    exact_mod_cast R_eq_sum_moebius ha h
  have hpartial : ∑ d ∈ range (h + 1), (μ d : ℝ) / (d : ℝ) ^ 2 =
      ∑ d ∈ Ioc 0 h, (μ d : ℝ) / (d : ℝ) ^ 2 := by
    have : range (h + 1) = insert 0 (Ioc 0 h) := by
      ext d; simp only [mem_range, mem_insert, mem_Ioc]; omega
    rw [this, sum_insert (by simp)]; simp
  have hdecomp : (R a h : ℝ) - c * (h : ℝ) ^ (2 * n) =
      ∑ d ∈ Ioc 0 h, (μ d : ℝ) * ((Vcount a h d : ℝ) - (h : ℝ) ^ (2 * n) / (d : ℝ) ^ 2) +
      ∑ d ∈ Ioc h (n * h * height a), (μ d : ℝ) * (Vcount a h d : ℝ) -
      (h : ℝ) ^ (2 * n) * (c - ∑ d ∈ range (h + 1), (μ d : ℝ) / (d : ℝ) ^ 2) := by
    rw [hR, ← sum_Ioc_consecutive _ (Nat.zero_le h) hhT, hpartial]
    have : ∑ d ∈ Ioc 0 h, (μ d : ℝ) * ((Vcount a h d : ℝ) - (h : ℝ) ^ (2 * n) / (d : ℝ) ^ 2) =
        ∑ d ∈ Ioc 0 h, (μ d : ℝ) * (Vcount a h d : ℝ) -
          (h : ℝ) ^ (2 * n) * ∑ d ∈ Ioc 0 h, (μ d : ℝ) / (d : ℝ) ^ 2 := by
      rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun d _ => by ring
    rw [this]; ring
  /- Step 2: the range `d ≤ h`. -/
  have hZ : (Zcount a h : ℝ) ≤ (h : ℝ) ^ (n - 1) := by exact_mod_cast Zcount_le ha0 h
  have hE1pt : ∀ d ∈ Ioc 0 h,
      |(μ d : ℝ) * ((Vcount a h d : ℝ) - (h : ℝ) ^ (2 * n) / (d : ℝ) ^ 2)| ≤
        2 * n * (2 * (h : ℝ)) ^ (2 * n - 1) * (1 / d) + (h : ℝ) ^ (n - 1) * (h : ℝ) ^ (n - 1) := by
    intro d hd
    rw [mem_Ioc] at hd
    have hV : (Vcount a h d : ℝ) = (Ucount a h d : ℝ) ^ 2 - (Zcount a h : ℝ) * Zcount a h := by
      have h1 : (Vcount a h d : ℝ) + Zcount a h * Zcount a h = Ucount a h d * Ucount a h d := by
        exact_mod_cast Vcount_add a h d
      rw [sq]; linarith
    have h1 := abs_sq_Ucount_sub hn1 ha hd.1 hd.2
    have hμ : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
    have hZ0 : (0 : ℝ) ≤ Zcount a h := Nat.cast_nonneg _
    rw [abs_mul]
    calc |(μ d : ℝ)| * |(Vcount a h d : ℝ) - (h : ℝ) ^ (2 * n) / (d : ℝ) ^ 2|
        ≤ 1 * |(Vcount a h d : ℝ) - (h : ℝ) ^ (2 * n) / (d : ℝ) ^ 2| := by gcongr
      _ ≤ |(Ucount a h d : ℝ) ^ 2 - (h : ℝ) ^ (2 * n) / (d : ℝ) ^ 2| +
            (Zcount a h : ℝ) * Zcount a h := by
          rw [one_mul, hV]
          have : (Ucount a h d : ℝ) ^ 2 - Zcount a h * Zcount a h - (h : ℝ) ^ (2 * n) / (d : ℝ) ^ 2
              = ((Ucount a h d : ℝ) ^ 2 - (h : ℝ) ^ (2 * n) / (d : ℝ) ^ 2) -
                Zcount a h * Zcount a h := by ring
          rw [this]
          calc _ ≤ _ := abs_sub _ _
            _ = _ := by rw [abs_of_nonneg (mul_nonneg hZ0 hZ0)]
      _ ≤ _ := by
          rw [mul_one_div]
          gcongr
  have hharm : ∑ d ∈ Ioc 0 h, (1 : ℝ) / d ≤ 1 + Real.log h := by
    have := harmonic_le_one_add_log h
    rw [harmonic_eq_sum_Icc] at this
    push_cast at this
    have e : Icc 1 h = Ioc 0 h := by ext d; simp; omega
    rw [e] at this
    simpa [one_div] using this
  have hpow1 : (h : ℝ) * ((h : ℝ) ^ (n - 1) * (h : ℝ) ^ (n - 1)) = (h : ℝ) ^ (2 * n - 1) := by
    rw [← pow_add, ← pow_succ']; congr 1; omega
  have hE1 : |∑ d ∈ Ioc 0 h, (μ d : ℝ) * ((Vcount a h d : ℝ) - (h : ℝ) ^ (2 * n) / (d : ℝ) ^ 2)|
      ≤ A * (h : ℝ) ^ (2 * n - 1) * (1 + Real.log h) + (h : ℝ) ^ (2 * n - 1) := by
    calc _ ≤ ∑ d ∈ Ioc 0 h,
          |(μ d : ℝ) * ((Vcount a h d : ℝ) - (h : ℝ) ^ (2 * n) / (d : ℝ) ^ 2)| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Ioc 0 h, (2 * n * (2 * (h : ℝ)) ^ (2 * n - 1) * (1 / d) +
            (h : ℝ) ^ (n - 1) * (h : ℝ) ^ (n - 1)) := sum_le_sum hE1pt
      _ = 2 * n * (2 * (h : ℝ)) ^ (2 * n - 1) * ∑ d ∈ Ioc 0 h, (1 : ℝ) / d +
            h * ((h : ℝ) ^ (n - 1) * (h : ℝ) ^ (n - 1)) := by
          rw [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Ioc, nsmul_eq_mul, Nat.sub_zero]
      _ ≤ 2 * n * (2 * (h : ℝ)) ^ (2 * n - 1) * (1 + Real.log h) +
            h * ((h : ℝ) ^ (n - 1) * (h : ℝ) ^ (n - 1)) := by gcongr
      _ = _ := by rw [hpow1, mul_pow, hA]; ring
  /- Step 3: the tail of the series. -/
  have hE3 : |(h : ℝ) ^ (2 * n) * (c - ∑ d ∈ range (h + 1), (μ d : ℝ) / (d : ℝ) ^ 2)| ≤
      (h : ℝ) ^ (2 * n - 1) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc (h : ℝ) ^ (2 * n) * |c - ∑ d ∈ range (h + 1), (μ d : ℝ) / (d : ℝ) ^ 2|
        ≤ (h : ℝ) ^ (2 * n) * (1 / h) := by gcongr; exact abs_tsum_moebius_sub_le h hh
      _ = _ := by
          rw [show 2 * n = (2 * n - 1) + 1 by omega, pow_succ]
          field_simp
          congr 1
  /- Step 4: the range `d > h`. -/
  have hUK : ∀ d ∈ Ioc h (n * h * height a), Squarefree d → (Ucount a h d : ℝ) ≤ K := by
    intro d hd hsq
    rw [mem_Ioc] at hd
    have hd0 : 0 < d := by omega
    by_cases hdD : (d : ℝ) ≤ cutD n h
    · calc (Ucount a h d : ℝ) ≤ 2 ^ n * (d : ℝ) ^ (n - 1) :=
            Ucount_le_large hn1 ha hd0 hd.1.le
        _ ≤ 2 ^ n * cutD n h ^ (n - 1) := by gcongr
        _ ≤ K := by
            rw [hKdef]
            have : 0 ≤ (h : ℝ) ^ n / cutD n h ^ ((1 : ℝ) / n) := by positivity
            have : 0 ≤ (h : ℝ) ^ (n - 1) := by positivity
            linarith
    · push Not at hdD
      have hroot : cutD n h ^ ((1 : ℝ) / n) ≤ (d : ℝ) ^ ((1 : ℝ) / n) :=
        Real.rpow_le_rpow hD0.le hdD.le (by positivity)
      have hroot0 : 0 < cutD n h ^ ((1 : ℝ) / n) := by positivity
      calc (Ucount a h d : ℝ) ≤ ((h : ℝ) / (d : ℝ) ^ ((1 : ℝ) / n) + 1) * (h : ℝ) ^ (n - 1) :=
            Ucount_le_squarefree (by omega) ha h hsq
        _ ≤ ((h : ℝ) / cutD n h ^ ((1 : ℝ) / n) + 1) * (h : ℝ) ^ (n - 1) := by
            gcongr
        _ = (h : ℝ) ^ n / cutD n h ^ ((1 : ℝ) / n) + (h : ℝ) ^ (n - 1) := by
            rw [hxn]; ring
        _ ≤ K := by
            rw [hKdef]
            have : 0 ≤ 2 ^ n * cutD n h ^ (n - 1) := by positivity
            linarith
  have hE2pt : ∀ d ∈ Ioc h (n * h * height a),
      |(μ d : ℝ) * (Vcount a h d : ℝ)| ≤ 2 * K * (Upcount a h d : ℝ) := by
    intro d hd
    by_cases hsq : Squarefree d
    · have hμ : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
      have hV : (Vcount a h d : ℝ) ≤ 2 * ((Upcount a h d : ℝ) * Ucount a h d) := by
        exact_mod_cast Vcount_le a h d
      rw [abs_mul, Nat.abs_cast]
      calc |(μ d : ℝ)| * (Vcount a h d : ℝ) ≤ 1 * (2 * ((Upcount a h d : ℝ) * Ucount a h d)) := by
            gcongr
        _ ≤ 1 * (2 * ((Upcount a h d : ℝ) * K)) := by gcongr; exact hUK d hd hsq
        _ = _ := by ring
    · rw [moebius_eq_zero_of_not_squarefree hsq]
      simp only [Int.cast_zero, zero_mul, abs_zero]
      positivity
  have hUpsum := sum_Upcount_le (a := a) h (n * h * height a) (fun y hy => natAbs_dot_le hy)
    hδ.le hCτ
  have hE2 : |∑ d ∈ Ioc h (n * h * height a), (μ d : ℝ) * (Vcount a h d : ℝ)| ≤
      2 * K * ((h : ℝ) ^ n * (Cτ * ((n * h * height a : ℕ) : ℝ) ^ δ)) := by
    calc _ ≤ ∑ d ∈ Ioc h (n * h * height a), |(μ d : ℝ) * (Vcount a h d : ℝ)| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Ioc h (n * h * height a), 2 * K * (Upcount a h d : ℝ) := sum_le_sum hE2pt
      _ = 2 * K * ∑ d ∈ Ioc h (n * h * height a), (Upcount a h d : ℝ) := by rw [mul_sum]
      _ ≤ 2 * K * ∑ d ∈ Ioc 0 (n * h * height a), (Upcount a h d : ℝ) := by
          exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg
            (Ioc_subset_Ioc_left (Nat.zero_le h)) fun _ _ _ => Nat.cast_nonneg _) (by positivity)
      _ ≤ _ := by gcongr
  /- Step 5: exponents. -/
  set X := (h : ℝ) ^ expE n with hX
  set P := ((h : ℝ) * height a) ^ δ with hPdef
  have hX0 : 0 ≤ X := by positivity
  have hY : (h : ℝ) ^ (2 * n - 1) ≤ X := pow_le_pow_expE hn hx1
  have hlog : 1 + Real.log h ≤ (1 + 1 / δ) * P := by
    have h1 : Real.log h ≤ (h : ℝ) ^ δ / δ := Real.log_le_rpow_div hx0.le hδ
    have h2 : (h : ℝ) ^ δ ≤ P := Real.rpow_le_rpow hx0.le (by nlinarith) hδ.le
    have h3 : (h : ℝ) ^ δ / δ ≤ P / δ := by gcongr
    have h4 : (1 + 1 / δ) * P = P + P / δ := by ring
    linarith
  have hKx : 2 * K * (h : ℝ) ^ n ≤ 2 * (2 ^ n + 2) * X := by
    have e1 := cutD_pow_mul hn hx0
    have e2 := pow_div_cutD_mul hn hx0
    have e3 : (h : ℝ) ^ (n - 1) * (h : ℝ) ^ n = (h : ℝ) ^ (2 * n - 1) := by
      rw [← pow_add]; congr 1; omega
    have : 2 * K * (h : ℝ) ^ n = 2 * (2 ^ n * (cutD n h ^ (n - 1) * (h : ℝ) ^ n) +
        (h : ℝ) ^ n / cutD n h ^ ((1 : ℝ) / n) * (h : ℝ) ^ n +
        (h : ℝ) ^ (n - 1) * (h : ℝ) ^ n) := by
      rw [hKdef]; ring
    rw [this, e1, e2, e3, ← hX]
    linarith
  have hT : ((n * h * height a : ℕ) : ℝ) ^ δ = (n : ℝ) ^ δ * P := by
    push_cast
    rw [mul_assoc, Real.mul_rpow (by positivity) (by positivity)]
  /- Step 6: combine. -/
  rw [hdecomp]
  have hA0 : 0 ≤ A := by positivity
  have hCn : 0 ≤ Cτ * (n : ℝ) ^ δ := by positivity
  have hfin1 : A * (h : ℝ) ^ (2 * n - 1) * (1 + Real.log h) ≤ A * (1 + 1 / δ) * (X * P) := by
    have : 0 ≤ 1 + Real.log h := by
      have := Real.log_nonneg hx1; linarith
    calc A * (h : ℝ) ^ (2 * n - 1) * (1 + Real.log h) ≤ A * X * ((1 + 1 / δ) * P) := by
          gcongr
      _ = _ := by ring
  have hfin2 : 2 * K * ((h : ℝ) ^ n * (Cτ * ((n * h * height a : ℕ) : ℝ) ^ δ)) ≤
      2 * (2 ^ n + 2) * (Cτ * (n : ℝ) ^ δ) * (X * P) := by
    rw [hT]
    calc 2 * K * ((h : ℝ) ^ n * (Cτ * ((n : ℝ) ^ δ * P)))
        = (2 * K * (h : ℝ) ^ n) * ((Cτ * (n : ℝ) ^ δ) * P) := by ring
      _ ≤ (2 * (2 ^ n + 2) * X) * ((Cτ * (n : ℝ) ^ δ) * P) := by gcongr
      _ = _ := by ring
  have hfin3 : (h : ℝ) ^ (2 * n - 1) ≤ X * P := by
    calc (h : ℝ) ^ (2 * n - 1) ≤ X * 1 := by rw [mul_one]; exact hY
      _ ≤ X * P := by gcongr
  calc _ ≤ |∑ d ∈ Ioc 0 h, (μ d : ℝ) * ((Vcount a h d : ℝ) - (h : ℝ) ^ (2 * n) / (d : ℝ) ^ 2) +
          ∑ d ∈ Ioc h (n * h * height a), (μ d : ℝ) * (Vcount a h d : ℝ)| +
        |(h : ℝ) ^ (2 * n) * (c - ∑ d ∈ range (h + 1), (μ d : ℝ) / (d : ℝ) ^ 2)| := abs_sub _ _
    _ ≤ |∑ d ∈ Ioc 0 h, (μ d : ℝ) * ((Vcount a h d : ℝ) - (h : ℝ) ^ (2 * n) / (d : ℝ) ^ 2)| +
          |∑ d ∈ Ioc h (n * h * height a), (μ d : ℝ) * (Vcount a h d : ℝ)| +
        |(h : ℝ) ^ (2 * n) * (c - ∑ d ∈ range (h + 1), (μ d : ℝ) / (d : ℝ) ^ 2)| := by
          gcongr; exact abs_add_le _ _
    _ ≤ (A * (h : ℝ) ^ (2 * n - 1) * (1 + Real.log h) + (h : ℝ) ^ (2 * n - 1)) +
          2 * K * ((h : ℝ) ^ n * (Cτ * ((n * h * height a : ℕ) : ℝ) ^ δ)) +
          (h : ℝ) ^ (2 * n - 1) := by gcongr
    _ ≤ A * (1 + 1 / δ) * (X * P) + X * P + 2 * (2 ^ n + 2) * (Cτ * (n : ℝ) ^ δ) * (X * P) +
          X * P := by linarith
    _ = _ := by ring

/-- **Theorem 4**. -/
theorem theorem4 {n : ℕ} (hn : 2 ≤ n) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ a : Fin n → ℤ, a ≠ 0 → ∀ h : ℕ, 1 ≤ h →
      |(R a h : ℝ) - (riemannZeta 2).re⁻¹ * (h : ℝ) ^ (2 * n)| ≤
        C * (h : ℝ) ^ ((2 * n : ℝ) - n / (n ^ 2 - n + 1)) * ((h : ℝ) * height a) ^ δ := by
  obtain ⟨C, hC⟩ := main_primitive hn hδ
  refine ⟨max C 0, fun a ha h hh => ?_⟩
  obtain ⟨b, hb, hba, hR⟩ := exists_primitive ha
  rw [hR h]
  calc _ ≤ C * (h : ℝ) ^ expE n * ((h : ℝ) * height b) ^ δ := hC b hb h hh
    _ ≤ max C 0 * (h : ℝ) ^ expE n * ((h : ℝ) * height b) ^ δ := by
        gcongr; exact le_max_left _ _
    _ ≤ max C 0 * (h : ℝ) ^ expE n * ((h : ℝ) * height a) ^ δ := by
        gcongr

end ShiftedGcd
