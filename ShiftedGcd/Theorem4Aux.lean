import ShiftedGcd.Theorem4Count
import ShiftedGcd.DivisorBound

/-!
# Theorem 4, auxiliary lemmas

* reduction to primitive vectors (`exists_primitive`);
* the Möbius inversion formula `R(a,h) = ∑_{d ≤ T} μ(d) V_d` (`R_eq_sum_moebius`), where
  `V_d` counts the pairs `(x, y)` with `d ∣ a · x`, `d ∣ a · y`, not both `a · x, a · y` zero;
* `V_d + Z² = U_d²` and `V_d ≤ 2 U'_d U_d`;
* `∑_{d ≤ T} U'_d ≤ hⁿ C T^δ` (from the divisor bound);
* `∑_d μ(d)/d² = 1/ζ(2)` and the tail bound.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace ShiftedGcd

variable {n : ℕ}

/-! ### Reduction to primitive vectors -/

lemma exists_primitive {a : Fin n → ℤ} (ha : a ≠ 0) :
    ∃ b : Fin n → ℤ, vgcd b = 1 ∧ height b ≤ height a ∧ ∀ h, R a h = R b h := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  set g := vgcd a with hgdef
  have hg0 : g ≠ 0 := by
    intro h0
    have := Finset.gcd_eq_zero_iff.mp h0 i (mem_univ i)
    exact hi (Int.natAbs_eq_zero.mp this)
  have hgdvd : ∀ j, (g : ℤ) ∣ a j := fun j =>
    Int.ofNat_dvd_left.mpr (Finset.gcd_dvd (f := fun i => (a i).natAbs) (mem_univ j))
  set b : Fin n → ℤ := fun j => a j / g
  have hab : ∀ j, a j = g * b j := fun j => (Int.mul_ediv_cancel' (hgdvd j)).symm
  have hnb : ∀ j, (b j).natAbs = (a j).natAbs / g := by
    intro j
    rw [hab j, Int.natAbs_mul, Int.natAbs_natCast, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hg0)]
  refine ⟨b, ?_, ?_, ?_⟩
  · have : vgcd b = univ.gcd (fun j => (a j).natAbs / univ.gcd fun i => (a i).natAbs) := by
      simp only [vgcd]; exact Finset.gcd_congr rfl fun j _ => hnb j
    rw [this]
    exact Finset.gcd_div_eq_one (mem_univ i) (by simpa using hi)
  · exact Finset.sup_mono_fun fun j _ => by rw [hnb j]; exact Nat.div_le_self _ _
  · intro h
    have hdot : ∀ x, dot a x = g * dot b x := by
      intro x; simp only [dot, mul_sum]
      exact sum_congr rfl fun j _ => by rw [hab j, mul_assoc]
    unfold R
    congr 1
    refine filter_congr fun p _ => ?_
    have h1 : vgcd b = 1 := by
      have : vgcd b = univ.gcd (fun j => (a j).natAbs / univ.gcd fun i => (a i).natAbs) := by
        simp only [vgcd]; exact Finset.gcd_congr rfl fun j _ => hnb j
      rw [this]
      exact Finset.gcd_div_eq_one (mem_univ i) (by simpa using hi)
    rw [hdot, hdot, Int.gcd_mul_left, Int.natAbs_natCast, h1]
    constructor
    · intro hh
      have : g * 1 = g * Int.gcd (dot b p.1) (dot b p.2) := by rw [mul_one]; exact hh
      exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hg0) this)
    · intro hh; rw [← hh, mul_one]

/-! ### Basic bounds -/

lemma natAbs_dot_le {a x : Fin n → ℤ} {h : ℕ} (hx : x ∈ boxVecs n h) :
    (dot a x).natAbs ≤ n * h * height a := by
  have h2 : ∀ i, |a i * x i| ≤ (height a : ℤ) * h := by
    intro i
    rw [abs_mul]
    have h1 : (a i).natAbs ≤ height a := Finset.le_sup (f := fun i => (a i).natAbs) (mem_univ i)
    have ha' : |a i| ≤ height a := by rw [Int.abs_eq_natAbs]; exact_mod_cast h1
    have hx' := (mem_boxVecs.mp hx) i
    have hx'' : |x i| ≤ h := by rw [abs_of_pos (by omega)]; exact hx'.2
    exact mul_le_mul ha' hx'' (abs_nonneg _) (by positivity)
  have : |dot a x| ≤ n * (height a * h) := by
    calc |dot a x| ≤ ∑ i, |a i * x i| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, (height a : ℤ) * h := sum_le_sum fun i _ => h2 i
      _ = _ := by simp
  have h3 : ((dot a x).natAbs : ℤ) ≤ ((n * h * height a : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs]; push_cast; linarith
  exact_mod_cast h3

/-! ### The Möbius formula -/

/-- `V_d`: pairs `(x, y)` in the box with `d ∣ a · x`, `d ∣ a · y`, not both zero. -/
def Vcount (a : Fin n → ℤ) (h d : ℕ) : ℕ :=
  #{p ∈ boxVecs n h ×ˢ boxVecs n h |
    (dot a p.1 ≠ 0 ∨ dot a p.2 ≠ 0) ∧ (d : ℤ) ∣ dot a p.1 ∧ (d : ℤ) ∣ dot a p.2}

lemma R_eq_sum_moebius {a : Fin n → ℤ} (ha : vgcd a = 1) (h : ℕ) :
    (R a h : ℤ) = ∑ d ∈ Ioc 0 (n * h * height a), μ d * (Vcount a h d : ℤ) := by
  classical
  set T := n * h * height a
  set B2 := boxVecs n h ×ˢ boxVecs n h
  have key : ∀ p ∈ B2, (if vgcd a = Int.gcd (dot a p.1) (dot a p.2) then (1 : ℤ) else 0) =
      ∑ d ∈ Ioc 0 T, if (dot a p.1 ≠ 0 ∨ dot a p.2 ≠ 0) ∧ (d : ℤ) ∣ dot a p.1 ∧
        (d : ℤ) ∣ dot a p.2 then μ d else 0 := by
    intro p hp
    rw [ha]
    by_cases hz : dot a p.1 ≠ 0 ∨ dot a p.2 ≠ 0
    · simp only [hz, true_and]
      set g := Int.gcd (dot a p.1) (dot a p.2) with hgdef
      have hg0 : g ≠ 0 := fun h0 => by
        rcases hz with hz | hz
        · exact hz (Int.gcd_eq_zero_iff.mp h0).1
        · exact hz (Int.gcd_eq_zero_iff.mp h0).2
      have hp' := mem_product.mp hp
      have hgT : g ≤ T := by
        rcases hz with hz | hz
        · exact (Nat.le_of_dvd (Int.natAbs_pos.mpr hz) (Nat.gcd_dvd_left _ _)).trans
            (natAbs_dot_le hp'.1)
        · exact (Nat.le_of_dvd (Int.natAbs_pos.mpr hz) (Nat.gcd_dvd_right _ _)).trans
            (natAbs_dot_le hp'.2)
      have hiff : ∀ d : ℕ, ((d : ℤ) ∣ dot a p.1 ∧ (d : ℤ) ∣ dot a p.2) ↔ d ∣ g := by
        intro d
        rw [Int.ofNat_dvd_left, Int.ofNat_dvd_left, ← Nat.dvd_gcd_iff]
        rfl
      simp_rw [hiff]
      rw [← sum_filter]
      have hfilt : {d ∈ Ioc 0 T | d ∣ g} = g.divisors := by
        ext d
        simp only [mem_filter, mem_Ioc, Nat.mem_divisors]
        constructor
        · rintro ⟨_, hd⟩; exact ⟨hd, hg0⟩
        · rintro ⟨hd, _⟩
          exact ⟨⟨Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hg0),
            (Nat.le_of_dvd (Nat.pos_of_ne_zero hg0) hd).trans hgT⟩, hd⟩
      rw [hfilt, ← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply]
      simp only [eq_comm]
    · simp only [hz, false_and, ite_false, sum_const_zero]
      push Not at hz
      rw [hz.1, hz.2]
      simp
  calc (R a h : ℤ) = ∑ p ∈ B2,
        (if vgcd a = Int.gcd (dot a p.1) (dot a p.2) then (1 : ℤ) else 0) := by
        rw [R, sum_boole]
    _ = ∑ p ∈ B2, ∑ d ∈ Ioc 0 T, if (dot a p.1 ≠ 0 ∨ dot a p.2 ≠ 0) ∧ (d : ℤ) ∣ dot a p.1 ∧
        (d : ℤ) ∣ dot a p.2 then μ d else 0 := sum_congr rfl key
    _ = ∑ d ∈ Ioc 0 T, ∑ p ∈ B2, if (dot a p.1 ≠ 0 ∨ dot a p.2 ≠ 0) ∧ (d : ℤ) ∣ dot a p.1 ∧
        (d : ℤ) ∣ dot a p.2 then μ d else 0 := sum_comm
    _ = _ := by
        refine sum_congr rfl fun d _ => ?_
        rw [← sum_filter, sum_const, Vcount, nsmul_eq_mul, mul_comm]

lemma Vcount_add (a : Fin n → ℤ) (h d : ℕ) :
    Vcount a h d + Zcount a h * Zcount a h = Ucount a h d * Ucount a h d := by
  classical
  rw [Ucount, Zcount, ← card_product, ← card_product, ← filter_product, ← filter_product, Vcount,
    ← card_filter_add_card_filter_not (s := {x ∈ boxVecs n h ×ˢ boxVecs n h |
      (d : ℤ) ∣ dot a x.1 ∧ (d : ℤ) ∣ dot a x.2})
    (fun p => dot a p.1 ≠ 0 ∨ dot a p.2 ≠ 0), filter_filter, filter_filter]
  have e1 : {x ∈ boxVecs n h ×ˢ boxVecs n h | ((d : ℤ) ∣ dot a x.1 ∧ (d : ℤ) ∣ dot a x.2) ∧
      (dot a x.1 ≠ 0 ∨ dot a x.2 ≠ 0)} = {p ∈ boxVecs n h ×ˢ boxVecs n h |
      (dot a p.1 ≠ 0 ∨ dot a p.2 ≠ 0) ∧ (d : ℤ) ∣ dot a p.1 ∧ (d : ℤ) ∣ dot a p.2} :=
    filter_congr fun p _ => by tauto
  have e2 : {x ∈ boxVecs n h ×ˢ boxVecs n h | ((d : ℤ) ∣ dot a x.1 ∧ (d : ℤ) ∣ dot a x.2) ∧
      ¬(dot a x.1 ≠ 0 ∨ dot a x.2 ≠ 0)} = {x ∈ boxVecs n h ×ˢ boxVecs n h |
      dot a x.1 = 0 ∧ dot a x.2 = 0} := by
    refine filter_congr fun p _ => ?_
    constructor
    · rintro ⟨_, hp⟩; push Not at hp; exact hp
    · rintro ⟨h1, h2⟩; refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp [h1, h2]
  rw [e1, e2]

lemma Vcount_le (a : Fin n → ℤ) (h d : ℕ) :
    Vcount a h d ≤ 2 * (Upcount a h d * Ucount a h d) := by
  classical
  have hsub : {p ∈ boxVecs n h ×ˢ boxVecs n h |
      (dot a p.1 ≠ 0 ∨ dot a p.2 ≠ 0) ∧ (d : ℤ) ∣ dot a p.1 ∧ (d : ℤ) ∣ dot a p.2} ⊆
      ({x ∈ boxVecs n h | dot a x ≠ 0 ∧ (d : ℤ) ∣ dot a x} ×ˢ
        {x ∈ boxVecs n h | (d : ℤ) ∣ dot a x}) ∪
      ({x ∈ boxVecs n h | (d : ℤ) ∣ dot a x} ×ˢ
        {x ∈ boxVecs n h | dot a x ≠ 0 ∧ (d : ℤ) ∣ dot a x}) := by
    intro p hp
    simp only [mem_filter, mem_product, mem_union] at hp ⊢
    tauto
  calc Vcount a h d ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ = _ := by rw [card_product, card_product, Upcount, Ucount]; ring

/-! ### The divisor-sum bound -/

lemma sum_Upcount_le {a : Fin n → ℤ} (h T : ℕ) (hT : ∀ x ∈ boxVecs n h, (dot a x).natAbs ≤ T)
    {δ C : ℝ} (hδ : 0 ≤ δ) (hC : ∀ m : ℕ, m ≠ 0 → ((m.divisors.card : ℕ) : ℝ) ≤ C * (m : ℝ) ^ δ) :
    (∑ d ∈ Ioc 0 T, (Upcount a h d : ℝ)) ≤ (h : ℝ) ^ n * (C * (T : ℝ) ^ δ) := by
  classical
  have hC0 : 0 ≤ C := by
    have := hC 1 one_ne_zero
    simp at this
    linarith
  have hswap : (∑ d ∈ Ioc 0 T, Upcount a h d : ℕ) =
      ∑ x ∈ boxVecs n h, #{d ∈ Ioc (0 : ℕ) T | dot a x ≠ 0 ∧ ((d : ℕ) : ℤ) ∣ dot a x} := by
    simp only [Upcount, card_eq_sum_ones, sum_filter]
    exact sum_comm
  have hpt : ∀ x ∈ boxVecs n h,
      (#{d ∈ Ioc (0 : ℕ) T | dot a x ≠ 0 ∧ ((d : ℕ) : ℤ) ∣ dot a x} : ℝ) ≤ C * (T : ℝ) ^ δ := by
    intro x hx
    by_cases h0 : dot a x = 0
    · have : {d ∈ Ioc (0 : ℕ) T | dot a x ≠ 0 ∧ ((d : ℕ) : ℤ) ∣ dot a x} = ∅ :=
        filter_eq_empty_iff.mpr fun d _ hd => hd.1 h0
      rw [this, card_empty, Nat.cast_zero]
      positivity
    · have hm : (dot a x).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr h0
      have hsub : {d ∈ Ioc (0 : ℕ) T | dot a x ≠ 0 ∧ ((d : ℕ) : ℤ) ∣ dot a x} ⊆ (dot a x).natAbs.divisors := by
        intro d hd
        simp only [mem_filter] at hd
        exact Nat.mem_divisors.mpr ⟨Int.ofNat_dvd_left.mp hd.2.2, hm⟩
      calc (#{d ∈ Ioc (0 : ℕ) T | dot a x ≠ 0 ∧ ((d : ℕ) : ℤ) ∣ dot a x} : ℝ)
          ≤ ((dot a x).natAbs.divisors.card : ℝ) := by exact_mod_cast card_le_card hsub
        _ ≤ C * ((dot a x).natAbs : ℝ) ^ δ := hC _ hm
        _ ≤ C * (T : ℝ) ^ δ := by
          gcongr
          exact_mod_cast hT x hx
  calc (∑ d ∈ Ioc 0 T, (Upcount a h d : ℝ)) = ((∑ d ∈ Ioc 0 T, Upcount a h d : ℕ) : ℝ) := by
        push_cast; rfl
    _ = ∑ x ∈ boxVecs n h, (#{d ∈ Ioc (0 : ℕ) T | dot a x ≠ 0 ∧ ((d : ℕ) : ℤ) ∣ dot a x} : ℝ) := by
        rw [hswap]; push_cast; rfl
    _ ≤ ∑ _x ∈ boxVecs n h, C * (T : ℝ) ^ δ := sum_le_sum hpt
    _ = _ := by rw [sum_const, card_boxVecs, nsmul_eq_mul]; push_cast; ring

/-! ### The series `∑ μ(d)/d²` -/

lemma abs_moebius_div_sq_le (d : ℕ) : |(μ d : ℝ) / (d : ℝ) ^ 2| ≤ 1 / (d : ℝ) ^ 2 := by
  rw [abs_div, abs_of_nonneg (sq_nonneg (d : ℝ))]
  exact div_le_div_of_nonneg_right (by exact_mod_cast abs_moebius_le_one) (sq_nonneg _)

lemma summable_moebius_div_sq : Summable fun d : ℕ => (μ d : ℝ) / (d : ℝ) ^ 2 :=
  Summable.of_norm_bounded (g := fun d : ℕ => 1 / (d : ℝ) ^ 2)
    (Real.summable_one_div_nat_pow.mpr one_lt_two) fun d => by
      rw [Real.norm_eq_abs]; exact abs_moebius_div_sq_le d

lemma tsum_moebius_div_sq : ∑' d : ℕ, (μ d : ℝ) / (d : ℝ) ^ 2 = (riemannZeta 2).re⁻¹ := by
  have h1 := LSeries_zeta_mul_Lseries_moebius (s := 2) (by norm_num)
  rw [LSeries_zeta_eq_riemannZeta (by norm_num)] at h1
  have h2 : LSeries (fun n => ((μ n : ℤ) : ℂ)) 2 =
      ((∑' d : ℕ, (μ d : ℝ) / (d : ℝ) ^ 2 : ℝ) : ℂ) := by
    rw [LSeries, Complex.ofReal_tsum]
    congr 1
    ext d
    rcases eq_or_ne d 0 with rfl | hd
    · simp
    · rw [LSeries.term_of_ne_zero hd, Complex.cpow_two]
      push_cast
      rfl
  rw [h2, riemannZeta_two] at h1
  generalize (∑' d : ℕ, (μ d : ℝ) / (d : ℝ) ^ 2) = S at h1 ⊢
  have h3 : (riemannZeta 2).re = Real.pi ^ 2 / 6 := by
    rw [riemannZeta_two]
    norm_cast
  rw [h3]
  have h5 : Real.pi ^ 2 / 6 * S = 1 := by exact_mod_cast h1
  have hpi : Real.pi ^ 2 / 6 ≠ 0 := by positivity
  field_simp
  linarith

lemma one_div_sq_le (x : ℝ) (hx : 1 ≤ x) : 1 / (x + 1) ^ 2 ≤ 1 / x - 1 / (x + 1) := by
  have hx0 : 0 < x := by linarith
  rw [div_sub_div _ _ hx0.ne' (by linarith), one_mul, mul_one, add_sub_cancel_left]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

lemma abs_tsum_moebius_sub_le (h : ℕ) (hh : 1 ≤ h) :
    |∑' d : ℕ, (μ d : ℝ) / (d : ℝ) ^ 2 - ∑ d ∈ range (h + 1), (μ d : ℝ) / (d : ℝ) ^ 2| ≤
      1 / h := by
  set f : ℕ → ℝ := fun d => (μ d : ℝ) / (d : ℝ) ^ 2
  have hs := summable_moebius_div_sq
  rw [← hs.sum_add_tsum_nat_add (h + 1), add_sub_cancel_left]
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hpt : ∀ i : ℕ, |f (i + (h + 1))| ≤ 1 / ((i : ℝ) + h) - 1 / ((i : ℝ) + h + 1) := by
    intro i
    have hi : (1 : ℝ) ≤ (i : ℝ) + h := by have : (0 : ℝ) ≤ i := i.cast_nonneg; linarith
    calc |f (i + (h + 1))| ≤ 1 / ((i : ℝ) + h + 1) ^ 2 := by
          have := abs_moebius_div_sq_le (i + (h + 1))
          push_cast at this
          rw [show (i : ℝ) + (h + 1) = (i : ℝ) + h + 1 by ring] at this
          simp only [f]; push_cast
          rwa [show (i : ℝ) + (h + 1) = (i : ℝ) + h + 1 by ring]
      _ ≤ _ := one_div_sq_le _ hi
  have hsum : Summable fun i => |f (i + (h + 1))| :=
    ((summable_nat_add_iff (h + 1)).mpr hs).abs
  calc |∑' i, f (i + (h + 1))| ≤ ∑' i, |f (i + (h + 1))| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm
          (f := fun i => f (i + (h + 1))) (by simpa only [Real.norm_eq_abs] using hsum)
    _ ≤ 1 / h := by
        refine Real.tsum_le_of_sum_range_le (fun _ => abs_nonneg _) fun N => ?_
        calc ∑ i ∈ range N, |f (i + (h + 1))|
            ≤ ∑ i ∈ range N, (1 / ((i : ℝ) + h) - 1 / (((i + 1 : ℕ) : ℝ) + h)) := by
              refine sum_le_sum fun i _ => ?_
              have := hpt i
              push_cast
              rwa [show (i : ℝ) + 1 + h = (i : ℝ) + h + 1 by ring]
          _ = 1 / ((0 : ℕ) + (h : ℝ)) - 1 / ((N : ℕ) + (h : ℝ)) :=
              sum_range_sub' (fun i : ℕ => 1 / ((i : ℝ) + h)) N
          _ ≤ 1 / h := by
              simp only [Nat.cast_zero, zero_add]
              have : 0 ≤ 1 / ((N : ℝ) + h) := by positivity
              linarith

end ShiftedGcd
