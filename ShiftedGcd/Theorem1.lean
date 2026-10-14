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

lemma gammaBH_denom_ge (K : ℝ) : 4 ≤ (2:ℝ) ^ (2 + max 1 K) - 4 := by
  have : (2:ℝ) ^ (3:ℝ) ≤ (2:ℝ) ^ (2 + max 1 K) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [le_max_left 1 K])
  have h8 : (2:ℝ) ^ (3:ℝ) = 8 := by norm_num
  linarith

lemma gammaBH_pos (K : ℝ) : 0 < gammaBH K := by
  unfold gammaBH; have := gammaBH_denom_ge K; positivity

lemma gammaBH_le (K : ℝ) : gammaBH K ≤ 1 / 4 := by
  unfold gammaBH; exact one_div_le_one_div_of_le (by norm_num) (gammaBH_denom_ge K)

lemma gammaBH_antitone : Antitone gammaBH := by
  intro x y hxy
  unfold gammaBH
  apply one_div_le_one_div_of_le (by linarith [gammaBH_denom_ge x])
  have := Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num)
    (show 2 + max 1 x ≤ 2 + max 1 y by linarith [max_le_max (le_refl (1:ℝ)) hxy])
  linarith

lemma gammaBH_continuous : Continuous gammaBH := by
  unfold gammaBH
  refine continuous_const.div ?_ (fun K => by have := gammaBH_denom_ge K; intro h; linarith)
  exact (continuous_const.rpow (continuous_const.add (continuous_const.max continuous_id))
    (fun _ => Or.inl (by norm_num))).sub continuous_const

/-- Equation (2) has a unique positive solution. -/
theorem kappa_existsUnique {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃! κ, IsKappa n ε κ := by
  have hn1 : (1:ℝ) < n := by exact_mod_cast hn
  set f : ℝ → ℝ := fun κ => (n:ℝ) * (ε * κ - 1) / ((n:ℝ) - 1) - gammaBH κ with hf
  have hfc : Continuous f := by
    refine Continuous.sub ?_ gammaBH_continuous
    exact (continuous_const.mul ((continuous_const.mul continuous_id).sub continuous_const)).div_const _
  have hfmono : StrictMono f := by
    intro x y hxy
    have h1 : (n:ℝ) * (ε * x - 1) / ((n:ℝ) - 1) < (n:ℝ) * (ε * y - 1) / ((n:ℝ) - 1) := by
      apply div_lt_div_of_pos_right _ (by linarith)
      apply mul_lt_mul_of_pos_left _ (by linarith); nlinarith
    have h2 := gammaBH_antitone hxy.le
    simp only [hf]; linarith
  have hf0 : f 0 < 0 := by
    have : (n:ℝ) * (ε * 0 - 1) / ((n:ℝ) - 1) < 0 := by
      apply div_neg_of_neg_of_pos _ (by linarith); simp; linarith
    simp only [hf]; linarith [gammaBH_pos 0]
  have hf1 : 0 < f (2 / ε) := by
    have e1 : ε * (2 / ε) - 1 = 1 := by field_simp; ring
    have : 1 ≤ (n:ℝ) * (ε * (2 / ε) - 1) / ((n:ℝ) - 1) := by
      rw [e1, le_div_iff₀ (by linarith)]; linarith
    simp only [hf]; linarith [gammaBH_le (2 / ε)]
  obtain ⟨κ, hκmem, hκ⟩ := intermediate_value_Icc (le_of_lt (by positivity : (0:ℝ) < 2 / ε))
    hfc.continuousOn ⟨hf0.le, hf1.le⟩
  have hκpos : 0 < κ := by
    rcases hκmem.1.eq_or_lt with h | h
    · subst h; linarith
    · exact h
  refine ⟨κ, ⟨hκpos, by simp only [hf] at hκ; linarith⟩, ?_⟩
  rintro κ' ⟨_, hκ'⟩
  exact hfmono.injective (by simp only [hf] at hκ ⊢; linarith)

theorem isKappa_kappa {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    IsKappa n ε (kappa n ε) := by
  have h := (kappa_existsUnique hn hε0 hε1).exists
  unfold kappa
  simp only [h, ↓reduceDIte]
  exact h.choose_spec

theorem one_lt_eps_mul_kappa {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    1 < ε * kappa n ε := by
  have hn1 : (1:ℝ) < n := by exact_mod_cast hn
  have hK := (isKappa_kappa hn hε0 hε1).2
  by_contra h
  have h := not_lt.1 h
  have : (n:ℝ) * (ε * kappa n ε - 1) / ((n:ℝ) - 1) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith))
      (by linarith)
  linarith [gammaBH_pos (kappa n ε)]

theorem theta_pos {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    0 < theta n ε := by
  have hn1 : (1:ℝ) < n := by exact_mod_cast hn
  have h := one_lt_eps_mul_kappa hn hε0 hε1
  unfold theta
  apply div_pos _ (by linarith)
  have : 1 / (ε * kappa n ε) < 1 := (div_lt_one (by linarith)).2 h
  linarith


lemma height_zero {n : ℕ} : height (0 : Fin n → ℤ) = 0 := by simp [height]

lemma natAbs_le_height {n : ℕ} (x : Fin n → ℤ) (i : Fin n) :
    ((x i).natAbs : ℝ) ≤ height x := by
  exact_mod_cast Finset.le_sup (f := fun i => (x i).natAbs) (mem_univ i)

lemma height_le_of_abs_le {n : ℕ} (x : Fin n → ℤ) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ i, |(x i : ℝ)| ≤ B) : (height x : ℝ) ≤ B := by
  unfold height
  rcases (Finset.univ : Finset (Fin n)).eq_empty_or_nonempty with he | hne
  · simp [he, hB]
  · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup _ hne (fun i => (x i).natAbs)
    rw [hi, Nat.cast_natAbs, Int.cast_abs]
    exact h i

lemma exists_shift (x : ℤ) (r : ℕ) (hr : 0 < r) (ψ : ℝ)
    (h : distNearestInt ((x.natAbs : ℝ) / r) ≤ ψ) :
    ∃ y : ℤ, (r : ℤ) ∣ x + y ∧ |(y : ℝ)| ≤ r * ψ := by
  set m := round ((x.natAbs : ℝ) / r)
  have hr' : (0:ℝ) < r := by exact_mod_cast hr
  have key : |(((r : ℤ) * m - (x.natAbs : ℤ) : ℤ) : ℝ)| ≤ r * ψ := by
    unfold distNearestInt at h
    have : (((r : ℤ) * m - (x.natAbs : ℤ) : ℤ) : ℝ) = -(r * ((x.natAbs : ℝ) / r - m)) := by
      rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_natCast]; field_simp; ring
    rw [this, abs_neg, abs_mul, abs_of_pos hr']
    exact mul_le_mul_of_nonneg_left h hr'.le
  rcases Int.natAbs_eq x with hx | hx
  · exact ⟨(r : ℤ) * m - (x.natAbs : ℤ), ⟨m, by linarith⟩, key⟩
  · refine ⟨-((r : ℤ) * m - (x.natAbs : ℤ)), ⟨-m, by linarith⟩, ?_⟩
    rw [Int.cast_neg, abs_neg]; exact key


open Filter Topology in
/-- **Theorem 1** (strong form, as actually proved in the paper). -/
theorem theorem1 {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hBH : BakerHarman n (kappa n ε)) :
    ∃ c > 0, ∀ (a : Fin n → ℤ) (H : ℝ), 1 ≤ H → (height a : ℝ) ^ ε ≤ H →
      ∃ h : Fin n → ℤ, (height h : ℝ) ≤ H ∧ ∃ r : ℕ, (∀ i, (r : ℤ) ∣ a i + h i) ∧
        c * height h * H ^ theta n ε ≤ r ∧ c * H ^ (1 / (ε * kappa n ε)) ≤ r := by
  have hK := isKappa_kappa hn hε0 hε1
  have hK2 := hK.2
  have hεK := one_lt_eps_mul_kappa hn hε0 hε1
  have hθ0 := theta_pos hn hε0 hε1
  set K := kappa n ε with hKdef
  obtain ⟨C₁, c₂, R₀, hc₂, hBH'⟩ := hBH
  have hn1 : (1:ℝ) < n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hn10 : (n:ℝ) - 1 ≠ 0 := by linarith
  have hKpos : 0 < K := hK.1
  have hK1 : 1 ≤ K := by nlinarith
  have hεK0 : ε * K ≠ 0 := by positivity
  set s := 1 / (ε * K) with hs
  have hs0 : 0 < s := by positivity
  have hsK : s * K = ε⁻¹ := by rw [hs]; field_simp
  set γ := gammaBH K with hγ
  have hγ0 : 0 < γ := gammaBH_pos K
  set θ := theta n ε with hθ
  have hθdef : θ = (1 - s) / ((n:ℝ) - 1) := rfl
  have hkey : (n:ℝ) * θ = γ * s := by
    rw [hθdef, hs, ← hK2]; field_simp
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1.le
  set L := (Real.log 2 + Real.log n) / ((n:ℝ) - 1) with hL
  have hL0 : 0 ≤ L := by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    rw [hL]; apply div_nonneg (by linarith) (by linarith)
  have h1 : ((n:ℝ) - 1) * θ = 1 - s := by rw [hθdef]; field_simp
  have h2 : ((n:ℝ) - 1) * L = Real.log 2 + Real.log n := by rw [hL]; field_simp
  -- threshold for the condition on `ψ`
  have hlim := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n
  obtain ⟨W, hW⟩ := eventually_atTop.1
    (hlim.eventually (gt_mem_nhds (show (0:ℝ) < c₂ / (n:ℝ) ^ n by positivity)))
  set Wst := max (max W 1) (Real.log (max C₁ 1)) with hWst
  set t₀ := max ((Wst + L) / θ) (Real.log (max R₀ 1) / s) with ht₀def
  have ht₀ : 0 ≤ t₀ := by
    have : 1 ≤ Wst := le_trans (le_max_right _ _) (le_max_left _ _)
    exact le_trans (div_nonneg (by linarith) hθ0.le) (le_max_left _ _)
  refine ⟨Real.exp (-L - t₀ * s), Real.exp_pos _, ?_⟩
  intro a H hH1 hHa
  obtain ⟨t, rfl⟩ : ∃ t, H = Real.exp t := ⟨Real.log H, (Real.exp_log (by linarith)).symm⟩
  have ht0 : 0 ≤ t := by have := Real.log_nonneg hH1; rwa [Real.log_exp] at this
  have hts : 0 ≤ t₀ * s := mul_nonneg ht₀ hs0.le
  by_cases ht : t₀ ≤ t
  swap
  · -- small `H`: take `h = 0`, `r = 1`
    refine ⟨0, ?_, 1, fun i => one_dvd _, ?_, ?_⟩
    · rw [height_zero, Nat.cast_zero]; positivity
    · rw [height_zero]; simp
    · rw [← Real.exp_mul, ← Real.exp_add, Nat.cast_one, Real.exp_le_one_iff]
      have : t * s ≤ t₀ * s := mul_le_mul_of_nonneg_right (le_of_lt (not_le.1 ht)) hs0.le
      linarith
  -- large `H`: apply Baker–Harman
  set w := θ * t - L with hw
  have hwW : Wst ≤ w := by
    have : (Wst + L) / θ ≤ t := le_trans (le_max_left _ _) ht
    rw [div_le_iff₀ hθ0] at this; rw [hw]; linarith
  have hw1 : 1 ≤ w := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hwW
  have hwW' : W ≤ w := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hwW
  have hwC : Real.log (max C₁ 1) ≤ w := le_trans (le_max_right _ _) hwW
  have hst : Real.log (max R₀ 1) ≤ s * t := by
    have : Real.log (max R₀ 1) / s ≤ t := le_trans (le_max_right _ _) ht
    rw [div_le_iff₀ hs0] at this; linarith
  set u := (n:ℝ) * w with hu
  set v := Real.log n + s * t with hv
  have hu0 : 0 < u := by positivity
  set a' : Fin n → ℕ := fun i => if a i = 0 then 1 else (a i).natAbs with ha'
  have ha'pos : ∀ i, 0 < a' i := by
    intro i; simp only [ha']; split_ifs with h
    · norm_num
    · exact Int.natAbs_pos.2 h
  have hha : (height a : ℝ) ≤ Real.exp (t * ε⁻¹) := by
    have e : (height a : ℝ) = ((height a : ℝ) ^ ε) ^ ε⁻¹ :=
      (Real.rpow_rpow_inv (Nat.cast_nonneg _) hε0.ne').symm
    rw [e, Real.exp_mul]
    exact Real.rpow_le_rpow (by positivity) hHa (by positivity)
  have hM : ∀ i, (a' i : ℝ) ≤ Real.exp (t * ε⁻¹) := by
    intro i; simp only [ha']; split_ifs with h
    · rw [Nat.cast_one]; exact Real.one_le_exp (by positivity)
    · exact (natAbs_le_height a i).trans hha
  have hsqrt : Real.sqrt (∑ i, ((a' i : ℝ)) ^ 2) ≤ (Real.exp v) ^ K := by
    rw [← Real.exp_mul]
    have hvK : v * K = Real.log n * K + t * ε⁻¹ := by
      have : v * K = Real.log n * K + t * (s * K) := by rw [hv]; ring
      rw [this, hsK]
    rw [hvK, Real.exp_add]
    have hnK : (n:ℝ) ≤ Real.exp (Real.log n * K) := by
      calc (n:ℝ) = Real.exp (Real.log n) := (Real.exp_log hn0).symm
        _ ≤ _ := Real.exp_le_exp.2 (le_mul_of_one_le_right hlogn hK1)
    set E := Real.exp (t * ε⁻¹)
    have hE : 0 < E := Real.exp_pos _
    apply Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    calc ∑ i, (a' i : ℝ) ^ 2 ≤ ∑ _i : Fin n, E ^ 2 :=
          Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (Nat.cast_nonneg _) (hM i) 2)
      _ = n * E ^ 2 := by simp
      _ ≤ (n * E) ^ 2 := by
          rw [mul_pow]; exact mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
      _ ≤ (Real.exp (Real.log n * K) * E) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hnK hE.le) 2
  have hR₀ : R₀ ≤ Real.exp v :=
    calc R₀ ≤ max R₀ 1 := le_max_left _ _
      _ = Real.exp (Real.log (max R₀ 1)) :=
          (Real.exp_log (lt_of_lt_of_le one_pos (le_max_right _ _))).symm
      _ ≤ Real.exp v := Real.exp_le_exp.2 (by rw [hv]; linarith)
  have hC₁ : C₁ ≤ Real.exp u :=
    calc C₁ ≤ max C₁ 1 := le_max_left _ _
      _ = Real.exp (Real.log (max C₁ 1)) :=
          (Real.exp_log (lt_of_lt_of_le one_pos (le_max_right _ _))).symm
      _ ≤ Real.exp u := Real.exp_le_exp.2 (by
          have : w ≤ n * w := le_mul_of_one_le_left (by linarith) hn1.le
          rw [hu]; linarith)
  have hQR : Real.exp u ≤ (Real.exp v) ^ γ := by
    rw [← Real.exp_mul]
    apply Real.exp_le_exp.2
    have e1 : u = γ * s * t - n * L := by rw [hu, hw, mul_sub, ← mul_assoc, hkey]
    have e2 : v * γ = γ * Real.log n + γ * s * t := by rw [hv]; ring
    rw [e1, e2]
    linarith [mul_nonneg hγ0.le hlogn, mul_nonneg hn0.le hL0]
  have hψ : ∀ i : Fin n, (fun _ => Real.exp (-w)) i ≤ c₂ * (Real.log (Real.exp u))⁻¹ ^ n := by
    intro i
    simp only
    rw [Real.log_exp, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    have hWw := hW w hwW'
    have := (lt_div_iff₀ (by positivity)).1 hWw
    rw [hu, mul_pow]
    have e : Real.exp (-w) * ((n:ℝ) ^ n * w ^ n) = w ^ n * Real.exp (-w) * (n:ℝ) ^ n := by ring
    linarith
  have hprod : ∏ _i : Fin n, Real.exp (-w) = (Real.exp u)⁻¹ := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul,
      ← Real.exp_neg, hu]
    congr 1; ring
  obtain ⟨r, hRr, hr2, hdist⟩ := hBH' a' ha'pos (Real.exp u) (Real.exp v) hR₀ hsqrt hC₁ hQR
    (fun _ => Real.exp (-w)) (fun _ => Real.exp_pos _) hψ hprod
  have hrpos : 0 < r := by
    have : 0 < (r:ℝ) := lt_of_lt_of_le (Real.exp_pos _) hRr
    exact_mod_cast this
  have hshift : ∀ i, ∃ y : ℤ, (r:ℤ) ∣ a i + y ∧ |(y:ℝ)| ≤ r * Real.exp (-w) := by
    intro i
    by_cases hai : a i = 0
    · exact ⟨0, by simp [hai], by simp; positivity⟩
    · have := hdist i
      simp only [ha', hai, ↓reduceIte] at this
      exact exists_shift (a i) r hrpos _ this
  choose h hhdvd hhabs using hshift
  have hhgt : (height h : ℝ) ≤ r * Real.exp (-w) :=
    height_le_of_abs_le h _ (by positivity) hhabs
  have hrw : (r:ℝ) * Real.exp (-w) ≤ Real.exp t := by
    calc (r:ℝ) * Real.exp (-w) ≤ 2 * Real.exp u * Real.exp v * Real.exp (-w) :=
          mul_le_mul_of_nonneg_right hr2 (Real.exp_pos _).le
      _ = Real.exp t := by
          rw [← Real.exp_log (show (0:ℝ) < 2 by norm_num), ← Real.exp_add, ← Real.exp_add,
            ← Real.exp_add]
          congr 1
          rw [hu, hv, hw]
          linear_combination t * h1 - h2
  refine ⟨h, hhgt.trans hrw, r, hhdvd, ?_, ?_⟩
  · have hcH : Real.exp (-L - t₀ * s) * Real.exp t ^ θ ≤ Real.exp w := by
      rw [← Real.exp_mul, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by rw [hw]; linarith)
    calc Real.exp (-L - t₀ * s) * height h * Real.exp t ^ θ
        = height h * (Real.exp (-L - t₀ * s) * Real.exp t ^ θ) := by ring
      _ ≤ height h * Real.exp w := mul_le_mul_of_nonneg_left hcH (Nat.cast_nonneg _)
      _ ≤ (r * Real.exp (-w)) * Real.exp w := mul_le_mul_of_nonneg_right hhgt (Real.exp_pos _).le
      _ = r := by rw [mul_assoc, ← Real.exp_add]; simp
  · calc Real.exp (-L - t₀ * s) * Real.exp t ^ s = Real.exp (-L - t₀ * s + t * s) := by
          rw [← Real.exp_mul, ← Real.exp_add]
      _ ≤ Real.exp v := Real.exp_le_exp.2 (by
          have : t * s = s * t := mul_comm _ _
          rw [hv]; linarith)
      _ ≤ r := hRr

/-- **Theorem 1** (gcd form): for `𝔥(a)^ε ≤ H < 𝔥(a)` there is a shift `h` with `𝔥(h) ≤ H` and
`gcd(a + h) ≫ 𝔥(h) H^ϑ`, and moreover `gcd(a + h) ≫ H^{1/(εκ)}`. -/
theorem theorem1_gcd {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hBH : BakerHarman n (kappa n ε)) :
    ∃ c > 0, ∀ (a : Fin n → ℤ) (H : ℝ), 1 ≤ H → (height a : ℝ) ^ ε ≤ H → H < height a →
      ∃ h : Fin n → ℤ, (height h : ℝ) ≤ H ∧
        c * height h * H ^ theta n ε ≤ vgcd (a + h) ∧
        c * H ^ (1 / (ε * kappa n ε)) ≤ vgcd (a + h) := by
  obtain ⟨c, hc, hmain⟩ := theorem1 hn hε0 hε1 hBH
  refine ⟨c, hc, fun a H hH1 hHa hHlt => ?_⟩
  obtain ⟨h, hhH, r, hdvd, hr1, hr2⟩ := hmain a H hH1 hHa
  have hne : ∃ i, a i + h i ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have hh : h = -a := funext fun i => by have := hcon i; simp only [Pi.neg_apply]; linarith
    have e : height h = height a := by rw [hh]; simp [height, Int.natAbs_neg]
    have : (height h : ℝ) = height a := by exact_mod_cast e
    linarith
  have hrd : r ∣ vgcd (a + h) :=
    Finset.dvd_gcd (fun i _ => Int.natCast_dvd.1 (hdvd i))
  have hv0 : vgcd (a + h) ≠ 0 := by
    obtain ⟨i, hi⟩ := hne
    intro h0
    rw [vgcd, Finset.gcd_eq_zero_iff] at h0
    exact hi (Int.natAbs_eq_zero.1 (h0 i (mem_univ i)))
  have hle : (r:ℝ) ≤ vgcd (a + h) := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hv0) hrd
  exact ⟨h, hhH, hr1.trans hle, hr2.trans hle⟩

end ShiftedGcd
