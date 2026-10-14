import ShiftedGcd.Defs

/-!
# The abstract's claim

The paper's abstract says: "we show that for any choice of `a₁, …, aₙ` there are shifts of this
type [`|hᵢ| ≤ H`] for which the greatest common divisor of `a₁ + h₁, …, aₙ + hₙ` is much larger
than `H`."

This is false, even under the hypotheses of Theorem 1 (`𝔥(a)^ε ≤ H < 𝔥(a)`) and with all
`aᵢ` positive and large. Take `a = (A, A + 2H + 1, A, …, A)`. Then `gcd(a + h)` divides
`(a₂ + h₂) - (a₁ + h₁) = 2H + 1 + h₂ - h₁`, which lies in `[1, 4H + 1]`. So `gcd(a + h) ≤ 4H + 1`
for every admissible shift (`abstract_claim_false`). In particular no bound
`gcd(a + h) ≫ H^{1+η}` holds (`not_gcd_much_larger`).

Conversely, `gcd(a + h) ≥ 2H + 1` is always attainable when `H < 𝔥(a)`: shift every entry to a
multiple of `2H + 1` (`exists_shift_vgcd_ge`). So in the worst case the largest attainable gcd
is `Θ(H)`.

This is probably a typo. The paper writes the height as a script `ℋ`, and "much larger than
`ℋ(h)`" is exactly what Theorem 1 says: `gcd(a + h) ≫ 𝔥(h) H^ϑ`. Our `theorem1` formalises
that reading. The sentence was added in the journal version; the arXiv abstract does not contain
it.
-/

open Finset

namespace ShiftedGcd

variable {n : ℕ}

private lemma natAbs_le_height (x : Fin n → ℤ) (i : Fin n) : (x i).natAbs ≤ height x :=
  Finset.le_sup (f := fun i => (x i).natAbs) (mem_univ i)

private lemma vgcd_dvd (x : Fin n → ℤ) (i : Fin n) : (vgcd x : ℤ) ∣ x i :=
  Int.natCast_dvd.2 (Finset.gcd_dvd (mem_univ i))

/-- Trivial lower bound: if `H < 𝔥(a)`, some shift of height `≤ H` gives `gcd(a + h) ≥ 2H + 1`. -/
theorem exists_shift_vgcd_ge (a : Fin n → ℤ) (H : ℕ) (hH : H < height a) :
    ∃ h : Fin n → ℤ, height h ≤ H ∧ 2 * H + 1 ≤ vgcd (a + h) := by
  set g : ℕ := 2 * H + 1 with hg
  have hg0 : (0 : ℤ) < g := by positivity
  -- centred remainder: `h i ∈ [-H, H]` with `g ∣ a i + h i`
  let h : Fin n → ℤ := fun i => if a i % g ≤ H then -(a i % g) else g - a i % g
  have hdvd : ∀ i, (g : ℤ) ∣ a i + h i := by
    intro i
    have := Int.emod_def (a i) g
    simp only [h]
    split_ifs
    · exact ⟨a i / g, by linarith⟩
    · exact ⟨a i / g + 1, by linarith⟩
  have hbd : ∀ i, (h i).natAbs ≤ H := by
    intro i
    have h1 := Int.emod_nonneg (a i) hg0.ne'
    have h2 := Int.emod_lt_of_pos (a i) hg0
    simp only [h]
    split_ifs with hc <;> omega
  refine ⟨h, Finset.sup_le fun i _ => hbd i, ?_⟩
  have hgd : g ∣ vgcd (a + h) :=
    Finset.dvd_gcd fun i _ => Int.natCast_dvd.1 (hdvd i)
  -- `a + h ≠ 0`: the coordinate where `|aᵢ| = 𝔥(a) > H` stays nonzero
  have hne : (univ : Finset (Fin n)).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    simp [height, hemp] at hH
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup _ hne fun i => (a i).natAbs
  have hv0 : vgcd (a + h) ≠ 0 := by
    intro h0
    rw [vgcd, Finset.gcd_eq_zero_iff] at h0
    have := h0 i (mem_univ i)
    have := hbd i
    simp only [Pi.add_apply, Int.natAbs_eq_zero] at *
    rw [height] at hH
    omega
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hv0) hgd

/-- If two entries of `a` differ by exactly `2H + 1`, every shift of height `≤ H` has
`gcd(a + h) ≤ 4H + 1`. -/
theorem vgcd_shift_le_of_gap (a : Fin n → ℤ) (i j : Fin n) (H : ℕ)
    (hgap : a j - a i = 2 * H + 1) (h : Fin n → ℤ) (hh : height h ≤ H) :
    vgcd (a + h) ≤ 4 * H + 1 := by
  have hi := (natAbs_le_height h i).trans hh
  have hj := (natAbs_le_height h j).trans hh
  have hd : (vgcd (a + h) : ℤ) ∣ (a + h) j - (a + h) i :=
    dvd_sub (vgcd_dvd _ j) (vgcd_dvd _ i)
  have hpos : 0 < (a + h) j - (a + h) i := by simp only [Pi.add_apply]; omega
  have := Int.le_of_dvd hpos hd
  simp only [Pi.add_apply] at this
  omega

/-- **The abstract's claim is false.** For `n ≥ 2` and `0 < ε < 1`, for every large `H` there is
`a` with positive entries and `𝔥(a)^ε ≤ H < 𝔥(a)` (the setting of Theorem 1) such that every
shift `h` with `𝔥(h) ≤ H` has `gcd(a + h) ≤ 4H + 1`. -/
theorem abstract_claim_false (hn : 2 ≤ n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ H₀ : ℕ, ∀ H : ℕ, H₀ ≤ H → ∃ a : Fin n → ℤ, (∀ i, 0 < a i) ∧
      (height a : ℝ) ^ ε ≤ H ∧ H < height a ∧
      ∀ h : Fin n → ℤ, height h ≤ H → vgcd (a + h) ≤ 4 * H + 1 := by
  set p : ℝ := 1 / ε - 1 with hp
  have hp0 : 0 < p := by rw [hp, sub_pos, lt_div_iff₀ hε0]; linarith
  refine ⟨⌈(4 : ℝ) ^ (1 / p)⌉₊ + 1, fun H hH => ?_⟩
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast (Nat.le_add_left 1 _).trans hH
  -- `H^{1/ε} ≥ 4H ≥ 2H + 2`
  have hpow : (4 : ℝ) ≤ (H : ℝ) ^ p := by
    have h4 : (4 : ℝ) ^ (1 / p) ≤ H :=
      (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_add_right _ 1).trans hH)
    calc (4 : ℝ) = ((4 : ℝ) ^ (1 / p)) ^ p := by
            rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hp0.ne', Real.rpow_one]
      _ ≤ (H : ℝ) ^ p := Real.rpow_le_rpow (by positivity) h4 hp0.le
  have hbig : 2 * (H : ℝ) + 2 ≤ (H : ℝ) ^ (1 / ε) := by
    have : (H : ℝ) ^ (1 / ε) = H * H ^ p := by
      rw [hp, Real.rpow_sub (by linarith), Real.rpow_one]; field_simp
    rw [this]; nlinarith
  set B : ℕ := ⌊(H : ℝ) ^ (1 / ε)⌋₊ with hB
  have hB2 : 2 * H + 2 ≤ B := by
    rw [hB]; apply Nat.le_floor; push_cast; exact hbig
  have hBle : (B : ℝ) ≤ (H : ℝ) ^ (1 / ε) := Nat.floor_le (by positivity)
  -- `a = (A, A + 2H + 1, A, …, A)` with `A + 2H + 1 = B`
  set A : ℤ := (B : ℤ) - (2 * H + 1) with hA
  have hA1 : 1 ≤ A := by omega
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let a : Fin n → ℤ := fun i => if i = i1 then A + (2 * H + 1) else A
  have hne : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have hAB : A + (2 * H + 1) = (B : ℤ) := by rw [hA]; ring
  have hht : height a = B := by
    apply le_antisymm
    · refine Finset.sup_le fun i _ => ?_
      simp only [a]; split_ifs <;> omega
    · have h1 : (a i1).natAbs = B := by simp [a, hAB]
      exact h1 ▸ natAbs_le_height a i1
  refine ⟨a, fun i => by simp only [a]; split_ifs <;> omega, ?_, by omega, ?_⟩
  · rw [hht]
    calc (B : ℝ) ^ ε ≤ ((H : ℝ) ^ (1 / ε)) ^ ε := Real.rpow_le_rpow (by positivity) hBle hε0.le
      _ = H := by rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hε0.ne', Real.rpow_one]
  · intro h hh
    exact vgcd_shift_le_of_gap a i0 i1 H (by simp [a, i0, i1, Fin.ext_iff]) h hh

/-- No bound of the form `gcd(a + h) ≫ H^{1+η}` holds in the setting of Theorem 1, even for
vectors with positive entries. -/
theorem not_gcd_much_larger (hn : 2 ≤ n) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ¬ ∃ η : ℝ, 0 < η ∧ ∃ c : ℝ, 0 < c ∧ ∀ (a : Fin n → ℤ) (H : ℝ), (∀ i, 0 < a i) → 1 ≤ H →
      (height a : ℝ) ^ ε ≤ H → H < height a →
      ∃ h : Fin n → ℤ, (height h : ℝ) ≤ H ∧ c * H ^ (1 + η) ≤ vgcd (a + h) := by
  rintro ⟨η, hη, c, hc, hclaim⟩
  obtain ⟨H₀, hH₀⟩ := abstract_claim_false hn hε0 hε1
  set H : ℕ := max H₀ (⌈(5 / c) ^ (1 / η)⌉₊ + 1)
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast (Nat.le_add_left 1 _).trans (le_max_right _ _)
  have hHη : 5 / c < (H : ℝ) ^ η := by
    have hlt : (5 / c) ^ (1 / η) < H := by
      have hc' : ⌈(5 / c) ^ (1 / η)⌉₊ < H := by omega
      exact (Nat.le_ceil _).trans_lt (by exact_mod_cast hc')
    calc 5 / c = ((5 / c) ^ (1 / η)) ^ η := by
            rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hη.ne', Real.rpow_one]
      _ < (H : ℝ) ^ η := Real.rpow_lt_rpow (by positivity) hlt hη
  obtain ⟨a, hpos, hε, hlt, hbound⟩ := hH₀ H (le_max_left _ _)
  obtain ⟨h, hh, hge⟩ := hclaim a H hpos hH1 hε (by exact_mod_cast hlt)
  have hle := hbound h (by exact_mod_cast hh)
  have : c * (H : ℝ) ^ (1 + η) = c * H * H ^ η := by
    rw [Real.rpow_add (by linarith), Real.rpow_one]; ring
  have h5 : 5 * (H : ℝ) < c * H * H ^ η := by
    have := mul_lt_mul_of_pos_left hHη (by positivity : (0 : ℝ) < c * H)
    rwa [show c * H * (5 / c) = 5 * H by field_simp] at this
  have : (vgcd (a + h) : ℝ) ≤ 4 * H + 1 := by exact_mod_cast hle
  nlinarith

end ShiftedGcd
