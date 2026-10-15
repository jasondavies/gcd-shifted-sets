import ShiftedGcd.Iwaniec

/-!
# Theorem 2: small shifts making a vector pairwise coprime

Uses Lemma 6 (Iwaniec's bound for the Jacobsthal function), proved as `iwaniecBound`
from the vendored quadratic Jacobsthal bound.

The bound `L(a) ≪ log² 𝔥(a)` needs `𝔥(a) ≥ 2`: for `a = 0 ∈ ℤ²` we have `L(a) = 1`. The implied
constant depends on `n`.

The paper's construction (`h₁ = 0`, then each `hᵢ ≥ 0` minimal with `aᵢ + hᵢ` coprime to
`∏_{j<i} (aⱼ + hⱼ)`) needs a small repair when some `aⱼ + hⱼ = 0`. The shifted entries must be
kept nonzero.
-/

open Finset

namespace ShiftedGcd

/-! ### Auxiliary lemmas -/

namespace Thm2

/-- The window length used with Iwaniec's bound. -/
noncomputable def winLen (C : ℝ) (r : ℕ) : ℕ := ⌊C * ((r : ℝ) * Real.log r) ^ 2⌋₊ + 2

lemma no_run (C : ℝ)
    (hC : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → 2 ≤ S.card →
      ∀ (x : ℤ) (m : ℕ), (∀ k < m, ∃ p ∈ S, (p : ℤ) ∣ x + k) →
        (m : ℝ) ≤ C * ((S.card : ℝ) * Real.log S.card) ^ 2)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (y : ℤ) :
    ¬ ∀ k < winLen C S.card, ∃ p ∈ S, (p : ℤ) ∣ y + k := by
  intro H
  have hM : 2 ≤ winLen C S.card := by unfold winLen; omega
  rcases Nat.lt_or_ge S.card 2 with hc | hc
  · interval_cases h : S.card
    · obtain ⟨p, hp, -⟩ := H 0 (by omega)
      rw [Finset.card_eq_zero] at h
      simp [h] at hp
    · obtain ⟨q, rfl⟩ := Finset.card_eq_one.1 h
      obtain ⟨p, hp, h0⟩ := H 0 (by omega)
      obtain ⟨p', hp', h1⟩ := H 1 (by omega)
      simp only [Finset.mem_singleton] at hp hp'
      rw [hp] at h0
      rw [hp'] at h1
      have : (q : ℤ) ∣ 1 := by
        have := dvd_sub h1 h0
        simpa using this
      have hp1 : q ∣ 1 := by exact_mod_cast this
      exact (hS q (Finset.mem_singleton_self q)).one_lt.ne' (Nat.dvd_one.1 hp1)
  · have := hC S hS hc y _ H
    have h2 := Nat.lt_floor_add_one (C * ((S.card : ℝ) * Real.log S.card) ^ 2)
    unfold winLen at this
    push_cast at this
    linarith

lemma exists_shift_le_abs (P : ℤ) (hP : 2 ≤ P.natAbs) (c : ℤ) :
    ∃ k : ℕ, k ≤ P.natAbs ∧ Int.gcd (c + k) P = 1 := by
  set Pn : ℤ := (P.natAbs : ℤ) with hPn
  have hPpos : 0 < Pn := by omega
  refine ⟨((1 - c) % Pn).toNat, ?_, ?_⟩
  · have := Int.emod_lt_of_pos (1 - c) hPpos
    have := Int.emod_nonneg (1 - c) hPpos.ne'
    omega
  · have hk : ((((1 - c) % Pn).toNat : ℕ) : ℤ) = (1 - c) % Pn :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ hPpos.ne')
    rw [hk]
    have hcop : IsCoprime (c + (1 - c) % Pn) Pn := by
      refine ⟨1, (1 - c) / Pn, ?_⟩
      rw [Int.emod_def]
      ring
    have := Int.isCoprime_iff_gcd_eq_one.1 hcop
    unfold Int.gcd at this ⊢
    simpa [hPn, Int.natAbs_abs] using this

lemma exists_shift_lt_win (C : ℝ)
    (hC : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → 2 ≤ S.card →
      ∀ (x : ℤ) (m : ℕ), (∀ k < m, ∃ p ∈ S, (p : ℤ) ∣ x + k) →
        (m : ℝ) ≤ C * ((S.card : ℝ) * Real.log S.card) ^ 2)
    (P : ℤ) (hP : P ≠ 0) (c : ℤ) :
    ∃ k : ℕ, k < winLen C P.natAbs.primeFactors.card ∧ Int.gcd (c + k) P = 1 := by
  by_contra H
  push Not at H
  apply no_run C hC P.natAbs.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp) c
  intro k hk
  set g := Int.gcd (c + k) P with hg
  have hg1 : g ≠ 1 := H k hk
  have hgpos : 0 < g := Int.gcd_pos_of_ne_zero_right _ hP
  have hp := Nat.minFac_prime hg1
  refine ⟨g.minFac, ?_, ?_⟩
  · rw [Nat.mem_primeFactors]
    refine ⟨hp, ?_, Int.natAbs_ne_zero.2 hP⟩
    exact (Nat.minFac_dvd g).trans (Int.natCast_dvd.1 (Int.gcd_dvd_right _ _))
  · exact (Int.natCast_dvd_natCast.2 (Nat.minFac_dvd g)).trans (Int.gcd_dvd_left _ _)

lemma factorial_card_le_prod (S : Finset ℕ) (hS : ∀ p ∈ S, 0 < p) :
    S.card.factorial ≤ ∏ p ∈ S, p := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [Finset.card_insert_of_notMem ha, Finset.prod_insert ha, Nat.factorial_succ]
    have hpos : ∀ p ∈ s, 0 < p := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have hsub : s ⊆ Finset.Ioo 0 a := fun p hp => Finset.mem_Ioo.2 ⟨hpos p hp, hlt p hp⟩
    have hcard : s.card + 1 ≤ a := by
      have := Finset.card_le_card hsub
      simp at this
      have : 0 < a := hS a (Finset.mem_insert_self a s)
      omega
    exact Nat.mul_le_mul hcard (ih hpos)

/-- `ω(N) log ω(N) ≤ 3 log N`. -/
lemma card_primeFactors_log_le (N : ℕ) (hN : N ≠ 0) :
    (N.primeFactors.card : ℝ) * Real.log N.primeFactors.card ≤ 3 * Real.log N := by
  set r := N.primeFactors.card with hr
  have hprod : ∏ p ∈ N.primeFactors, p ≤ N :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hN) (Nat.prod_primeFactors_dvd N)
  have hfact : r.factorial ≤ N :=
    (factorial_card_le_prod _ fun p hp => (Nat.prime_of_mem_primeFactors hp).pos).trans hprod
  have h2 : 2 ^ r ≤ N := by
    refine le_trans ?_ hprod
    exact Finset.pow_card_le_prod _ _ _ fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hN
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  rcases Nat.eq_zero_or_pos r with h0 | hrpos
  · rw [h0]; simp; exact hlogN
  have hrR : (0 : ℝ) < r := by exact_mod_cast hrpos
  -- r ≤ 2 log N
  have hr2 : (r : ℝ) ≤ 2 * Real.log N := by
    have : (r : ℝ) * Real.log 2 ≤ Real.log N := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) (by exact_mod_cast h2)
    have := Real.log_two_gt_d9
    nlinarith
  -- r^r ≤ e^r r!
  have hexp : (r : ℝ) ^ r ≤ Real.exp r * r.factorial := by
    have := Real.pow_div_factorial_le_exp (r : ℝ) hrR.le r
    have hf : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
    rwa [div_le_iff₀ hf] at this
  have hlog : (r : ℝ) * Real.log r ≤ r + Real.log N := by
    rw [← Real.log_pow]
    have hf : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
    calc Real.log ((r : ℝ) ^ r) ≤ Real.log (Real.exp r * r.factorial) :=
          Real.log_le_log (by positivity) hexp
      _ = r + Real.log r.factorial := by
          rw [Real.log_mul (Real.exp_pos _).ne' hf.ne', Real.log_exp]
      _ ≤ r + Real.log N := by
          gcongr
  linarith

lemma exists_good_shift (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → 2 ≤ S.card →
      ∀ (x : ℤ) (m : ℕ), (∀ k < m, ∃ p ∈ S, (p : ℤ) ∣ x + k) →
        (m : ℝ) ≤ C * ((S.card : ℝ) * Real.log S.card) ^ 2)
    (P : ℤ) (hP : P ≠ 0) (c : ℤ) (T : ℝ) (hT : Real.log P.natAbs ≤ T) :
    ∃ k : ℕ, k ≤ P.natAbs ∧ (k : ℝ) ≤ C * (3 * T) ^ 2 + 2 ∧ c + k ≠ 0 ∧
      Int.gcd (c + k) P = 1 := by
  set r := P.natAbs.primeFactors.card with hr
  have hPn : P.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hP
  have hrl := card_primeFactors_log_le P.natAbs hPn
  have hrl0 : 0 ≤ (r : ℝ) * Real.log r :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have hsq : ((r : ℝ) * Real.log r) ^ 2 ≤ (3 * T) ^ 2 := by
    rw [← hr] at hrl
    exact pow_le_pow_left₀ hrl0 (by linarith) 2
  have hwin : (winLen C r : ℝ) ≤ C * (3 * T) ^ 2 + 2 := by
    unfold winLen
    push_cast
    have := Nat.floor_le (a := C * ((r : ℝ) * Real.log r) ^ 2) (by positivity)
    nlinarith
  rcases Nat.lt_or_ge P.natAbs 2 with h1 | h2
  · have hP1 : P.natAbs = 1 := by omega
    have hg : ∀ z : ℤ, Int.gcd z P = 1 := fun z => by
      unfold Int.gcd; rw [hP1]; exact Nat.gcd_one_right _
    have hw2 : (2 : ℝ) ≤ winLen C r := by
      unfold winLen; push_cast; have := Nat.cast_nonneg (α := ℝ) ⌊C * ((r : ℝ) * Real.log r) ^ 2⌋₊
      linarith
    by_cases hc : c = 0
    · refine ⟨1, by omega, ?_, by simp [hc], hg _⟩
      push_cast; linarith
    · refine ⟨0, by omega, ?_, by simpa using hc, hg _⟩
      push_cast; linarith
  · classical
    have hex : ∃ k : ℕ, Int.gcd (c + k) P = 1 := by
      obtain ⟨k, -, hk⟩ := exists_shift_le_abs P h2 c
      exact ⟨k, hk⟩
    obtain ⟨k1, hk1, hg1⟩ := exists_shift_le_abs P h2 c
    obtain ⟨k2, hk2, hg2⟩ := exists_shift_lt_win C hC P hP c
    refine ⟨Nat.find hex, (Nat.find_min' hex hg1).trans hk1, ?_, ?_, Nat.find_spec hex⟩
    · have : Nat.find hex ≤ winLen C r := (Nat.find_min' hex hg2).trans hk2.le
      exact (Nat.cast_le.2 this).trans hwin
    · intro h0
      have := Nat.find_spec hex
      rw [h0] at this
      simp at this
      omega

lemma construct (B T : ℝ) (x : ℕ) (hx : 1 ≤ x)
    (hk : ∀ P : ℤ, P ≠ 0 → Real.log P.natAbs ≤ T → ∀ c : ℤ, ∃ k : ℕ, k ≤ P.natAbs ∧
      (k : ℝ) ≤ B ∧ c + k ≠ 0 ∧ Int.gcd (c + k) P = 1) :
    ∀ (n : ℕ) (a : Fin n → ℤ), (∀ i, (a i).natAbs ≤ x) →
      ((2 : ℝ) ^ n - 1) * Real.log (2 * x) ≤ T →
      ∃ h : Fin n → ℕ, PairwiseCoprimeVec (a + fun i => (h i : ℤ)) ∧
        (∏ i, (a i + h i)) ≠ 0 ∧ (∏ i, (a i + h i)).natAbs ≤ (2 * x) ^ (2 ^ n - 1) ∧
        ∀ i, (h i : ℝ) ≤ B := by
  intro n
  induction n with
  | zero =>
    intro a _ _
    refine ⟨fun i => i.elim0, fun i => i.elim0, by simp, by simp, fun i => i.elim0⟩
  | succ n ih =>
    intro a ha hT
    have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
    have hL : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
    have hpow : (2 : ℝ) ^ n ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hTn : ((2 : ℝ) ^ n - 1) * Real.log (2 * x) ≤ T :=
      le_trans (mul_le_mul_of_nonneg_right (by linarith) hL) hT
    obtain ⟨h', hcop, hne, hbd, hB⟩ := ih (fun i => a i.castSucc) (fun i => ha _) hTn
    set Q : ℤ := ∏ i : Fin n, (a i.castSucc + h' i) with hQ
    have h2n : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hQlog : Real.log Q.natAbs ≤ T := by
      have hQ0 : (0 : ℝ) < Q.natAbs := by
        have := Int.natAbs_pos.2 hne
        exact_mod_cast this
      refine le_trans ?_ hTn
      calc Real.log Q.natAbs ≤ Real.log (((2 * x : ℕ) : ℝ) ^ (2 ^ n - 1)) :=
            Real.log_le_log hQ0 (by exact_mod_cast hbd)
        _ = ((2 : ℝ) ^ n - 1) * Real.log (2 * x) := by
            rw [Real.log_pow]
            push_cast [Nat.cast_sub h2n]
            ring
    obtain ⟨k, hkQ, hkB, hkne, hkg⟩ := hk Q hne hQlog (a (Fin.last n))
    have key : ∀ j : Fin n, Int.gcd (a (Fin.last n) + k) (a j.castSucc + h' j) = 1 := by
      intro j
      exact Int.isCoprime_iff_gcd_eq_one.1
        ((Int.isCoprime_iff_gcd_eq_one.2 hkg).of_isCoprime_of_dvd_right
          (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)))
    have hprod : ∏ i : Fin (n + 1), (a i + ((Fin.snoc (α := fun _ => ℕ) h' k i : ℕ) : ℤ)) =
        Q * (a (Fin.last n) + k) := by
      rw [Fin.prod_univ_castSucc]
      simp [Q]
    refine ⟨Fin.snoc (α := fun _ => ℕ) h' k, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      simp only [Pi.add_apply]
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd rfl hij
        | cast j => simpa using key j
      | cast i =>
        induction j using Fin.lastCases with
        | last => rw [Int.gcd_comm]; simpa using key i
        | cast j =>
          have := hcop i j (fun h => hij (by rw [h]))
          simpa using this
    · rw [hprod]
      exact mul_ne_zero hne hkne
    · rw [hprod, Int.natAbs_mul]
      set Y := (2 * x) ^ (2 ^ n - 1) with hY
      have hY1 : 1 ≤ Y := Nat.one_le_pow _ _ (by omega)
      have hlast : (a (Fin.last n) + k).natAbs ≤ x + Y := by
        have := ha (Fin.last n)
        omega
      have hexp : (2 * x) ^ (2 ^ (n + 1) - 1) = (2 * x) * Y * Y := by
        rw [hY, mul_assoc, ← pow_two, ← pow_mul, ← pow_succ']
        congr 1
        rw [pow_succ]
        omega
      rw [hexp]
      calc Q.natAbs * (a (Fin.last n) + k).natAbs ≤ Y * (x + Y) :=
            Nat.mul_le_mul hbd hlast
        _ ≤ Y * (2 * x * Y) := by
            apply Nat.mul_le_mul_left
            have h1 : x ≤ x * Y := Nat.le_mul_of_pos_right x hY1
            have h2 : Y ≤ x * Y := Nat.le_mul_of_pos_left Y hx
            linarith
        _ = 2 * x * Y * Y := by ring
    · intro i
      induction i using Fin.lastCases with
      | last => simpa using hkB
      | cast i => simpa using hB i

end Thm2

open Thm2

/-- **Theorem 2** (existence form). -/
theorem theorem2 (n : ℕ) :
    ∃ C : ℝ, ∀ a : Fin n → ℤ, 2 ≤ height a →
      ∃ h : Fin n → ℤ, PairwiseCoprimeVec (a + h) ∧
        (height h : ℝ) ≤ C * Real.log (height a) ^ 2 := by
  obtain ⟨C0, hC0⟩ := iwaniecBound
  set C := max C0 0 with hCdef
  have hC0' : 0 ≤ C := le_max_right _ _
  have hC : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → 2 ≤ S.card →
      ∀ (x : ℤ) (m : ℕ), (∀ k < m, ∃ p ∈ S, (p : ℤ) ∣ x + k) →
        (m : ℝ) ≤ C * ((S.card : ℝ) * Real.log S.card) ^ 2 := by
    intro S hS hc x m hm
    refine (hC0 S hS hc x m hm).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
  refine ⟨36 * C * ((2 : ℝ) ^ n) ^ 2 + 5, ?_⟩
  intro a ha
  set x := height a with hxdef
  set T : ℝ := ((2 : ℝ) ^ n - 1) * Real.log (2 * x) with hT
  set B : ℝ := C * (3 * T) ^ 2 + 2 with hB
  have hk : ∀ P : ℤ, P ≠ 0 → Real.log P.natAbs ≤ T → ∀ c : ℤ, ∃ k : ℕ, k ≤ P.natAbs ∧
      (k : ℝ) ≤ B ∧ c + k ≠ 0 ∧ Int.gcd (c + k) P = 1 :=
    fun P hP hPT c => exists_good_shift C hC0' hC P hP c T hPT
  have hax : ∀ i, (a i).natAbs ≤ x := fun i =>
    Finset.le_sup (f := fun i => (a i).natAbs) (Finset.mem_univ i)
  obtain ⟨h, hcop, -, -, hhB⟩ := construct B T x (by omega) hk n a hax le_rfl
  refine ⟨fun i => (h i : ℤ), hcop, ?_⟩
  have hB0 : 0 ≤ B := by positivity
  have hhgt : (height (fun i => (h i : ℤ)) : ℝ) ≤ B := by
    have : height (fun i => (h i : ℤ)) ≤ ⌊B⌋₊ := by
      apply Finset.sup_le
      intro i _
      simp only [Int.natAbs_natCast]
      exact Nat.le_floor (hhB i)
    exact (Nat.cast_le.2 this).trans (Nat.floor_le hB0)
  refine hhgt.trans ?_
  -- estimate B
  have hx2 : (2 : ℝ) ≤ x := by exact_mod_cast ha
  set l := Real.log x with hl
  have hl2 : Real.log 2 ≤ l := Real.log_le_log (by norm_num) hx2
  have hlog2 := Real.log_two_gt_d9
  have hL : Real.log (2 * x) ≤ 2 * l := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    linarith
  have hL0 : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hT0 : 0 ≤ T := mul_nonneg (by linarith) hL0
  have hTle : T ≤ 2 ^ n * (2 * l) :=
    mul_le_mul (by linarith) hL hL0 (by positivity)
  have hT2 : T ^ 2 ≤ (2 ^ n * (2 * l)) ^ 2 := pow_le_pow_left₀ hT0 hTle 2
  have hl2' : (2 : ℝ) / 5 ≤ l ^ 2 := by nlinarith
  have : C * (3 * T) ^ 2 ≤ 36 * C * ((2 : ℝ) ^ n) ^ 2 * l ^ 2 := by
    have := mul_le_mul_of_nonneg_left hT2 hC0'
    nlinarith
  rw [hB]
  nlinarith

/-- **Theorem 2**: `L(a) ≪ log² 𝔥(a)`. -/
theorem theorem2_L (n : ℕ) :
    ∃ C : ℝ, ∀ a : Fin n → ℤ, 2 ≤ height a → (L a : ℝ) ≤ C * Real.log (height a) ^ 2 := by
  obtain ⟨C, hC⟩ := theorem2 n
  refine ⟨C, fun a ha => ?_⟩
  obtain ⟨h, hcop, hb⟩ := hC a ha
  have : L a ≤ height h := Nat.sInf_le ⟨h, rfl, hcop⟩
  exact (Nat.cast_le.2 this).trans hb

end ShiftedGcd
