import ShiftedGcd.Defs

/-!
# Theorem 3: vectors that need large shifts to become coprime

Unconditional. The construction uses the Chinese Remainder Theorem together with Chebyshev's
lower bound for `π(x)`.

The paper takes primes `p > H`, but the construction does not need this: any distinct
primes work.
-/

open Finset

namespace ShiftedGcd
namespace Thm3

/-! ### Auxiliary lemmas

Proof outline: for a parameter `H`, take `N = (2H+1)ⁿ` distinct primes `q_v ≤ X`, one for each
shift vector `v ∈ [-H, H]ⁿ`, where `X = 16 N (⌊log₂ N⌋ + 1)` (Chebyshev's bound gives
`π(X) ≥ N`). By CRT pick `c_k ≡ v_k + H (mod q_v)` and put `a_k = H - c_k`; then `q_v ∣ a + v`,
so every shift of height `≤ H` fails, while `𝔥(a) ≤ 4^{X+1}` since `∏ q_v ∣ X#`. -/

lemma pi_large_aux (N m : ℕ) (hN : 1 ≤ N) (hm : 1 ≤ m) (h1 : N < 2 ^ m) :
    N ≤ Nat.primeCounting (16 * N * m) := by
  have h2 : m < 2 ^ m := Nat.lt_two_pow_self
  set X := 16 * N * m with hXdef
  have hX : X + 1 ≤ 2 ^ (2 * m + 4) := by
    have : 2 ^ (2 * m + 4) = 16 * (2 ^ m * 2 ^ m) := by ring
    rw [this, hXdef]; nlinarith
  have hX16 : 16 ≤ X := by rw [hXdef]; nlinarith
  have key := Chebyshev.pi_ge X
  have hXr : (16 : ℝ) ≤ X := by exact_mod_cast hX16
  have hX1r : ((X : ℝ) + 1) ≤ (2 : ℝ) ^ (2 * m + 4) := by exact_mod_cast hX
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogX : Real.log X ≤ (2 * m + 4 : ℕ) * Real.log 2 := by
    rw [← Real.log_pow]; exact Real.log_le_log (by linarith) (by linarith)
  have hlogX1 : Real.log (X + 1) ≤ (2 * m + 4 : ℕ) * Real.log 2 := by
    rw [← Real.log_pow]; exact Real.log_le_log (by linarith) hX1r
  have hlogXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hXeq : (X : ℝ) = 16 * N * m := by rw [hXdef]; push_cast; ring
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hint : ((N : ℝ) + 1) * (2 * m + 4) ≤ 16 * N * m := by nlinarith
  have : (N : ℝ) ≤ (X * Real.log 2 - Real.log (X + 1)) / Real.log X := by
    rw [le_div_iff₀ hlogXpos]
    push_cast at hlogX hlogX1
    have e1 : (N : ℝ) * Real.log X ≤ N * ((2 * m + 4) * Real.log 2) :=
      mul_le_mul_of_nonneg_left hlogX (by linarith)
    have e2 : ((N : ℝ) + 1) * (2 * m + 4) * Real.log 2 ≤ 16 * N * m * Real.log 2 :=
      mul_le_mul_of_nonneg_right hint hl2.le
    rw [hXeq] at e1 hlogX1 ⊢
    nlinarith
  exact_mod_cast this.trans key

lemma pi_large (N : ℕ) (hN : 1 ≤ N) : N ≤ Nat.primeCounting (16 * N * (Nat.log 2 N + 1)) :=
  pi_large_aux N _ hN (by omega) (Nat.lt_pow_succ_log_self (by norm_num) N)

lemma exists_primes (N X : ℕ) (h : N ≤ Nat.primeCounting X) :
    ∃ s : Fin N → ℕ, Function.Injective s ∧ (∀ j, (s j).Prime) ∧ ∏ j, s j ≤ 4 ^ X := by
  have hinj : Function.Injective (Nat.nth Nat.Prime) := Nat.nth_injective Nat.infinite_setOfPred_prime
  refine ⟨fun j => Nat.nth Nat.Prime j, fun i j hij => Fin.ext (hinj hij),
    fun j => Nat.prime_nth_prime j, ?_⟩
  rw [Fin.prod_univ_eq_prod_range (fun j => Nat.nth Nat.Prime j) N,
    show ∏ i ∈ range N, Nat.nth Nat.Prime i = ∏ p ∈ (range N).image (Nat.nth Nat.Prime), p from
      (Finset.prod_image (f := fun p => p) (fun i _ j _ hij => hinj hij)).symm]
  refine le_trans (Nat.le_of_dvd (primorial_pos X) ?_) (primorial_le_four_pow X)
  rw [primorial_eq_prod_primesLE]
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  simp only [Finset.mem_image, Finset.mem_range] at hp
  obtain ⟨j, hj, rfl⟩ := hp
  rw [Nat.mem_primesLE]
  refine ⟨?_, Nat.prime_nth_prime j⟩
  have : j < Nat.count Nat.Prime (X + 1) := by
    have : Nat.primeCounting X = Nat.count Nat.Prime (X + 1) := rfl
    omega
  have := Nat.nth_lt_of_lt_count this
  omega

lemma exists_shift_one {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℤ) :
    ∃ h : Fin n → ℤ, height h ≤ height a + 1 ∧ vgcd (a + h) = 1 := by
  let i0 : Fin n := ⟨0, hn⟩
  refine ⟨fun i => -a i + if i = i0 then 1 else 0, ?_, ?_⟩
  · refine Finset.sup_le fun i _ => ?_
    have := natAbs_le_height a i
    simp only
    split_ifs <;> omega
  · have hd : vgcd (a + fun i => -a i + if i = i0 then 1 else 0) ∣ 1 := by
      have := Finset.gcd_dvd (f := fun i => ((a + fun i => -a i + if i = i0 then 1 else 0) i).natAbs)
        (Finset.mem_univ i0)
      simpa [vgcd] using this
    exact Nat.dvd_one.mp hd

lemma height_ge {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℤ) (H : ℕ)
    (hA : ∀ h : Fin n → ℤ, height h ≤ H → vgcd (a + h) ≠ 1) : H ≤ height a := by
  by_contra hlt
  obtain ⟨h, hh, hg⟩ := exists_shift_one hn a
  exact hA h (by omega) hg

lemma construct {n : ℕ} (H N X : ℕ) (hNX : N ≤ Nat.primeCounting X)
    (hN : N = (2 * H + 1) ^ n) (hHX : H ≤ X) :
    ∃ a : Fin n → ℤ, (∀ h : Fin n → ℤ, height h ≤ H → vgcd (a + h) ≠ 1) ∧
      height a ≤ 4 ^ (X + 1) := by
  obtain ⟨s, hsinj, hsp, hsprod⟩ := exists_primes N X hNX
  have hcard : Fintype.card (Fin n → Fin (2 * H + 1)) = N := by simp [hN]
  let e : (Fin n → Fin (2 * H + 1)) ≃ Fin N := (Fintype.equivFin _).trans (finCongr hcard)
  let q : (Fin n → Fin (2 * H + 1)) → ℕ := fun v => s (e v)
  have hqp : ∀ v, (q v).Prime := fun v => hsp _
  have hqprod : ∏ v, q v ≤ 4 ^ X := by
    rw [Equiv.prod_comp e s]; exact hsprod
  have hcop : Set.Pairwise (↑(Finset.univ : Finset (Fin n → Fin (2 * H + 1))))
      (Function.onFun Nat.Coprime q) := by
    intro v _ w _ hvw
    exact (Nat.coprime_primes (hqp v) (hqp w)).2 fun hq => hvw (e.injective (hsinj hq))
  have hne : ∀ v ∈ (Finset.univ : Finset (Fin n → Fin (2 * H + 1))), q v ≠ 0 :=
    fun v _ => (hqp v).ne_zero
  let crt : Fin n → ℕ := fun k =>
    (Nat.chineseRemainderOfFinset (fun v : Fin n → Fin (2 * H + 1) => ((v k : ℕ))) q
      Finset.univ hne hcop).1
  have hcrt : ∀ k v, crt k ≡ (v k : ℕ) [MOD q v] := fun k v =>
    (Nat.chineseRemainderOfFinset (fun v : Fin n → Fin (2 * H + 1) => ((v k : ℕ))) q
      Finset.univ hne hcop).2 v (Finset.mem_univ v)
  have hcrtlt : ∀ k, crt k < 4 ^ X := fun k =>
    lt_of_lt_of_le (Nat.chineseRemainderOfFinset_lt_prod _ _ hne hcop) hqprod
  refine ⟨fun k => (H : ℤ) - crt k, ?_, ?_⟩
  · intro h hh hg
    have hb : ∀ k, (h k).natAbs ≤ H := fun k => (natAbs_le_height h k).trans hh
    let v : Fin n → Fin (2 * H + 1) := fun k => ⟨(h k + H).toNat, by have := hb k; omega⟩
    have hdvd : q v ∣ vgcd ((fun k => (H : ℤ) - crt k) + h) := by
      refine Finset.dvd_gcd fun k _ => ?_
      rw [← Int.ofNat_dvd_left]
      have h1 := (Nat.modEq_iff_dvd).1 (hcrt k v)
      have h2 : (((v k : ℕ) : ℤ)) = h k + H := by
        have := hb k
        simp only [v]
        omega
      have h3 : ((fun k => (H : ℤ) - crt k) + h) k = ((v k : ℕ) : ℤ) - crt k := by
        simp only [Pi.add_apply]; rw [h2]; ring
      rw [h3]; exact h1
    rw [hg] at hdvd
    exact (hqp v).one_lt.ne' (Nat.dvd_one.mp hdvd)
  · refine Finset.sup_le fun k _ => ?_
    have h1 := hcrtlt k
    have h2 : H < 4 ^ X := lt_of_lt_of_le (Nat.lt_pow_self (by norm_num))
      (Nat.pow_le_pow_right (by norm_num) hHX)
    have h3 : 4 ^ (X + 1) = 4 * 4 ^ X := by ring
    show ((H : ℤ) - crt k).natAbs ≤ _
    omega


lemma real_aux (N ℓ x : ℕ) (hℓ : 1 ≤ ℓ) (hN : 2 ^ ℓ ≤ N) (hx : 27 ≤ x)
    (hx2 : x ≤ 4 ^ (16 * N * (ℓ + 1) + 1)) :
    0 ≤ Real.log x / Real.log (Real.log x) ∧
      Real.log x / Real.log (Real.log x) ≤ 100 * N := by
  have hxr : (27 : ℝ) ≤ x := by exact_mod_cast hx
  have hx2r : (x : ℝ) ≤ (4 : ℝ) ^ (16 * N * (ℓ + 1) + 1) := by exact_mod_cast hx2
  have hl3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9; norm_num at this; linarith
  have hL3 : 3 < Real.log x := by
    have : Real.log 27 ≤ Real.log x := Real.log_le_log (by norm_num) hxr
    have h27 : Real.log 27 = 3 * Real.log 3 := by
      rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]; norm_num
    linarith
  have hlL : 1 < Real.log (Real.log x) := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9; norm_num at this; linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLup : Real.log x ≤ (16 * N * (ℓ + 1) + 1 : ℕ) * (2 * Real.log 2) := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [← h4, ← Real.log_pow]
    exact Real.log_le_log (by linarith) hx2r
  push_cast at hLup
  have hNr : ((2 : ℝ) ^ ℓ) ≤ N := by exact_mod_cast hN
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hN1 : (1 : ℝ) ≤ N := le_trans (one_le_pow₀ (by norm_num)) hNr
  refine ⟨div_nonneg (by linarith) (by linarith), ?_⟩
  rw [div_le_iff₀ (by linarith)]
  rcases le_or_gt (Real.log x) N with hc | hc
  · nlinarith
  · have hlogN : (ℓ : ℝ) * Real.log 2 ≤ Real.log (Real.log x) := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) (by linarith)
    have e1 : (16 * (N : ℝ) * (ℓ + 1) + 1) ≤ 33 * N * ℓ := by nlinarith
    have e2 : (16 * (N : ℝ) * (ℓ + 1) + 1) * (2 * Real.log 2) ≤ 33 * N * ℓ * (2 * Real.log 2) :=
      mul_le_mul_of_nonneg_right e1 (by linarith)
    have e3 : (N : ℝ) * (ℓ * Real.log 2) ≤ N * Real.log (Real.log x) :=
      mul_le_mul_of_nonneg_left hlogN (by linarith)
    nlinarith

lemma rpow_step {n : ℕ} (hn : 1 ≤ n) {C z y : ℝ} (hC : 0 < C) (hz : 0 ≤ z) (hy : 0 ≤ y)
    (h : z ≤ C * y ^ n) : 1 / C ^ ((1 : ℝ) / n) * z ^ ((1 : ℝ) / n) ≤ y := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hCp : 0 < C ^ ((1 : ℝ) / n) := Real.rpow_pos_of_pos hC _
  have h1 : z ^ ((1 : ℝ) / n) ≤ (C * y ^ n) ^ ((1 : ℝ) / n) :=
    Real.rpow_le_rpow hz h (by positivity)
  rw [Real.mul_rpow hC.le (by positivity), one_div (n : ℝ),
    Real.pow_rpow_inv_natCast hy (by omega), ← one_div] at h1
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hCp]
  linarith

end Thm3

open Thm3

/-- **Theorem 3**. There are vectors `a` of arbitrarily large height such that every `h` with
`gcd(a + h) = 1` has `𝔥(h) ≫ (log 𝔥(a) / log log 𝔥(a))^{1/n}`. -/
theorem theorem3 {n : ℕ} (hn : 1 ≤ n) :
    ∃ c > 0, ∀ N : ℕ, ∃ a : Fin n → ℤ, N ≤ height a ∧
      ∀ h : Fin n → ℤ, vgcd (a + h) = 1 →
        c * (Real.log (height a) / Real.log (Real.log (height a))) ^ ((1 : ℝ) / n) ≤
          height h := by
  refine ⟨1 / (100 * 3 ^ n : ℝ) ^ ((1 : ℝ) / n), by positivity, ?_⟩
  intro N0
  set H := max N0 27 with hHdef
  set N := (2 * H + 1) ^ n with hNdef
  set ℓ := Nat.log 2 N with hℓdef
  set X := 16 * N * (ℓ + 1) with hXdef
  have h2H : 2 * H + 1 ≤ N := Nat.le_self_pow (by omega) _
  have hNX : N ≤ Nat.primeCounting X := pi_large N (by omega)
  have hHX : H ≤ X := by rw [hXdef]; nlinarith
  obtain ⟨a, hA, hht⟩ := construct H N X hNX rfl hHX
  have hHa := height_ge hn a H hA
  refine ⟨a, le_trans (le_max_left _ _) hHa, ?_⟩
  intro h hg
  have hHh : H < height h := by
    by_contra hcon
    exact hA h (by omega) hg
  have hℓ : 1 ≤ ℓ := Nat.log_pos (by norm_num) (by omega)
  have hpow : 2 ^ ℓ ≤ N := Nat.pow_log_le_self 2 (by omega)
  obtain ⟨hz0, hz⟩ := real_aux N ℓ (height a) hℓ hpow (by omega) hht
  have hN3 : N ≤ 3 ^ n * height h ^ n := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) n
  have hN3r : (N : ℝ) ≤ 3 ^ n * (height h : ℝ) ^ n := by exact_mod_cast hN3
  exact rpow_step hn (by positivity) hz0 (Nat.cast_nonneg _) (by nlinarith)

/-- **Theorem 3**: `ℓ(a) ≫ (log 𝔥(a) / log log 𝔥(a))^{1/n}` for infinitely many `a`. -/
theorem theorem3_ell {n : ℕ} (hn : 1 ≤ n) :
    ∃ c > 0, Set.Infinite {a : Fin n → ℤ |
      c * (Real.log (height a) / Real.log (Real.log (height a))) ^ ((1 : ℝ) / n) ≤ ell a} := by
  obtain ⟨c, hc, hmain⟩ := theorem3 hn
  refine ⟨c, hc, fun hfin => ?_⟩
  obtain ⟨B, hB⟩ : ∃ B, ∀ a ∈ {a : Fin n → ℤ |
      c * (Real.log (height a) / Real.log (Real.log (height a))) ^ ((1 : ℝ) / n) ≤ ell a},
      height a ≤ B :=
    ⟨hfin.toFinset.sup height, fun a ha => Finset.le_sup (hfin.mem_toFinset.2 ha)⟩
  obtain ⟨a, ha, hbound⟩ := hmain (B + 1)
  have hmem : c * (Real.log (height a) / Real.log (Real.log (height a))) ^ ((1 : ℝ) / n) ≤
      ell a := by
    obtain ⟨h0, -, hg0⟩ := exists_shift_one hn a
    have hne : {H | ∃ h : Fin n → ℤ, height h = H ∧ vgcd (a + h) = 1}.Nonempty :=
      ⟨_, h0, rfl, hg0⟩
    obtain ⟨h, hh, hg⟩ := Nat.sInf_mem hne
    unfold ell
    rw [← hh]
    exact hbound h hg
  have := hB a hmem
  omega

end ShiftedGcd
