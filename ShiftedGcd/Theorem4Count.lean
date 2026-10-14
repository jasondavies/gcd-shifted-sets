import ShiftedGcd.Defs

/-!
# Theorem 4, auxiliary counting lemmas

For a primitive vector `a` (`gcd(a) = 1`) we count the vectors `x` in the box `[1, h]ⁿ` with
`d ∣ a · x`:

* `Ucount_mul_le`, `le_Ucount_mul`: `(h - d)ⁿ ≤ d · U_d ≤ (h + d)ⁿ` (the second for `d ≤ h`);
* `Ucount_le_squarefree`: `U_d ≤ (h d^{-1/n} + 1) h^{n-1}` for squarefree `d`;
* `Zcount_le`: the number of `x` with `a · x = 0` is at most `h^{n-1}` (for `a ≠ 0`).
-/

open Finset

namespace ShiftedGcd

variable {n : ℕ}

/-- `U_d(a, h)`: the number of `x ∈ [1,h]ⁿ` with `d ∣ a · x`. -/
def Ucount (a : Fin n → ℤ) (h d : ℕ) : ℕ := #{x ∈ boxVecs n h | (d : ℤ) ∣ dot a x}

/-- The number of `x ∈ [1,h]ⁿ` with `a · x = 0`. -/
def Zcount (a : Fin n → ℤ) (h : ℕ) : ℕ := #{x ∈ boxVecs n h | dot a x = 0}

/-- `U'_d(a, h)`: the number of `x ∈ [1,h]ⁿ` with `a · x ≠ 0` and `d ∣ a · x`. -/
def Upcount (a : Fin n → ℤ) (h d : ℕ) : ℕ := #{x ∈ boxVecs n h | dot a x ≠ 0 ∧ (d : ℤ) ∣ dot a x}

lemma mem_boxVecs {h : ℕ} {x : Fin n → ℤ} : x ∈ boxVecs n h ↔ ∀ i, 1 ≤ x i ∧ x i ≤ h := by
  simp [boxVecs, Fintype.mem_piFinset]

lemma card_boxVecs (n h : ℕ) : #(boxVecs n h) = h ^ n := by
  simp [boxVecs, Fintype.card_piFinset]

/-! ### One-dimensional counting -/

/-- A set of integers in `[1, h]` which are pairwise congruent modulo `c` has at most
`h / c + 1` elements. -/
lemma card_le_of_dvd_sub {S : Finset ℤ} {h c : ℕ} (hc : 0 < c) (hS : S ⊆ Icc 1 (h : ℤ))
    (hdiv : ∀ s ∈ S, ∀ t ∈ S, (c : ℤ) ∣ s - t) : #S ≤ h / c + 1 := by
  have hc' : (0 : ℤ) < c := by exact_mod_cast hc
  have : #S ≤ #(Icc (0 : ℤ) ((h / c : ℕ) : ℤ)) := by
    refine card_le_card_of_injOn (fun t => (t - 1) / c) ?_ ?_
    · intro t ht
      have := hS ht
      simp only [mem_Icc, coe_Icc, Set.mem_Icc] at this ⊢
      constructor
      · exact Int.ediv_nonneg (by omega) hc'.le
      · calc (t - 1) / (c : ℤ) ≤ (h : ℤ) / c := Int.ediv_le_ediv hc' (by omega)
          _ = ((h / c : ℕ) : ℤ) := by push_cast; rfl
    · intro s hs t ht hst
      simp only at hst
      obtain ⟨k, hk⟩ := hdiv s (by simpa using hs) t (by simpa using ht)
      have e : s - 1 = (t - 1) + (c : ℤ) * k := by linarith
      rw [e, Int.add_mul_ediv_left _ _ hc'.ne'] at hst
      have : k = 0 := by linarith
      subst this
      linarith
  rwa [Int.card_Icc, sub_zero, ← Nat.cast_one (R := ℤ), ← Nat.cast_add, Int.toNat_natCast] at this

/-- Number of `t ∈ [1, h]` in a residue class modulo `d`: upper bound. -/
lemma card_residue_le (d h : ℕ) [NeZero d] (ρ : ZMod d) :
    #{t ∈ Icc (1 : ℤ) h | ((t : ℤ) : ZMod d) = ρ} ≤ h / d + 1 := by
  apply card_le_of_dvd_sub (Nat.pos_of_ne_zero (NeZero.ne d)) (filter_subset _ _)
  intro s hs t ht
  simp only [mem_filter] at hs ht
  have := (ZMod.intCast_eq_intCast_iff_dvd_sub t s d).mp (by rw [hs.2, ht.2])
  exact this

/-- Number of `t ∈ [1, h]` in a residue class modulo `d`: lower bound. -/
lemma le_card_residue (d h : ℕ) [NeZero d] (ρ : ZMod d) :
    h / d ≤ #{t ∈ Icc (1 : ℤ) h | ((t : ℤ) : ZMod d) = ρ} := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  set t₀ : ℤ := ((ρ - 1).val : ℤ) + 1
  have hval : (ρ - 1).val < d := ZMod.val_lt _
  have hdq : d * (h / d) ≤ h := Nat.mul_div_le h d
  calc h / d = #(range (h / d)) := (card_range _).symm
    _ ≤ _ := by
      refine card_le_card_of_injOn (fun k : ℕ => t₀ + d * k) ?_ ?_
      · intro k hk
        simp only [coe_range, Set.mem_Iio] at hk
        simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq]
        have h0 : (0 : ℤ) ≤ (d : ℤ) * k := by positivity
        have h0' : (0 : ℤ) ≤ ((ρ - 1).val : ℤ) := by positivity
        refine ⟨⟨by simp only [t₀]; linarith, ?_⟩, ?_⟩
        · have : d * (k + 1) ≤ d * (h / d) := Nat.mul_le_mul_left _ hk
          have : (d : ℤ) * (k + 1) ≤ h := by exact_mod_cast this.trans hdq
          simp only [t₀]
          have : ((ρ - 1).val : ℤ) + 1 ≤ d := by exact_mod_cast hval
          nlinarith
        · simp [t₀]
      · intro k _ l _ hkl
        simp only at hkl
        have : (d : ℤ) * k = d * l := by linarith
        exact_mod_cast (mul_left_cancel₀ (by exact_mod_cast hd.ne') this)

/-! ### Counting modulo `d` -/

/-- Bézout for primitive vectors. -/
lemma exists_bezout {a : Fin n → ℤ} (ha : vgcd a = 1) : ∃ c : Fin n → ℤ, ∑ i, a i * c i = 1 := by
  obtain ⟨g, hg⟩ := Finset.gcd_eq_sum_mul (univ : Finset (Fin n)) a
  set G := univ.gcd a
  have hG : G.natAbs ∣ 1 := by
    rw [← ha]
    exact Finset.dvd_gcd fun i _ => Int.natAbs_dvd_natAbs.mpr (Finset.gcd_dvd (mem_univ i))
  have hG1 : G * G = 1 := by
    rw [← Int.natAbs_mul_self, Nat.dvd_one.mp hG]; rfl
  refine ⟨fun i => g i * G, ?_⟩
  simp_rw [← mul_assoc, ← sum_mul, ← hg, hG1]

/-- The linear form `r ↦ a · r` on `(ℤ/d)ⁿ`. -/
def linZ (d : ℕ) (a : Fin n → ℤ) (r : Fin n → ZMod d) : ZMod d := ∑ i, (a i : ZMod d) * r i

/-- For primitive `a`, the kernel of `r ↦ a · r` on `(ℤ/d)ⁿ` has `d^{n-1}` elements. -/
lemma card_ker_mul (d : ℕ) [NeZero d] {a : Fin n → ℤ} (ha : vgcd a = 1) :
    #{r : Fin n → ZMod d | linZ d a r = 0} * d = d ^ n := by
  classical
  obtain ⟨c, hc⟩ := exists_bezout ha
  set cc : Fin n → ZMod d := fun i => (c i : ZMod d)
  have hLc : linZ d a cc = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod d) hc
    push_cast at this
    simpa [linZ, cc] using this
  have hLsub : ∀ r (t : ZMod d), linZ d a (r - t • cc) = linZ d a r - t := by
    intro r t
    have : linZ d a (r - t • cc) = linZ d a r - t * linZ d a cc := by
      simp only [linZ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, sum_sub_distrib,
        mul_sum]
      congr 1
      exact sum_congr rfl fun i _ => by ring
    rw [this, hLc, mul_one]
  have hLadd : ∀ r (t : ZMod d), linZ d a (r + t • cc) = linZ d a r + t := by
    intro r t
    have := hLsub (r + t • cc) t
    rw [add_sub_cancel_right] at this
    linear_combination -this
  have hfib : ∀ t : ZMod d, #{r | linZ d a r = t} = #{r | linZ d a r = 0} := by
    intro t
    refine card_nbij' (fun r => r - t • cc) (fun r => r + t • cc) ?_ ?_ ?_ ?_
    · intro r hr
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hr ⊢
      rw [hLsub, hr, sub_self]
    · intro r hr
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hr ⊢
      rw [hLadd, hr, zero_add]
    · intro r _; exact sub_add_cancel r _
    · intro r _; exact add_sub_cancel_right r _
  have := card_eq_sum_card_fiberwise (f := linZ d a) (s := univ) (t := univ)
    (fun _ _ => mem_coe.mpr (mem_univ _))
  rw [card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin] at this
  rw [this, sum_congr rfl fun t _ => hfib t, sum_const, card_univ, ZMod.card, smul_eq_mul,
    mul_comm]

/-- `U_d` as a sum over residue classes. -/
lemma Ucount_eq_sum (a : Fin n → ℤ) (h d : ℕ) [NeZero d] :
    Ucount a h d = ∑ r ∈ {r : Fin n → ZMod d | linZ d a r = 0},
      ∏ i, #{t ∈ Icc (1 : ℤ) h | ((t : ℤ) : ZMod d) = r i} := by
  classical
  rw [Ucount, card_eq_sum_card_fiberwise (f := fun x i => (x i : ZMod d))
    (t := {r : Fin n → ZMod d | linZ d a r = 0})]
  · refine sum_congr rfl fun r hr => ?_
    rw [← Fintype.card_piFinset]
    congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and] at hr
    simp only [mem_filter, boxVecs, Fintype.mem_piFinset, funext_iff]
    constructor
    · rintro ⟨⟨hx, _⟩, hxr⟩ i
      exact ⟨hx i, hxr i⟩
    · intro hx
      refine ⟨⟨fun i => (hx i).1, ?_⟩, fun i => (hx i).2⟩
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← hr]
      simp [dot, linZ, (hx _).2]
  · intro x hx
    simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hx ⊢
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hx
    simpa [dot, linZ] using hx.2

/-- Upper bound `d · U_d ≤ (h + d)ⁿ`. -/
lemma Ucount_mul_le {a : Fin n → ℤ} (ha : vgcd a = 1) (h : ℕ) {d : ℕ} (hd : 0 < d) :
    Ucount a h d * d ≤ (h + d) ^ n := by
  have : NeZero d := ⟨hd.ne'⟩
  have h1 : Ucount a h d ≤ #{r : Fin n → ZMod d | linZ d a r = 0} * (h / d + 1) ^ n := by
    rw [Ucount_eq_sum, ← smul_eq_mul, ← sum_const]
    refine sum_le_sum fun r _ => ?_
    calc ∏ i, #{t ∈ Icc (1 : ℤ) h | ((t : ℤ) : ZMod d) = r i} ≤ ∏ _i : Fin n, (h / d + 1) :=
          prod_le_prod fun i _ => card_residue_le d h _
      _ = _ := by simp
  calc Ucount a h d * d ≤ #{r : Fin n → ZMod d | linZ d a r = 0} * (h / d + 1) ^ n * d :=
        Nat.mul_le_mul_right _ h1
    _ = (d * (h / d + 1)) ^ n := by rw [mul_right_comm, card_ker_mul d ha, mul_pow]
    _ ≤ (h + d) ^ n := by
        gcongr
        rw [mul_add, mul_one]
        exact Nat.add_le_add_right (Nat.mul_div_le h d) d

/-- Lower bound `(d ⌊h/d⌋)ⁿ ≤ d · U_d`. -/
lemma le_Ucount_mul {a : Fin n → ℤ} (ha : vgcd a = 1) (h : ℕ) {d : ℕ} (hd : 0 < d) :
    (d * (h / d)) ^ n ≤ Ucount a h d * d := by
  have : NeZero d := ⟨hd.ne'⟩
  have h1 : #{r : Fin n → ZMod d | linZ d a r = 0} * (h / d) ^ n ≤ Ucount a h d := by
    rw [Ucount_eq_sum, ← smul_eq_mul, ← sum_const]
    refine sum_le_sum fun r _ => ?_
    calc (h / d) ^ n = ∏ _i : Fin n, (h / d) := by simp
      _ ≤ _ := prod_le_prod fun i _ => le_card_residue d h _
  calc (d * (h / d)) ^ n = #{r : Fin n → ZMod d | linZ d a r = 0} * (h / d) ^ n * d := by
        rw [mul_right_comm, card_ker_mul d ha, mul_pow]
    _ ≤ _ := Nat.mul_le_mul_right _ h1

/-! ### Fibres over all but one coordinate -/

lemma update_eq_imp {x y : Fin n → ℤ} {i : Fin n}
    (hxy : Function.update x i 0 = Function.update y i 0) (j : Fin n) (hj : j ≠ i) :
    x j = y j := by
  have := congrFun hxy j
  simpa [Function.update_of_ne hj] using this

lemma dot_sub_of_update_eq (a : Fin n → ℤ) {x y : Fin n → ℤ} {i : Fin n}
    (hxy : Function.update x i 0 = Function.update y i 0) :
    dot a x - dot a y = a i * (x i - y i) := by
  rw [dot, dot, ← sum_sub_distrib, sum_eq_single i]
  · ring
  · intro j _ hj; rw [update_eq_imp hxy j hj]; ring
  · simp

lemma eq_of_update_eq {x y : Fin n → ℤ} {i : Fin n}
    (hxy : Function.update x i 0 = Function.update y i 0) (hi : x i = y i) : x = y := by
  funext j
  by_cases hj : j = i
  · subst hj; exact hi
  · exact update_eq_imp hxy j hj

/-- Fibring the box over all coordinates but the `i`-th. -/
lemma card_filter_le_fiber {h : ℕ} (i : Fin n) (P : (Fin n → ℤ) → Prop) [DecidablePred P]
    (k : ℕ) (hk : ∀ z, #{x ∈ boxVecs n h | P x ∧ Function.update x i 0 = z} ≤ k) :
    #{x ∈ boxVecs n h | P x} ≤ k * h ^ (n - 1) := by
  classical
  set t : Finset (Fin n → ℤ) := Fintype.piFinset fun j => if j = i then {0} else Icc 1 (h : ℤ)
  have ht : #t = h ^ (n - 1) := by
    rw [Fintype.card_piFinset]
    have : ∀ j, #(if j = i then ({0} : Finset ℤ) else Icc 1 (h : ℤ)) = if j = i then 1 else h := by
      intro j; split_ifs <;> simp
    simp_rw [this]
    rw [prod_ite, prod_const_one, one_mul, prod_const, filter_ne' univ i,
      card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  rw [← ht]
  refine card_le_mul_card_image_of_maps_to (f := fun x => Function.update x i 0) ?_ k ?_
  · intro x hx
    rw [mem_filter, mem_boxVecs] at hx
    rw [Fintype.mem_piFinset]
    intro j
    by_cases hj : j = i
    · subst hj; simp
    · simp only [hj, ite_false, Function.update_of_ne hj, mem_Icc]
      exact_mod_cast hx.1 j
  · intro z _
    rw [filter_filter]
    exact hk z

/-- If `gcd(c, aᵢ) = 1` then `#{x ∈ [1,h]ⁿ : c ∣ a · x} ≤ (h / c + 1) h^{n-1}`. -/
lemma card_dvd_le_of_coprime {a : Fin n → ℤ} {h c : ℕ} (hc : 0 < c) (i : Fin n)
    (hcop : Int.gcd c (a i) = 1) :
    #{x ∈ boxVecs n h | (c : ℤ) ∣ dot a x} ≤ (h / c + 1) * h ^ (n - 1) := by
  classical
  refine card_filter_le_fiber i _ _ fun z => ?_
  set F := {x ∈ boxVecs n h | (c : ℤ) ∣ dot a x ∧ Function.update x i 0 = z}
  have hinj : Set.InjOn (fun x : Fin n → ℤ => x i) F := by
    intro x hx y hy hxy
    simp only [F, coe_filter, Set.mem_ofPred_eq] at hx hy
    exact eq_of_update_eq (hx.2.2.trans hy.2.2.symm) hxy
  rw [← card_image_of_injOn hinj]
  apply card_le_of_dvd_sub hc
  · intro t ht
    obtain ⟨x, hx, rfl⟩ := mem_image.mp ht
    simp only [F, mem_filter, mem_boxVecs] at hx
    simp only [mem_Icc]
    exact hx.1 i
  · intro s hs t ht
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hs
    obtain ⟨y, hy, rfl⟩ := mem_image.mp ht
    simp only [F, mem_filter] at hx hy
    have h1 : (c : ℤ) ∣ a i * (x i - y i) := by
      rw [← dot_sub_of_update_eq a (hx.2.2.trans hy.2.2.symm)]
      exact dvd_sub hx.2.1 hy.2.1
    exact Int.dvd_of_dvd_mul_right_of_gcd_one h1 hcop

/-- For `a ≠ 0`: `#{x ∈ [1,h]ⁿ : a · x = 0} ≤ h^{n-1}`. -/
lemma Zcount_le {a : Fin n → ℤ} (ha : a ≠ 0) (h : ℕ) : Zcount a h ≤ h ^ (n - 1) := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  rw [Zcount, ← one_mul (h ^ (n - 1))]
  refine card_filter_le_fiber i _ _ fun z => ?_
  refine card_le_one.mpr fun x hx y hy => ?_
  simp only [mem_filter] at hx hy
  have hxy := hx.2.2.trans hy.2.2.symm
  have h1 := dot_sub_of_update_eq a hxy
  rw [hx.2.1, hy.2.1, sub_self, eq_comm, mul_eq_zero] at h1
  exact eq_of_update_eq hxy (sub_eq_zero.mp (h1.resolve_left hi))

/-! ### Squarefree moduli -/

/-- For squarefree `d` and primitive `a`, there are an index `i` and a divisor `c ∣ d` coprime
to `aᵢ` with `d ≤ cⁿ`. -/
lemma exists_coprime_divisor {a : Fin n → ℤ} (hn : 0 < n) (ha : vgcd a = 1) {d : ℕ}
    (hd : Squarefree d) : ∃ i, ∃ c : ℕ, c ∣ d ∧ Int.gcd c (a i) = 1 ∧ d ≤ c ^ n := by
  have hd0 : d ≠ 0 := by rintro rfl; exact not_squarefree_zero hd
  set cf : Fin n → ℕ := fun i => d / Nat.gcd d (a i).natAbs
  have hcf_dvd : ∀ i, cf i ∣ d := fun i => Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
  have hcf0 : ∀ i, cf i ≠ 0 := fun i => ne_zero_of_dvd_ne_zero hd0 (hcf_dvd i)
  have hcop : ∀ i, Nat.Coprime (cf i) (a i).natAbs := by
    intro i
    by_cases h0 : (a i).natAbs = 0
    · simp [cf, h0, Nat.div_self (Nat.pos_of_ne_zero hd0)]
    · exact Nat.coprime_div_gcd_of_squarefree hd h0
  have hprod0 : ∏ i, cf i ≠ 0 := prod_ne_zero_iff.mpr fun i _ => hcf0 i
  have hdvd : d ∣ ∏ i, cf i := by
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hd]
    rw [Nat.prod_primeFactors_dvd_iff hprod0]
    intro p hp
    rw [Nat.mem_primeFactors] at hp ⊢
    refine ⟨hp.1, ?_, hprod0⟩
    obtain ⟨j, hj⟩ : ∃ j, ¬ p ∣ (a j).natAbs := by
      by_contra hcon
      push Not at hcon
      have : p ∣ vgcd a := Finset.dvd_gcd fun j _ => hcon j
      rw [ha] at this
      exact hp.1.one_lt.ne' (Nat.dvd_one.mp this)
    have hpj : p ∣ cf j := by
      have : p ∣ cf j * Nat.gcd d (a j).natAbs := by
        rw [Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)]; exact hp.2.1
      exact (hp.1.dvd_mul.mp this).resolve_right
        fun h' => hj (h'.trans (Nat.gcd_dvd_right _ _))
    exact hpj.trans (dvd_prod_of_mem _ (mem_univ j))
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i, -, hi⟩ := exists_max_image univ cf univ_nonempty
  refine ⟨i, cf i, hcf_dvd i, ?_, ?_⟩
  · simpa [Int.gcd] using hcop i
  · calc d ≤ ∏ j, cf j := Nat.le_of_dvd (Nat.pos_of_ne_zero hprod0) hdvd
      _ ≤ cf i ^ #(univ : Finset (Fin n)) := prod_le_pow_card _ _ _ fun j _ => hi j (mem_univ j)
      _ = cf i ^ n := by rw [card_univ, Fintype.card_fin]

/-- (11): for squarefree `d`, `U_d ≤ (h d^{-1/n} + 1) h^{n-1}`. -/
lemma Ucount_le_squarefree {a : Fin n → ℤ} (hn : 0 < n) (ha : vgcd a = 1) (h : ℕ) {d : ℕ}
    (hd : Squarefree d) :
    (Ucount a h d : ℝ) ≤ ((h : ℝ) / (d : ℝ) ^ ((1 : ℝ) / n) + 1) * (h : ℝ) ^ (n - 1) := by
  obtain ⟨i, c, hcd, hcop, hdc⟩ := exists_coprime_divisor hn ha hd
  have hd0 : d ≠ 0 := by rintro rfl; exact not_squarefree_zero hd
  have hc0 : 0 < c := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hd0 hcd)
  have h1 : Ucount a h d ≤ (h / c + 1) * h ^ (n - 1) := by
    refine le_trans ?_ (card_dvd_le_of_coprime hc0 i hcop)
    refine card_le_card fun x hx => ?_
    simp only [mem_filter] at hx ⊢
    exact ⟨hx.1, (Int.natCast_dvd_natCast.mpr hcd).trans hx.2⟩
  have h2 : (d : ℝ) ^ ((1 : ℝ) / n) ≤ c := by
    have : (d : ℝ) ≤ (c : ℝ) ^ n := by exact_mod_cast hdc
    calc (d : ℝ) ^ ((1 : ℝ) / n) ≤ ((c : ℝ) ^ n) ^ ((1 : ℝ) / n) :=
          Real.rpow_le_rpow (by positivity) this (by positivity)
      _ = c := by rw [one_div, Real.pow_rpow_inv_natCast (by positivity) hn.ne']
  have hdpos : 0 < (d : ℝ) ^ ((1 : ℝ) / n) := by
    have : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
    positivity
  calc (Ucount a h d : ℝ) ≤ ((h / c : ℕ) + 1 : ℝ) * (h : ℝ) ^ (n - 1) := by exact_mod_cast h1
    _ ≤ _ := by
      gcongr
      calc ((h / c : ℕ) : ℝ) ≤ (h : ℝ) / c := Nat.cast_div_le
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hdpos h2

end ShiftedGcd
