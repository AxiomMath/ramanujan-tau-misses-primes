import Mathlib

/-! # S(X) = O(X^{9/10} log X) via reduction lemma + ABC bounds on E₂, E₄. -/

open Filter Asymptotics Classical

noncomputable def Nat.radical (n : ℕ) : ℕ :=
  if n = 0 then 0 else ∏ p ∈ n.primeFactors, p

structure RamanujanTau where
  τ : ℕ+ → ℤ
  hecke_mult : ∀ m n : ℕ+, Nat.Coprime (m : ℕ) (n : ℕ) → τ (m * n) = τ m * τ n
  hecke_rec : ∀ (p : ℕ+), (p : ℕ).Prime → ∀ (m : ℕ), 2 ≤ m →
    τ (p ^ m) = τ p * τ (p ^ (m - 1)) - (↑(p : ℕ) : ℤ) ^ 11 * τ (p ^ (m - 2))
  parity : ∀ n : ℕ+, ¬(2 ∣ τ n) ↔ (Odd (n : ℕ) ∧ IsSquare (n : ℕ))
  deligne_bound : ∀ (p : ℕ+), (p : ℕ).Prime →
    (|τ p| : ℝ) ≤ 2 * (p : ℝ) ^ ((11 : ℝ) / 2)
  non_unit : ∀ (n : ℕ+), 2 ≤ (n : ℕ) → τ n ≠ 1 ∧ τ n ≠ -1

variable (R : RamanujanTau)

noncomputable def S_set (X : ℝ) : Set ℕ :=
  {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧ ∃ n : ℕ+, (R.τ n).natAbs = ℓ}

noncomputable def S (X : ℝ) : ℕ := (S_set R X).ncard

noncomputable def E2_set (X : ℝ) : Set (ℕ+ × ℤ) :=
  {p : ℕ+ × ℤ | (p.1 : ℝ) > X ^ ((2 : ℝ) / 11) ∧
    1 ≤ |(↑p.1 : ℤ) ^ 11 - p.2 ^ 2| ∧
    (|(↑p.1 : ℤ) ^ 11 - p.2 ^ 2| : ℝ) ≤ X}

noncomputable def E2 (X : ℝ) : ℕ := (E2_set X).ncard

noncomputable def E4_set (X : ℝ) : Set (ℕ+ × ℤ) :=
  {p : ℕ+ × ℤ | (p.1 : ℝ) > X ^ ((1 : ℝ) / 11) ∧
    1 ≤ |p.2 ^ 2 - 5 * (↑p.1 : ℤ) ^ 22| ∧
    (|p.2 ^ 2 - 5 * (↑p.1 : ℤ) ^ 22| : ℝ) ≤ 4 * X}

noncomputable def E4 (X : ℝ) : ℕ := (E4_set X).ncard

def ABC : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ K : ℝ, 0 < K ∧
      ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
        Nat.Coprime a b → a + b = c →
          (c : ℝ) ≤ K * ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε)

def oddPrimesSigned : Set ℤ :=
  {z : ℤ | ∃ p : ℕ, Nat.Prime p ∧ p ≠ 2 ∧ (z = ↑p ∨ z = -↑p)}

def X2k (k : ℕ) : Set ℤ :=
  {z : ℤ | ∃ p : ℕ+, (p : ℕ).Prime ∧ z = R.τ (p ^ (2 * k))}

def Proposition5_4 : Prop :=
  (∃ c₄ : ℝ, 0 < c₄ ∧
    ∀ N : ℝ, c₄ < N →
      ∀ k : ℕ, 3 ≤ k → (k : ℝ) < Real.log N / (2 * Real.log 2) →
        ((oddPrimesSigned ∩ X2k R k ∩ {z : ℤ | (|z| : ℝ) ≤ N}).ncard : ℝ) < N ^ ((9 : ℝ) / 10)) ∧
  (∃ c₅ : ℝ, 0 < c₅ ∧
    ∀ N : ℝ, c₅ < N →
      ∀ k : ℕ, (k : ℝ) ≥ Real.log N / (2 * Real.log 2) →
        X2k R k ∩ {z : ℤ | (|z| : ℝ) ≤ N} = ∅)

/-! ## Basic properties of τ -/

lemma tau_one_eq_one (R : RamanujanTau) : R.τ 1 = 1 := by
  have h1 : R.τ (1 * 1) = R.τ 1 * R.τ 1 :=
    R.hecke_mult 1 1 ((Nat.coprime_one_left_iff 1).mpr trivial)
  simp only [mul_one] at h1
  have h2 : R.τ 1 * (R.τ 1 - 1) = 0 := by linarith
  rcases mul_eq_zero.mp h2 with h | h
  · exfalso
    exact ((R.parity 1).mpr ⟨⟨0, by norm_num⟩, ⟨1, by norm_num⟩⟩) (h ▸ dvd_zero 2)
  · linarith

lemma prime_tau_value_n_ge_two (R : RamanujanTau) (n : ℕ+) (ℓ : ℕ)
    (hprime : Nat.Prime ℓ) (_hne2 : ℓ ≠ 2) (habs : (R.τ n).natAbs = ℓ) :
    2 ≤ (n : ℕ) := by
  by_contra h
  push_neg at h
  have hn1 : (n : ℕ) = 1 := by
    have := n.pos
    omega
  have hn_eq : n = (1 : ℕ+) := PNat.eq hn1
  rw [show R.τ n = 1 from hn_eq ▸ tau_one_eq_one R] at habs
  simp at habs
  linarith [hprime.one_lt]
/-! ## Coprime factorization lemmas -/

lemma not_isPrimePow_coprime_factors {n : ℕ} (hn : 2 ≤ n) (hnpp : ¬IsPrimePow n) :
    ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ Nat.Coprime a b ∧ n = a * b := by
  have hn0 : n ≠ 0 := by omega
  set p := n.minFac with hp_def
  have hp : p.Prime := Nat.minFac_prime (by omega)
  set a := p ^ n.factorization p with ha_def
  set b := n / a with hb_def
  have hab : a * b = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hcop_pb : p.Coprime b := Nat.coprime_ordCompl hp hn0
  have hcop : a.Coprime b := by
    rwa [ha_def, Nat.coprime_pow_left_iff (Nat.Prime.factorization_pos_of_dvd hp hn0 (Nat.minFac_dvd n))]
  have ha2 : 2 ≤ a :=
    le_trans hp.two_le (le_trans (pow_one p).symm.le
      (Nat.pow_le_pow_right hp.pos (Nat.Prime.factorization_pos_of_dvd hp hn0 (Nat.minFac_dvd n))))
  have hb1 : b ≠ 1 := fun hb1 => by
    have : n = a := by rw [← hab, hb1, mul_one]
    rw [this, ha_def] at hnpp
    exact hnpp ((isPrimePow_pow_iff (Nat.Prime.factorization_pos_of_dvd hp hn0 (Nat.minFac_dvd n)).ne').mpr hp.isPrimePow)
  have hb2 : 2 ≤ b := by
    have hb0 : 0 < b := Nat.ordCompl_pos p hn0
    omega
  exact ⟨a, b, ha2, hb2, hcop, hab.symm⟩

lemma prime_tau_value_is_prime_power (R : RamanujanTau) (n : ℕ+) (ℓ : ℕ)
    (hprime : Nat.Prime ℓ) (hn2 : 2 ≤ (n : ℕ)) (habs : (R.τ n).natAbs = ℓ) :
    ∃ (p : ℕ) (m : ℕ), p.Prime ∧ 1 ≤ m ∧ (n : ℕ) = p ^ m := by
  by_cases hpp : IsPrimePow (n : ℕ)
  · rw [isPrimePow_iff_pow_succ] at hpp
    obtain ⟨p, k, hp, hpk⟩ := hpp
    exact ⟨p, k + 1, hp.nat_prime, by omega, hpk.symm⟩
  · exfalso
    obtain ⟨a, b, ha2, hb2, hcop, hn_eq⟩ := not_isPrimePow_coprime_factors hn2 hpp
    let a' : ℕ+ := ⟨a, by omega⟩
    let b' : ℕ+ := ⟨b, by omega⟩
    have hn_pnat : n = a' * b' := PNat.eq (by simp [a', b', hn_eq])
    rw [show R.τ n = R.τ a' * R.τ b' from hn_pnat ▸ R.hecke_mult a' b' hcop,
      Int.natAbs_mul] at habs
    have := hprime.eq_one_or_self_of_dvd (R.τ a').natAbs ⟨(R.τ b').natAbs, habs.symm⟩
    rcases this with h1 | h2
    · rcases Int.natAbs_eq (R.τ a') with h | h
      · exact (R.non_unit a' ha2).1 (by omega)
      · exact (R.non_unit a' ha2).2 (by omega)
    · have hb1 : (R.τ b').natAbs = 1 := by nlinarith [hprime.pos, habs, h2]
      rcases Int.natAbs_eq (R.τ b') with h | h
      · exact (R.non_unit b' hb2).1 (by omega)
      · exact (R.non_unit b' hb2).2 (by omega)

lemma isSquare_prime_pow_even {p m : ℕ} (hp : p.Prime) (hsq : IsSquare (p ^ m)) : Even m := by
  obtain ⟨r, hr⟩ := hsq
  have hr_pos : 0 < r := Nat.eq_zero_or_pos r |>.resolve_left
    (fun h => by rw [h, mul_zero] at hr; exact pow_ne_zero _ hp.ne_zero hr)
  have hfact : (p ^ m).factorization p = m := by simp [Nat.Prime.factorization_pow hp]
  have hfact2 : (r * r).factorization p = 2 * r.factorization p := by
    simp [show r * r = r ^ 2 by ring, Nat.factorization_pow]
  rw [hr, hfact2] at hfact
  exact ⟨r.factorization p, by omega⟩

lemma odd_prime_tau_value_even_power (R : RamanujanTau) (n : ℕ+) (p : ℕ) (m : ℕ) (ℓ : ℕ)
    (hprime_ℓ : Nat.Prime ℓ) (hne2 : ℓ ≠ 2)
    (hprime_p : p.Prime) (hm : 1 ≤ m) (hn : (n : ℕ) = p ^ m)
    (habs : (R.τ n).natAbs = ℓ) :
    ∃ k : ℕ, 1 ≤ k ∧ m = 2 * k := by
  have hτ_odd : ¬(2 ∣ R.τ n) := by
    intro h2div
    exact hne2 (hprime_ℓ.eq_one_or_self_of_dvd 2 (by rw [← habs]; exact Int.natAbs_dvd_natAbs.mpr h2div)
      |>.resolve_left (by omega) |>.symm)
  have ⟨_, hsq⟩ := (R.parity n).mp hτ_odd
  obtain ⟨k, hk⟩ := isSquare_prime_pow_even hprime_p (hn ▸ hsq)
  exact ⟨k, by omega, by omega⟩

lemma tau_prime_power_mem_X2k (R : RamanujanTau) (n : ℕ+) (p : ℕ) (k : ℕ)
    (hp : p.Prime) (hn : (n : ℕ) = p ^ (2 * k)) :
    R.τ n ∈ X2k R k := by
  let p' : ℕ+ := ⟨p, hp.pos⟩
  have hn_pnat : n = p' ^ (2 * k) := PNat.eq (by simp only [PNat.pow_coe, p']; exact hn)
  exact ⟨p', hp, by rw [hn_pnat]⟩

lemma S_set_subset_union (R : RamanujanTau) (X : ℝ) :
    S_set R X ⊆ {2} ∪ {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ k : ℕ, 1 ≤ k ∧ ((ℓ : ℤ) ∈ X2k R k ∨ (-(ℓ : ℤ)) ∈ X2k R k)} := by
  intro ℓ hℓ
  simp only [S_set, Set.mem_setOf_eq] at hℓ
  obtain ⟨hprime, hle, n, habs⟩ := hℓ
  by_cases h2 : ℓ = 2
  · left
    exact Set.mem_singleton_iff.mpr h2
  · right
    simp only [Set.mem_setOf_eq]
    refine ⟨hprime, hle, ?_⟩
    obtain ⟨p, m, hp, hm, hnpm⟩ := prime_tau_value_is_prime_power R n ℓ hprime
      (prime_tau_value_n_ge_two R n ℓ hprime h2 habs) habs
    obtain ⟨k, hk1, hmk⟩ := odd_prime_tau_value_even_power R n p m ℓ hprime h2 hp hm hnpm habs
    refine ⟨k, hk1, ?_⟩
    have hmem : R.τ n ∈ X2k R k := tau_prime_power_mem_X2k R n p k hp (by rw [hnpm, hmk])
    rcases Int.natAbs_eq (R.τ n) with h | h
    · left
      rw [show (ℓ : ℤ) = R.τ n by omega]
      exact hmem
    · right
      rw [show -(ℓ : ℤ) = R.τ n by omega]
      exact hmem
/-! ## Finiteness lemmas -/

lemma pnat_bounded_finite (B : ℝ) : {x : ℕ+ | (x : ℝ) ≤ B}.Finite := by
  apply Set.Finite.subset (Set.finite_Icc (1 : ℕ+)
    ⟨Nat.ceil (max B 1), Nat.ceil_pos.mpr (lt_of_lt_of_le one_pos (le_max_right B 1))⟩)
  intro x hx
  exact Set.mem_Icc.mpr ⟨x.one_le, by
    show (x : ℕ) ≤ ⌈max B 1⌉₊
    rw [← Nat.ceil_natCast (R := ℝ) (x : ℕ)]
    exact Nat.ceil_le_ceil (by exact_mod_cast (show (x : ℝ) ≤ B from hx).trans (le_max_left B 1))⟩

lemma sq_le_imp_abs_le {y : ℤ} {K : ℤ} (_hK : 0 ≤ K) (h : y ^ 2 ≤ K) : |y| ≤ K := by
  rcases eq_or_ne y 0 with rfl | hy
  · simpa
  · nlinarith [Int.one_le_abs hy, sq_abs y]

lemma E2_y_fiber_finite (X : ℝ) (x : ℕ+) : {y : ℤ | (x, y) ∈ E2_set X}.Finite := by
  let K : ℤ := (x : ℤ) ^ 11 + Int.ceil (|X|)
  apply Set.Finite.subset (Set.finite_Icc (-K) K)
  intro y hy
  simp only [Set.mem_setOf_eq, E2_set] at hy
  obtain ⟨_, _, h3⟩ := hy
  simp only [Set.mem_Icc]
  have hK : (0 : ℤ) ≤ K := by positivity
  have hy_sq : y ^ 2 ≤ K := by
    suffices h : (y ^ 2 : ℝ) ≤ (K : ℝ) by exact_mod_cast h
    have h_sub : (↑y : ℝ) ^ 2 - (↑(↑(↑x : ℕ) : ℤ) : ℝ) ^ 11 ≤ |X| := by
      calc (↑y : ℝ) ^ 2 - (↑(↑(↑x : ℕ) : ℤ) : ℝ) ^ 11
          ≤ |(↑(↑(↑x : ℕ) : ℤ) : ℝ) ^ 11 - (↑y : ℝ) ^ 2| := by
            linarith [le_abs_self ((↑y : ℝ) ^ 2 - (↑(↑(↑x : ℕ) : ℤ) : ℝ) ^ 11),
                      abs_sub_comm ((↑(↑(↑x : ℕ) : ℤ) : ℝ) ^ 11) ((↑y : ℝ) ^ 2)]
        _ ≤ X := h3
        _ ≤ |X| := le_abs_self X
    push_cast at h_sub ⊢
    change (y : ℝ) ^ 2 ≤ ((↑↑x : ℤ) ^ 11 + ⌈|X|⌉ : ℤ)
    push_cast
    linarith [Int.le_ceil (|X| : ℝ)]
  exact ⟨by linarith [sq_le_imp_abs_le hK hy_sq, abs_nonneg y, neg_abs_le y],
    by linarith [sq_le_imp_abs_le hK hy_sq, le_abs_self y]⟩

lemma E2_y_zero_bound (ε : ℝ) (hε : 0 < ε) (hε2 : ε < 9 / 13) :
    ∀ X : ℝ, 1 < X → ∀ (p : ℕ+ × ℤ), p ∈ E2_set X → p.2 = 0 →
      (p.1 : ℝ) ≤ X ^ (((4 : ℝ) + 2 * ε) / (9 - 13 * ε)) := by
  intro X hX p hp hy
  simp only [E2_set, Set.mem_setOf_eq] at hp
  obtain ⟨_, _, habs_ub⟩ := hp
  rw [hy] at habs_ub
  have hX_pos : (0 : ℝ) < X := by linarith
  have hx11_le_X : ((p.1 : ℕ) : ℝ) ^ 11 ≤ X := by
    rw [show ((0 : ℤ) : ℝ) ^ 2 = 0 by norm_num, sub_zero,
      abs_of_nonneg (show (0 : ℝ) ≤ ((↑(p.1 : ℕ) : ℤ) : ℝ) ^ 11 by positivity),
      show ((↑(p.1 : ℕ) : ℤ) : ℝ) = ((p.1 : ℕ) : ℝ) by push_cast; ring] at habs_ub
    exact habs_ub
  have hx_le : ((p.1 : ℕ) : ℝ) ≤ X ^ ((1 : ℝ) / 11) := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (11 : ℕ) ≠ 0) (by positivity)
    rw [← Real.rpow_natCast (X ^ ((1 : ℝ) / 11)) 11, ← Real.rpow_mul hX_pos.le]
    norm_num
    exact hx11_le_X
  exact le_trans hx_le (Real.rpow_le_rpow_of_exponent_le (le_of_lt hX) (by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 11) (by nlinarith : (0 : ℝ) < 9 - 13 * ε)]
    nlinarith))
/-! ## Radical function properties -/

lemma radical_dvd (n : ℕ) (hn : 0 < n) : Nat.radical n ∣ n := by
  simp only [Nat.radical, Nat.pos_iff_ne_zero.mp hn, ↓reduceIte]
  exact Nat.prod_primeFactors_dvd n

lemma radical_le (n : ℕ) (hn : 0 < n) : Nat.radical n ≤ n :=
  Nat.le_of_dvd hn (radical_dvd n hn)

lemma radical_mul_le (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Nat.radical (a * b) ≤ Nat.radical a * Nat.radical b := by
  simp only [Nat.radical, Nat.pos_iff_ne_zero.mp ha, Nat.pos_iff_ne_zero.mp hb,
    (Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp ha) (Nat.pos_iff_ne_zero.mp hb)), if_false]
  rw [Nat.primeFactors_mul (Nat.pos_iff_ne_zero.mp ha) (Nat.pos_iff_ne_zero.mp hb)]
  have h := Finset.prod_union_inter (f := fun p => p)
            (s₁ := a.primeFactors) (s₂ := b.primeFactors)
  have hge : 1 ≤ ∏ p ∈ (a.primeFactors ∩ b.primeFactors), p :=
    Finset.one_le_prod' fun i hi => (Nat.prime_of_mem_primeFactors (Finset.mem_inter.mp hi).1).one_le
  calc ∏ p ∈ a.primeFactors ∪ b.primeFactors, p
      ≤ (∏ p ∈ a.primeFactors ∪ b.primeFactors, p) *
        (∏ p ∈ a.primeFactors ∩ b.primeFactors, p) := le_mul_of_one_le_right (Nat.zero_le _) hge
    _ = (∏ p ∈ a.primeFactors, p) * (∏ p ∈ b.primeFactors, p) := h

lemma radical_pow (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : 0 < k) :
    Nat.radical (n ^ k) = Nat.radical n := by
  simp_all [Nat.radical, show n ≠ 0 by omega, Nat.primeFactors_pow n (by omega : k ≠ 0)]

lemma radical_pos (n : ℕ) (hn : 0 < n) : 0 < Nat.radical n :=
  Nat.pos_of_ne_zero (fun h => by have := radical_dvd n hn; rw [h] at this; omega)

lemma radical_dvd_of_dvd (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hdvd : a ∣ b) :
    Nat.radical a ∣ Nat.radical b := by
  simp only [Nat.radical, show a ≠ 0 by omega, show b ≠ 0 by omega, ↓reduceIte]
  exact Finset.prod_dvd_prod_of_subset _ _ _ fun p hp => by
    rw [Nat.mem_primeFactors] at hp ⊢
    exact ⟨hp.1, dvd_trans hp.2.1 hdvd, by omega⟩

lemma radical_dvd_pow_le (x : ℕ) (hx : 0 < x) (k : ℕ) (hk : 0 < k)
    (a : ℕ) (ha : 0 < a) (hdvd : a ∣ x ^ k) :
    Nat.radical a ≤ x := by
  have h1 := radical_dvd_of_dvd a (x ^ k) ha (by positivity) hdvd
  rw [radical_pow x hx k hk] at h1
  exact le_trans (Nat.le_of_dvd (radical_pos x hx) h1) (radical_le x hx)

lemma gcd_coprime_triple (x : ℕ) (hx : 0 < x) (y_abs : ℕ) (hy : 0 < y_abs)
    (d : ℕ) (hd : 0 < d) (hsum : y_abs ^ 2 + d = x ^ 11) :
    ∃ a' b' c' g : ℕ,
      0 < a' ∧ 0 < b' ∧ 0 < c' ∧ 0 < g ∧
      Nat.Coprime a' b' ∧
      a' + b' = c' ∧
      g * c' = x ^ 11 ∧
      a' ∣ y_abs ^ 2 ∧ b' ∣ d ∧ c' ∣ x ^ 11 ∧
      g ≤ d := by
  set g := Nat.gcd (y_abs ^ 2) d with hg_def
  have hg_pos : 0 < g := Nat.pos_of_ne_zero (by intro h; simp [hg_def] at h; omega)
  have hg_dvd_l : g ∣ y_abs ^ 2 := Nat.gcd_dvd_left ..
  have hg_dvd_r : g ∣ d := Nat.gcd_dvd_right ..
  have hg_dvd_sum : g ∣ x ^ 11 := hsum ▸ dvd_add hg_dvd_l hg_dvd_r
  refine ⟨y_abs ^ 2 / g, d / g, x ^ 11 / g, g,
    Nat.div_pos (Nat.le_of_dvd (by positivity) hg_dvd_l) hg_pos,
    Nat.div_pos (Nat.le_of_dvd hd hg_dvd_r) hg_pos,
    Nat.div_pos (Nat.le_of_dvd (by positivity) hg_dvd_sum) hg_pos,
    hg_pos, Nat.coprime_div_gcd_div_gcd hg_pos, ?_,
    Nat.mul_div_cancel' hg_dvd_sum,
    Nat.div_dvd_of_dvd hg_dvd_l, Nat.div_dvd_of_dvd hg_dvd_r,
    Nat.div_dvd_of_dvd hg_dvd_sum, Nat.le_of_dvd hd hg_dvd_r⟩
  exact Nat.mul_right_cancel hg_pos (by
    rw [Nat.add_mul, Nat.div_mul_cancel hg_dvd_l,
      Nat.div_mul_cancel hg_dvd_r, Nat.div_mul_cancel hg_dvd_sum, hsum])

lemma radical_triple_bound (x : ℕ) (hx : 0 < x) (y_abs : ℕ) (hy : 0 < y_abs)
    (d : ℕ) (hd : 0 < d)
    (a' b' c' : ℕ) (ha' : 0 < a') (hb' : 0 < b') (hc' : 0 < c')
    (ha_dvd : a' ∣ y_abs ^ 2) (hb_dvd : b' ∣ d) (hc_dvd : c' ∣ x ^ 11) :
    (Nat.radical (a' * b' * c') : ℝ) ≤ (y_abs : ℝ) * (d : ℝ) * (x : ℝ) := by
  have ha_bound : Nat.radical a' ≤ y_abs := by
    calc Nat.radical a' ≤ Nat.radical (y_abs ^ 2) :=
          Nat.le_of_dvd (radical_pos _ (pow_pos hy 2)) (radical_dvd_of_dvd _ _ ha' (pow_pos hy 2) ha_dvd)
      _ = Nat.radical y_abs := radical_pow y_abs hy 2 (by norm_num)
      _ ≤ y_abs := radical_le y_abs hy
  have hb_bound : Nat.radical b' ≤ d :=
    le_trans (radical_le b' hb') (Nat.le_of_dvd hd hb_dvd)
  have hc_bound : Nat.radical c' ≤ x := radical_dvd_pow_le x hx 11 (by norm_num) c' hc' hc_dvd
  exact_mod_cast show Nat.radical (a' * b' * c') ≤ y_abs * d * x from
    calc Nat.radical (a' * b' * c')
        ≤ Nat.radical (a' * b') * Nat.radical c' :=
          radical_mul_le _ _ (Nat.mul_pos ha' hb') hc'
      _ ≤ Nat.radical a' * Nat.radical b' * Nat.radical c' :=
          Nat.mul_le_mul_right _ (radical_mul_le _ _ ha' hb')
      _ ≤ y_abs * d * x :=
          Nat.mul_le_mul (Nat.mul_le_mul ha_bound hb_bound) hc_bound
/-! ## ABC-based bounds for E₂ (Case 1: x^{11} ≥ y²) -/

lemma rpow_mul_self (X : ℝ) (hX : 0 < X) (ε : ℝ) :
    X * X ^ (1 + ε) = X ^ (2 + ε) := by
  have : X ^ (1 : ℝ) * X ^ (1 + ε) = X ^ (2 + ε) := by
    rw [← Real.rpow_add hX]
    congr 1
    ring
  rwa [Real.rpow_one] at this

lemma abc_real_chain (K : ℝ) (hK : 0 < K) (ε : ℝ) (hε : 0 < ε)
    (x : ℕ) (hx : 0 < x) (y_abs : ℕ) (hy : 0 < y_abs)
    (d : ℕ) (hd : 0 < d) (X : ℝ) (hX : 1 < X)
    (g c' : ℕ) (hg : 0 < g) (_hc' : 0 < c')
    (hgc : g * c' = x ^ 11)
    (hg_le_d : g ≤ d)
    (habc_rad : (c' : ℝ) ≤ K * ((y_abs : ℝ) * (d : ℝ) * (x : ℝ)) ^ (1 + ε))
    (hd_le : (d : ℝ) ≤ X)
    (hy_le : (y_abs : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 2)) :
    (x : ℝ) ^ (11 : ℝ) ≤
      K * ((x : ℝ) ^ ((13 * (1 + ε)) / 2)) * X ^ (2 + ε) := by
  have hx_pos : (0 : ℝ) < (x : ℝ) := Nat.cast_pos.mpr hx
  have hX_pos : (0 : ℝ) < X := by linarith
  have heq : (x : ℝ) ^ (11 : ℝ) = (g : ℝ) * (c' : ℝ) := by
    rw [show (x : ℝ) ^ (11 : ℝ) = (x : ℝ) ^ (11 : ℕ) by exact_mod_cast Real.rpow_natCast (x : ℝ) 11,
      show (x : ℝ) ^ (11 : ℕ) = ((x ^ 11 : ℕ) : ℝ) by push_cast; ring, ← hgc]
    push_cast
    ring
  have h5base : (y_abs : ℝ) * (d : ℝ) * (x : ℝ) ≤ (x : ℝ) ^ ((13 : ℝ) / 2) * X := by
    have : (y_abs : ℝ) * (d : ℝ) * (x : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 2) * X * (x : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul hy_le hd_le (by positivity) (by positivity)) hx_pos.le
    have hxp : (x : ℝ) ^ ((11 : ℝ) / 2) * (x : ℝ) = (x : ℝ) ^ ((13 : ℝ) / 2) := by
      calc (x : ℝ) ^ ((11 : ℝ) / 2) * (x : ℝ)
          = (x : ℝ) ^ ((11 : ℝ) / 2) * (x : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = (x : ℝ) ^ ((11 : ℝ) / 2 + 1) := by rw [← Real.rpow_add hx_pos]
        _ = (x : ℝ) ^ ((13 : ℝ) / 2) := by norm_num
    nlinarith [hxp, mul_comm X (x : ℝ), mul_assoc ((x : ℝ) ^ ((11 : ℝ) / 2)) X (x : ℝ)]
  have h5 : ((y_abs : ℝ) * (d : ℝ) * (x : ℝ)) ^ (1 + ε) ≤
      (x : ℝ) ^ ((13 * (1 + ε)) / 2) * X ^ (1 + ε) := by
    calc ((y_abs : ℝ) * (d : ℝ) * (x : ℝ)) ^ (1 + ε)
        ≤ ((x : ℝ) ^ ((13 : ℝ) / 2) * X) ^ (1 + ε) := Real.rpow_le_rpow (by positivity) h5base (by linarith)
      _ = ((x : ℝ) ^ ((13 : ℝ) / 2)) ^ (1 + ε) * X ^ (1 + ε) :=
            Real.mul_rpow (Real.rpow_nonneg hx_pos.le _) hX_pos.le
      _ = (x : ℝ) ^ ((13 * (1 + ε)) / 2) * X ^ (1 + ε) := by
            rw [← Real.rpow_mul hx_pos.le]
            congr 1
            ring_nf
  calc (x : ℝ) ^ (11 : ℝ) = (g : ℝ) * (c' : ℝ) := heq
    _ ≤ (g : ℝ) * (K * ((y_abs : ℝ) * (d : ℝ) * (x : ℝ)) ^ (1 + ε)) :=
        mul_le_mul_of_nonneg_left habc_rad (by positivity)
    _ ≤ X * (K * ((y_abs : ℝ) * (d : ℝ) * (x : ℝ)) ^ (1 + ε)) :=
        mul_le_mul_of_nonneg_right (le_trans (Nat.cast_le.mpr hg_le_d) hd_le) (by positivity)
    _ ≤ X * (K * ((x : ℝ) ^ ((13 * (1 + ε)) / 2) * X ^ (1 + ε))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 hK.le) hX_pos.le
    _ = K * (x : ℝ) ^ ((13 * (1 + ε)) / 2) * (X * X ^ (1 + ε)) := by ring
    _ = K * (x : ℝ) ^ ((13 * (1 + ε)) / 2) * X ^ (2 + ε) := by rw [rpow_mul_self X hX_pos ε]

lemma abc_nat_bound (K : ℝ) (hK : 0 < K) (ε : ℝ) (hε : 0 < ε)
    (hK_abc : ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
      Nat.Coprime a b → a + b = c →
        (c : ℝ) ≤ K * ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε))
    (x : ℕ) (hx : 0 < x) (y_abs : ℕ) (hy : 0 < y_abs)
    (d : ℕ) (hd : 0 < d) (X : ℝ) (hX : 1 < X)
    (hsum : y_abs ^ 2 + d = x ^ 11)
    (hd_le : (d : ℝ) ≤ X)
    (hy_le : (y_abs : ℝ) ≤ (x : ℝ) ^ ((11 : ℝ) / 2)) :
    (x : ℝ) ^ (11 : ℝ) ≤
      K * ((x : ℝ) ^ ((13 * (1 + ε)) / 2)) * X ^ (2 + ε) := by
  obtain ⟨a', b', c', g, ha', hb', hc', hg, hcop, hab_sum, hgc, ha_dvd, hb_dvd, hc_dvd, hg_le_d⟩ :=
    gcd_coprime_triple x hx y_abs hy d hd hsum
  have habc_rad : (c' : ℝ) ≤ K * ((y_abs : ℝ) * (d : ℝ) * (x : ℝ)) ^ (1 + ε) :=
    le_trans (hK_abc a' b' c' ha' hb' hc' hcop hab_sum)
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _)
        (radical_triple_bound x hx y_abs hy d hd a' b' c' ha' hb' hc' ha_dvd hb_dvd hc_dvd)
        (by linarith)) hK.le)
  exact abc_real_chain K hK ε hε x hx y_abs hy d hd X hX g c' hg hc' hgc hg_le_d habc_rad hd_le hy_le

lemma int_to_nat_decomposition (x : ℕ+) (y : ℤ)
    (hcase : (x : ℤ) ^ 11 ≥ y ^ 2) :
    y.natAbs ^ 2 + ((↑x : ℤ) ^ 11 - y ^ 2).toNat = (x : ℕ) ^ 11 := by
  have hysq : y ^ 2 = (y.natAbs : ℤ) ^ 2 := (Int.natAbs_sq y).symm
  rw [hysq]
  have hle : (y.natAbs : ℤ) ^ 2 ≤ (x : ℤ) ^ 11 := by linarith
  rw [show (↑↑x : ℤ) ^ 11 - (↑y.natAbs : ℤ) ^ 2 = ↑((x : ℕ) ^ 11 - y.natAbs ^ 2) by
    rw [Int.ofNat_sub]
    · push_cast
      ring
    · exact_mod_cast hle]
  simp only [Int.toNat_natCast]
  have : y.natAbs ^ 2 ≤ (x : ℕ) ^ 11 := by exact_mod_cast hle
  omega

lemma y_natAbs_le_x_pow (x : ℕ+) (y : ℤ) (_hy : y ≠ 0)
    (hd_pos : 1 ≤ |(↑x : ℤ) ^ 11 - y ^ 2|)
    (hcase : (x : ℤ) ^ 11 ≥ y ^ 2) :
    (y.natAbs : ℝ) ≤ ((x : ℕ) : ℝ) ^ ((11 : ℝ) / 2) := by
  have h1 : y ^ 2 < (↑x : ℤ) ^ 11 := by
    have := abs_of_nonneg (show 0 ≤ (↑x : ℤ) ^ 11 - y ^ 2 by omega)
    omega
  have h2 : ((y.natAbs : ℕ) : ℝ) ^ 2 ≤ ((x : ℕ) : ℝ) ^ 11 := by
    exact_mod_cast show (y.natAbs : ℤ) ^ 2 ≤ (↑x : ℤ) ^ 11 by rw [Int.natAbs_sq]; exact h1.le
  rw [← show √(((x : ℕ) : ℝ) ^ 11) = ((x : ℕ) : ℝ) ^ ((11 : ℝ) / 2) by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((x : ℕ) : ℝ) 11,
      ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num]
  exact Real.le_sqrt_of_sq_le h2

lemma rpow_divide_case1 (K : ℝ) (_hK : 0 < K) (ε : ℝ) (_hε : 0 < ε) (_hε2 : ε < 9 / 13)
    (x : ℕ+) (X : ℝ) (_hX : 1 < X)
    (h : ((x : ℕ) : ℝ) ^ (11 : ℝ) ≤ K * ((x : ℝ) ^ ((13 * (1 + ε)) / 2)) * X ^ (2 + ε)) :
    (x : ℝ) ^ ((9 - 13 * ε) / 2) ≤ K * X ^ (2 + ε) := by
  have hx_pos : (0 : ℝ) < (x : ℕ) := Nat.cast_pos.mpr x.pos
  rw [show (9 - 13 * ε) / 2 = (11 : ℝ) - 13 * (1 + ε) / 2 by ring,
    Real.rpow_sub hx_pos, div_le_iff₀ (Real.rpow_pos_of_pos hx_pos _),
    mul_comm (K * X ^ (2 + ε)) _]
  linarith

lemma abc_case1_bound (K : ℝ) (hK : 0 < K) (ε : ℝ) (hε : 0 < ε) (hε2 : ε < 9 / 13)
    (hK_abc : ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
      Nat.Coprime a b → a + b = c →
        (c : ℝ) ≤ K * ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε))
    (x : ℕ+) (y : ℤ) (hy : y ≠ 0) (X : ℝ) (hX : 1 < X)
    (_hx_gt : (x : ℝ) > X ^ ((2 : ℝ) / 11))
    (hd_pos : 1 ≤ |(↑x : ℤ) ^ 11 - y ^ 2|)
    (hd_le : (|(↑x : ℤ) ^ 11 - y ^ 2| : ℝ) ≤ X)
    (hcase : (x : ℤ) ^ 11 ≥ y ^ 2) :
    (x : ℝ) ^ ((9 - 13 * ε) / 2) ≤
      K * (2 : ℝ) ^ ((1 + ε) / 2) * X ^ (2 + ε) := by
  have hd_pos' : 0 < ((↑x : ℤ) ^ 11 - y ^ 2).toNat := by
    have := hd_pos
    rw [abs_of_nonneg (show (0 : ℤ) ≤ (↑x : ℤ) ^ 11 - y ^ 2 by omega)] at this
    omega
  have h_nn : (0 : ℤ) ≤ (↑x : ℤ) ^ 11 - y ^ 2 := by linarith
  have d_le : (((↑x : ℤ) ^ 11 - y ^ 2).toNat : ℝ) ≤ X := by
    linarith [show (((↑x : ℤ) ^ 11 - y ^ 2).toNat : ℝ) = ((↑x : ℤ) ^ 11 - y ^ 2 : ℝ) by
      exact_mod_cast Int.toNat_of_nonneg h_nn,
      show (|(↑x : ℤ) ^ 11 - y ^ 2| : ℝ) = ((↑x : ℤ) ^ 11 - y ^ 2 : ℝ) by
        rw [abs_of_nonneg]; norm_cast]
  calc _ ≤ K * X ^ (2 + ε) := rpow_divide_case1 K hK ε hε hε2 x X hX
          (abc_nat_bound K hK ε hε hK_abc (x : ℕ) x.pos y.natAbs
            (Int.natAbs_pos.mpr hy) _ hd_pos' X hX
            (int_to_nat_decomposition x y hcase) d_le
            (y_natAbs_le_x_pow x y hy hd_pos hcase))
    _ ≤ K * X ^ (2 + ε) * (2 : ℝ) ^ ((1 + ε) / 2) :=
        le_mul_of_one_le_right (by positivity) (Real.one_le_rpow (by linarith) (by linarith))
    _ = K * (2 : ℝ) ^ ((1 + ε) / 2) * X ^ (2 + ε) := by ring
/-! ## ABC-based bounds for E₂ (Case 2: y² > x^{11}) -/

lemma d_nat_le_X_case2 (x : ℕ+) (y : ℤ) (X : ℝ)
    (hd_le : (|(↑x : ℤ) ^ 11 - y ^ 2| : ℝ) ≤ X)
    (_hcase : y ^ 2 > (x : ℤ) ^ 11) :
    ((y ^ 2 - (↑x : ℤ) ^ 11).natAbs : ℝ) ≤ X := by
  rw [Nat.cast_natAbs, abs_sub_comm, Int.cast_abs]
  push_cast
  exact hd_le

lemma d_nat_lt_x11 (x : ℕ+) (d_nat : ℕ) (X : ℝ) (hX : 1 < X)
    (hx_gt : (x : ℝ) > X ^ ((2 : ℝ) / 11))
    (hd_le : (d_nat : ℝ) ≤ X) :
    d_nat < (x : ℕ) ^ 11 := by
  have hX_pos : (0 : ℝ) < X := by linarith
  exact_mod_cast show (d_nat : ℝ) < ((x : ℕ) : ℝ) ^ (11 : ℕ) by
    rw [show ((x : ℕ) : ℝ) ^ (11 : ℕ) = (x : ℝ) ^ (11 : ℝ) by rw [← Real.rpow_natCast]; norm_cast]
    linarith [Real.rpow_lt_rpow (by positivity) hx_gt (by norm_num : (0 : ℝ) < 11 / 2),
      show (X ^ ((2 : ℝ) / 11)) ^ ((11 : ℝ) / 2) = X from by
        rw [← Real.rpow_mul hX_pos.le]; ring_nf; exact Real.rpow_one X,
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast x.2 : (1 : ℝ) ≤ x) (by norm_num : (11 : ℝ) / 2 ≤ 11)]

lemma case2_extract_d (x : ℕ+) (y : ℤ) (_hy : y ≠ 0) (X : ℝ) (hX : 1 < X)
    (hx_gt : (x : ℝ) > X ^ ((2 : ℝ) / 11))
    (_hd_pos : 1 ≤ |(↑x : ℤ) ^ 11 - y ^ 2|)
    (hd_le : (|(↑x : ℤ) ^ 11 - y ^ 2| : ℝ) ≤ X)
    (hcase : y ^ 2 > (x : ℤ) ^ 11) :
    ∃ d_nat : ℕ, 1 ≤ d_nat ∧ (d_nat : ℝ) ≤ X
      ∧ (x : ℕ) ^ 11 + d_nat = y.natAbs ^ 2
      ∧ d_nat < (x : ℕ) ^ 11 :=
  ⟨(y ^ 2 - (↑x : ℤ) ^ 11).natAbs,
    Int.natAbs_pos.mpr (by omega),
    d_nat_le_X_case2 x y X hd_le hcase,
    by have hnn : (0 : ℤ) ≤ y ^ 2 - (↑x : ℤ) ^ 11 := by omega
       zify; rw [abs_of_nonneg hnn, sq_abs]; omega,
    d_nat_lt_x11 x _ X hX hx_gt (d_nat_le_X_case2 x y X hd_le hcase)⟩

lemma case2_radical_bound (x : ℕ) (hx : 0 < x) (d_nat : ℕ) (_hd : 0 < d_nat)
    (y_abs : ℕ) (hy : 0 < y_abs)
    (hsum : x ^ 11 + d_nat = y_abs ^ 2)
    (g : ℕ) (hg : g = Nat.gcd (x ^ 11) d_nat)
    (hg_pos : 0 < g)
    (a' b' c' : ℕ)
    (ha' : a' = x ^ 11 / g) (hb' : b' = d_nat / g) (hc' : c' = y_abs ^ 2 / g)
    (ha'_pos : 0 < a') (hb'_pos : 0 < b') (hc'_pos : 0 < c') :
    (Nat.radical (a' * b' * c') : ℝ) ≤ (x : ℝ) * (d_nat : ℝ) * (y_abs : ℝ) := by
  have h_submult : Nat.radical (a' * b' * c') ≤ Nat.radical a' * Nat.radical b' * Nat.radical c' :=
    le_trans (radical_mul_le _ _ (Nat.mul_pos ha'_pos hb'_pos) hc'_pos)
      (Nat.mul_le_mul_right _ (radical_mul_le _ _ ha'_pos hb'_pos))
  have ha'_dvd : a' ∣ x ^ 11 := by
    subst ha'
    subst hg
    exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
  have h_rad_a : Nat.radical a' ≤ x := radical_dvd_pow_le x hx 11 (by norm_num) a' ha'_pos ha'_dvd
  have h_rad_b : Nat.radical b' ≤ d_nat :=
    le_trans (radical_le b' hb'_pos) (by subst hb'; exact Nat.div_le_self d_nat g)
  have hc'_dvd : c' ∣ y_abs ^ 2 := by
    subst hc'
    subst hg
    exact Nat.div_dvd_of_dvd (hsum ▸ Dvd.dvd.add (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _))
  have h_rad_c : Nat.radical c' ≤ y_abs := radical_dvd_pow_le y_abs hy 2 (by norm_num) c' hc'_pos hc'_dvd
  exact_mod_cast le_trans h_submult (Nat.mul_le_mul (Nat.mul_le_mul h_rad_a h_rad_b) h_rad_c)

lemma case2_yabs_real_bound (x : ℕ) (_hx : 0 < x) (y_abs : ℕ)
    (hysq : y_abs ^ 2 < 2 * x ^ 11) :
    (y_abs : ℝ) < Real.sqrt 2 * (x : ℝ) ^ ((11 : ℝ) / 2) := by
  have h1 := Real.sqrt_lt_sqrt (sq_nonneg (y_abs : ℝ))
    (show (y_abs : ℝ) ^ 2 < 2 * (x : ℝ) ^ 11 by exact_mod_cast hysq)
  rw [Real.sqrt_sq (Nat.cast_nonneg y_abs),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    show Real.sqrt ((x : ℝ) ^ 11) = (x : ℝ) ^ ((11 : ℝ) / 2) by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (x : ℝ) 11,
        ← Real.rpow_mul (Nat.cast_nonneg x)]; norm_num] at h1
  exact h1

lemma case2_rad_overall_bound (x : ℕ) (hx : 0 < x) (d_nat : ℕ) (y_abs : ℕ)
    (X : ℝ) (_hX : 0 < X)
    (rad_val : ℝ) (hrad_le : rad_val ≤ (x : ℝ) * (d_nat : ℝ) * (y_abs : ℝ))
    (_hrad_nn : 0 ≤ rad_val)
    (hd_le : (d_nat : ℝ) ≤ X)
    (hy_bound : (y_abs : ℝ) < Real.sqrt 2 * (x : ℝ) ^ ((11 : ℝ) / 2)) :
    rad_val ≤ Real.sqrt 2 * (x : ℝ) ^ ((13 : ℝ) / 2) * X := by
  have hx_pos : (0 : ℝ) < (x : ℝ) := Nat.cast_pos.mpr hx
  have h_xy : (x : ℝ) * (y_abs : ℝ) ≤ Real.sqrt 2 * (x : ℝ) ^ ((13 : ℝ) / 2) := by
    have := mul_lt_mul_of_pos_left hy_bound hx_pos
    rw [show (x : ℝ) * (Real.sqrt 2 * (x : ℝ) ^ ((11 : ℝ) / 2)) =
        Real.sqrt 2 * ((x : ℝ) * (x : ℝ) ^ ((11 : ℝ) / 2)) by ring,
      show (x : ℝ) * (x : ℝ) ^ ((11 : ℝ) / 2) = (x : ℝ) ^ ((13 : ℝ) / 2) by
        rw [show (13 : ℝ) / 2 = 1 + 11 / 2 by norm_num,
          Real.rpow_add hx_pos, Real.rpow_one]] at this
    linarith
  calc rad_val ≤ (x : ℝ) * (d_nat : ℝ) * (y_abs : ℝ) := hrad_le
    _ = (x : ℝ) * (y_abs : ℝ) * (d_nat : ℝ) := by ring
    _ ≤ Real.sqrt 2 * (x : ℝ) ^ ((13 : ℝ) / 2) * (d_nat : ℝ) :=
        mul_le_mul_of_nonneg_right h_xy (Nat.cast_nonneg _)
    _ ≤ Real.sqrt 2 * (x : ℝ) ^ ((13 : ℝ) / 2) * X :=
        mul_le_mul_of_nonneg_left hd_le
          (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hx_pos.le _))

lemma case2_abc_upper (K : ℝ) (_hK : 0 < K) (ε : ℝ) (_hε : 0 < ε)
    (x : ℕ) (_hx : 0 < x) (X : ℝ) (hX : 0 < X)
    (c'_real : ℝ)
    (h_abc : c'_real ≤ K * (Real.sqrt 2 * (x : ℝ) ^ ((13 : ℝ) / 2) * X) ^ (1 + ε)) :
    c'_real ≤ K * (2 : ℝ) ^ ((1 + ε) / 2) * (x : ℝ) ^ (13 * (1 + ε) / 2) * X ^ (1 + ε) := by
  have hx_nn : (0 : ℝ) ≤ x := Nat.cast_nonneg _
  calc c'_real ≤ K * (Real.sqrt 2 * (x : ℝ) ^ ((13 : ℝ) / 2) * X) ^ (1 + ε) := h_abc
    _ = K * ((2 : ℝ) ^ ((1 + ε) / 2) * (x : ℝ) ^ (13 * (1 + ε) / 2) * X ^ (1 + ε)) := by
        rw [Real.mul_rpow (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hx_nn _)) hX.le,
          Real.mul_rpow (Real.sqrt_nonneg _) (Real.rpow_nonneg hx_nn _),
          show (Real.sqrt 2) ^ (1 + ε) = (2 : ℝ) ^ ((1 + ε) / 2) by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]; ring_nf,
          show ((x : ℝ) ^ ((13 : ℝ) / 2)) ^ (1 + ε) = (x : ℝ) ^ (13 * (1 + ε) / 2) by
            rw [← Real.rpow_mul hx_nn]; ring_nf]
    _ = K * (2 : ℝ) ^ ((1 + ε) / 2) * (x : ℝ) ^ (13 * (1 + ε) / 2) * X ^ (1 + ε) := by ring

lemma case2_cprime_lower (x : ℕ) (hx : 0 < x) (d_nat : ℕ) (hd : 0 < d_nat)
    (y_abs : ℕ) (X : ℝ) (hX : 0 < X)
    (hsum : x ^ 11 + d_nat = y_abs ^ 2)
    (g : ℕ) (hg : g = Nat.gcd (x ^ 11) d_nat)
    (hg_le_X : (g : ℝ) ≤ X)
    (c' : ℕ) (hc' : c' = y_abs ^ 2 / g) (_hc'_pos : 0 < c') :
    (x : ℝ) ^ (11 : ℝ) / X < (c' : ℝ) := by
  have hg_dvd_x11 : g ∣ x ^ 11 := hg ▸ Nat.gcd_dvd_left _ _
  have hg_dvd_d : g ∣ d_nat := hg ▸ Nat.gcd_dvd_right _ _
  have hg_dvd : g ∣ y_abs ^ 2 := hsum ▸ Dvd.dvd.add hg_dvd_x11 hg_dvd_d
  have hg_pos : 0 < g := hg ▸ Nat.pos_of_ne_zero (Nat.gcd_ne_zero_left (by positivity))
  rw [show (x : ℝ) ^ (11 : ℝ) = (x : ℝ) ^ (11 : ℕ) by
      exact_mod_cast Real.rpow_natCast (x : ℝ) 11,
    show (c' : ℝ) = ↑(y_abs ^ 2 : ℕ) / (g : ℝ) from by rw [hc', Nat.cast_div_charZero hg_dvd]]
  push_cast
  exact lt_of_lt_of_le
    (div_lt_div_of_pos_right (by exact_mod_cast show x ^ 11 < y_abs ^ 2 by omega) hX)
    (div_le_div_of_nonneg_left (by positivity) (Nat.cast_pos.mpr hg_pos) hg_le_X)

lemma case2_combine_bounds (K : ℝ) (_hK : 0 < K) (ε : ℝ) (_hε : 0 < ε)
    (x : ℕ) (_hx : 0 < x) (X : ℝ) (hX : 0 < X)
    (c'_real : ℝ)
    (h_lower : (x : ℝ) ^ (11 : ℝ) / X < c'_real)
    (h_upper : c'_real ≤ K * (2 : ℝ) ^ ((1 + ε) / 2) * (x : ℝ) ^ (13 * (1 + ε) / 2) * X ^ (1 + ε)) :
    (x : ℝ) ^ (11 : ℝ) ≤
      K * (2 : ℝ) ^ ((1 + ε) / 2) * (x : ℝ) ^ (13 * (1 + ε) / 2) * X ^ (2 + ε) := by
  have h_chain := (div_lt_iff₀ hX).mp (lt_of_lt_of_le h_lower h_upper)
  linarith [show K * (2 : ℝ) ^ ((1 + ε) / 2) * (x : ℝ) ^ (13 * (1 + ε) / 2) * X ^ (1 + ε) * X =
    K * (2 : ℝ) ^ ((1 + ε) / 2) * (x : ℝ) ^ (13 * (1 + ε) / 2) * X ^ (2 + ε) from by
    rw [mul_assoc, mul_comm (X ^ (1 + ε)) X, rpow_mul_self X hX ε]]

lemma gcd_coprime_triple_sum (x : ℕ) (hx : 0 < x) (d_nat : ℕ) (hd : 0 < d_nat)
    (y_abs : ℕ) (hy : 0 < y_abs)
    (hsum : x ^ 11 + d_nat = y_abs ^ 2)
    (_hd_lt : d_nat < x ^ 11) :
    ∃ a' b' c' : ℕ,
      0 < a' ∧ 0 < b' ∧ 0 < c' ∧
      Nat.Coprime a' b' ∧ a' + b' = c' ∧
      a' = x ^ 11 / Nat.gcd (x ^ 11) d_nat ∧
      b' = d_nat / Nat.gcd (x ^ 11) d_nat ∧
      c' = y_abs ^ 2 / Nat.gcd (x ^ 11) d_nat := by
  set g := Nat.gcd (x ^ 11) d_nat with hg_def
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right _ hd
  have hg_dvd_x : g ∣ x ^ 11 := Nat.gcd_dvd_left _ _
  have hg_dvd_d : g ∣ d_nat := Nat.gcd_dvd_right _ _
  have hg_dvd_y : g ∣ y_abs ^ 2 := hsum ▸ dvd_add hg_dvd_x hg_dvd_d
  exact ⟨x ^ 11 / g, d_nat / g, y_abs ^ 2 / g,
    Nat.div_pos (Nat.le_of_dvd (by positivity) hg_dvd_x) hg_pos,
    Nat.div_pos (Nat.le_of_dvd hd hg_dvd_d) hg_pos,
    Nat.div_pos (Nat.le_of_dvd (by positivity) hg_dvd_y) hg_pos,
    Nat.coprime_div_gcd_div_gcd hg_pos,
    by rw [← Nat.add_div_of_dvd_right hg_dvd_x, hsum],
    rfl, rfl, rfl⟩

lemma case2_gcd_abc_chain (K : ℝ) (hK : 0 < K) (ε : ℝ) (hε : 0 < ε)
    (hK_abc : ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
      Nat.Coprime a b → a + b = c →
        (c : ℝ) ≤ K * ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε))
    (x : ℕ) (hx : 0 < x) (d_nat : ℕ) (hd : 0 < d_nat)
    (y_abs : ℕ) (hy : 0 < y_abs)
    (hsum : x ^ 11 + d_nat = y_abs ^ 2)
    (hd_lt : d_nat < x ^ 11)
    (X : ℝ) (hX : 0 < X)
    (hd_le : (d_nat : ℝ) ≤ X) :
    ∃ c' : ℕ, 0 < c' ∧
      (x : ℝ) ^ (11 : ℝ) / X < (c' : ℝ) ∧
      (c' : ℝ) ≤ K * (Real.sqrt 2 * (x : ℝ) ^ ((13 : ℝ) / 2) * X) ^ (1 + ε) := by
  obtain ⟨a', b', c', ha'_pos, hb'_pos, hc'_pos, hcop, hsum_abc, ha'_eq, hb'_eq, hc'_eq⟩ :=
    gcd_coprime_triple_sum x hx d_nat hd y_abs hy hsum hd_lt
  set g := Nat.gcd (x ^ 11) d_nat with hg_def
  have hg_pos : 0 < g :=
    Nat.pos_of_ne_zero (by intro h; simp [hg_def, Nat.gcd_eq_zero_iff] at h; omega)
  have hg_le_X : (g : ℝ) ≤ X :=
    le_trans (Nat.cast_le.mpr (Nat.le_of_dvd hd (Nat.gcd_dvd_right _ _))) hd_le
  refine ⟨c', hc'_pos,
    case2_cprime_lower x hx d_nat hd y_abs X hX hsum g hg_def hg_le_X c' hc'_eq hc'_pos, ?_⟩
  · have hrad_overall := case2_rad_overall_bound x hx d_nat y_abs X hX
      ((Nat.radical (a' * b' * c') : ℕ) : ℝ)
      (case2_radical_bound x hx d_nat hd y_abs hy hsum
        g hg_def hg_pos a' b' c' ha'_eq hb'_eq hc'_eq ha'_pos hb'_pos hc'_pos)
      (Nat.cast_nonneg _) hd_le (case2_yabs_real_bound x hx y_abs (by omega))
    calc (c' : ℝ)
        ≤ K * ((Nat.radical (a' * b' * c') : ℕ) : ℝ) ^ (1 + ε) :=
          hK_abc a' b' c' ha'_pos hb'_pos hc'_pos hcop hsum_abc
      _ ≤ K * (Real.sqrt 2 * (x : ℝ) ^ ((13 : ℝ) / 2) * X) ^ (1 + ε) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (Nat.cast_nonneg _) hrad_overall (by linarith)) hK.le

lemma case2_x11_le_chain (K : ℝ) (hK : 0 < K) (ε : ℝ) (hε : 0 < ε) (hε2 : ε < 9 / 13)
    (hK_abc : ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
      Nat.Coprime a b → a + b = c →
        (c : ℝ) ≤ K * ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε))
    (x : ℕ+) (y : ℤ) (hy : y ≠ 0) (X : ℝ) (hX : 1 < X)
    (hx_gt : (x : ℝ) > X ^ ((2 : ℝ) / 11))
    (hd_pos : 1 ≤ |(↑x : ℤ) ^ 11 - y ^ 2|)
    (hd_le : (|(↑x : ℤ) ^ 11 - y ^ 2| : ℝ) ≤ X)
    (hcase : y ^ 2 > (x : ℤ) ^ 11) :
    (x : ℝ) ^ (11 : ℝ) ≤
      K * (2 : ℝ) ^ ((1 + ε) / 2) * (x : ℝ) ^ (13 * (1 + ε) / 2) * X ^ (2 + ε) := by
  obtain ⟨d_nat, hd1, hd_le_X, hsum, hd_lt⟩ := case2_extract_d x y hy X hX hx_gt hd_pos hd_le hcase
  obtain ⟨c', hc'_pos, hc'_lower, hc'_upper⟩ :=
    case2_gcd_abc_chain K hK ε hε hK_abc (x : ℕ) x.pos d_nat (by omega)
      y.natAbs (Int.natAbs_pos.mpr hy) hsum hd_lt X (by linarith) hd_le_X
  exact case2_combine_bounds K hK ε hε (x : ℕ) x.pos X (by linarith) (c' : ℝ) hc'_lower
    (case2_abc_upper K hK ε hε (x : ℕ) x.pos X (by linarith) (c' : ℝ) hc'_upper)

lemma abc_case2_bound (K : ℝ) (hK : 0 < K) (ε : ℝ) (hε : 0 < ε) (hε2 : ε < 9 / 13)
    (hK_abc : ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
      Nat.Coprime a b → a + b = c →
        (c : ℝ) ≤ K * ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε))
    (x : ℕ+) (y : ℤ) (hy : y ≠ 0) (X : ℝ) (hX : 1 < X)
    (hx_gt : (x : ℝ) > X ^ ((2 : ℝ) / 11))
    (hd_pos : 1 ≤ |(↑x : ℤ) ^ 11 - y ^ 2|)
    (hd_le : (|(↑x : ℤ) ^ 11 - y ^ 2| : ℝ) ≤ X)
    (hcase : y ^ 2 > (x : ℤ) ^ 11) :
    (x : ℝ) ^ ((9 - 13 * ε) / 2) ≤
      K * (2 : ℝ) ^ ((1 + ε) / 2) * X ^ (2 + ε) := by
  have hK' : (0 : ℝ) < K * (2 : ℝ) ^ ((1 + ε) / 2) :=
    mul_pos hK (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _)
  exact rpow_divide_case1 (K * (2 : ℝ) ^ ((1 + ε) / 2)) hK' ε hε hε2 x X hX (by
    linarith [case2_x11_le_chain K hK ε hε hε2 hK_abc x y hy X hX hx_gt hd_pos hd_le hcase])

lemma rpow_le_of_rpow_le (ε : ℝ) (hε : 0 < ε) (hε2 : ε < 9 / 13)
    (M : ℝ) (_hM : 0 < M) (x : ℝ) (hx : 1 ≤ x)
    (hle : x ^ ((9 - 13 * ε) / 2) ≤ M) :
    x ≤ M ^ (2 / (9 - 13 * ε)) := by
  have hx0 : 0 ≤ x := by linarith
  have _hα : (0 : ℝ) < (9 - 13 * ε) / 2 := by linarith
  have h1 : (x ^ ((9 - 13 * ε) / 2)) ^ (1 / ((9 - 13 * ε) / 2)) ≤
      M ^ (1 / ((9 - 13 * ε) / 2)) :=
    Real.rpow_le_rpow (by positivity) hle (by positivity)
  rw [← Real.rpow_mul hx0, show (9 - 13 * ε) / 2 * (1 / ((9 - 13 * ε) / 2)) = 1 by
    field_simp [show (9 : ℝ) - 13 * ε ≠ 0 from ne_of_gt (by linarith)],
    Real.rpow_one] at h1
  rwa [show (1 : ℝ) / ((9 - 13 * ε) / 2) = 2 / (9 - 13 * ε) by field_simp] at h1

lemma rpow_product_split (K : ℝ) (hK : 0 < K) (ε : ℝ) (_hε : 0 < ε) (_hε2 : ε < 9 / 13)
    (X : ℝ) (hX : 0 < X) :
    (K * (2 : ℝ) ^ ((1 + ε) / 2) * X ^ (2 + ε)) ^ (2 / (9 - 13 * ε)) =
      (K * (2 : ℝ) ^ ((1 + ε) / 2)) ^ (2 / (9 - 13 * ε)) * X ^ (((4 : ℝ) + 2 * ε) / (9 - 13 * ε)) := by
  have hK2 : (0 : ℝ) ≤ K * (2 : ℝ) ^ ((1 + ε) / 2) :=
    mul_nonneg hK.le (Real.rpow_nonneg (by norm_num) _)
  rw [Real.mul_rpow hK2 (Real.rpow_nonneg hX.le _)]
  congr 1
  rw [show X ^ (((4 : ℝ) + 2 * ε) / (9 - 13 * ε)) = X ^ ((2 + ε) * (2 / (9 - 13 * ε))) by
    rw [show (2 + ε) * (2 / (9 - 13 * ε)) = (4 + 2 * ε) / (9 - 13 * ε) by field_simp; ring]]
  exact (Real.rpow_mul hX.le (2 + ε) (2 / (9 - 13 * ε))).symm

lemma E2_y_nonzero_bound (K : ℝ) (hK : 0 < K) (ε : ℝ) (hε : 0 < ε) (hε2 : ε < 9 / 13)
    (hK_abc : ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
      Nat.Coprime a b → a + b = c →
        (c : ℝ) ≤ K * ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε)) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₁ : ℝ, 0 < X₁ ∧
      ∀ X : ℝ, X₁ < X → ∀ (p : ℕ+ × ℤ), p ∈ E2_set X → p.2 ≠ 0 →
        (p.1 : ℝ) ≤ C * X ^ (((4 : ℝ) + 2 * ε) / (9 - 13 * ε)) := by
  set C := (K * (2 : ℝ) ^ ((1 + ε) / 2)) ^ (2 / (9 - 13 * ε))
  refine ⟨C, by positivity, 1, one_pos, ?_⟩
  intro X hX p hp hy
  have hX_pos : (0 : ℝ) < X := lt_trans one_pos hX
  obtain ⟨hx_gt, hd_pos, hd_le⟩ := hp
  have hpow : (p.1 : ℝ) ^ ((9 - 13 * ε) / 2) ≤
      K * (2 : ℝ) ^ ((1 + ε) / 2) * X ^ (2 + ε) := by
    by_cases hcase : (p.1 : ℤ) ^ 11 ≥ p.2 ^ 2
    · exact abc_case1_bound K hK ε hε hε2 hK_abc p.1 p.2 hy X hX hx_gt hd_pos hd_le hcase
    · push_neg at hcase
      exact abc_case2_bound K hK ε hε hε2 hK_abc p.1 p.2 hy X hX hx_gt hd_pos hd_le hcase
  have h_x_le := rpow_le_of_rpow_le ε hε hε2 _
    (mul_pos (mul_pos hK (Real.rpow_pos_of_pos two_pos _)) (Real.rpow_pos_of_pos hX_pos _))
    _ (by exact_mod_cast PNat.one_le p.1) hpow
  rwa [rpow_product_split K hK ε hε hε2 X hX_pos] at h_x_le

lemma E2_x_bound_core (habc : ABC) (ε : ℝ) (hε : 0 < ε) (hε2 : ε < 9 / 13) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₁ : ℝ, 0 < X₁ ∧
      ∀ X : ℝ, X₁ < X → ∀ (p : ℕ+ × ℤ), p ∈ E2_set X →
        (p.1 : ℝ) ≤ C * X ^ (((4 : ℝ) + 2 * ε) / (9 - 13 * ε)) := by
  obtain ⟨K, hK, hK_abc⟩ := habc ε hε
  obtain ⟨C₁, hC₁, X₁, hX₁, h_nonzero⟩ := E2_y_nonzero_bound K hK ε hε hε2 hK_abc
  refine ⟨max C₁ 1, lt_max_of_lt_right one_pos, max X₁ 1, lt_max_of_lt_right one_pos, ?_⟩
  intro X hX p hp
  have hX1 : 1 < X := lt_of_le_of_lt (le_max_right X₁ 1) hX
  have hXpos : (0 : ℝ) < X := by linarith
  by_cases hy : p.2 = 0
  · calc (p.1 : ℝ) ≤ X ^ (((4 : ℝ) + 2 * ε) / (9 - 13 * ε)) :=
          E2_y_zero_bound ε hε hε2 X hX1 p hp hy
      _ ≤ max C₁ 1 * X ^ (((4 : ℝ) + 2 * ε) / (9 - 13 * ε)) :=
          le_mul_of_one_le_left (Real.rpow_nonneg hXpos.le _) (le_max_right _ _)
  · calc (p.1 : ℝ) ≤ C₁ * X ^ (((4 : ℝ) + 2 * ε) / (9 - 13 * ε)) :=
          h_nonzero X (lt_of_le_of_lt (le_max_left X₁ 1) hX) p hp hy
      _ ≤ max C₁ 1 * X ^ (((4 : ℝ) + 2 * ε) / (9 - 13 * ε)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hXpos.le _)

lemma E2_x_bound (habc : ABC) (η : ℝ) (hη : 0 < η) :
    ∃ Cx : ℝ, 0 < Cx ∧ ∃ X₁ : ℝ, 0 < X₁ ∧
      ∀ X : ℝ, X₁ < X → ∀ (p : ℕ+ × ℤ), p ∈ E2_set X →
        (p.1 : ℝ) ≤ Cx * X ^ ((4 : ℝ) / 9 + η / 2) := by
  obtain ⟨ε, hε, hε2, hexp⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < 9 / 13 ∧
      (4 + 2 * ε) / (9 - 13 * ε) ≤ 4 / 9 + η / 2 := by
    refine ⟨min (η / 100) (1 / 100), by positivity,
      by linarith [min_le_right (η / 100) (1 / 100 : ℝ)], ?_⟩
    rw [div_le_iff₀ (by linarith [min_le_right (η / 100) (1 / 100 : ℝ)])]
    nlinarith [min_le_left (η / 100) (1 / 100 : ℝ), min_le_right (η / 100) (1 / 100 : ℝ),
      sq_nonneg η, sq_nonneg (min (η / 100) (1 / 100 : ℝ)),
      mul_pos hη (show (0 : ℝ) < min (η / 100) (1 / 100) by positivity)]
  obtain ⟨C, hC, X₁, hX₁, hcore⟩ := E2_x_bound_core habc ε hε hε2
  refine ⟨C, hC, max X₁ 1, by positivity, fun X hX p hp => ?_⟩
  have hX₁' : X₁ < X := lt_of_le_of_lt (le_max_left _ _) hX
  have hX1 : 1 ≤ X := le_of_lt (lt_of_le_of_lt (le_max_right X₁ 1) hX)
  calc (p.1 : ℝ) ≤ C * X ^ (((4 : ℝ) + 2 * ε) / (9 - 13 * ε)) := hcore X hX₁' p hp
    _ ≤ C * X ^ ((4 : ℝ) / 9 + η / 2) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX1 hexp) hC.le

lemma E2_set_finite (habc : ABC) (X : ℝ) (_hX : 0 < X) : (E2_set X).Finite := by
  by_cases hX1 : X < 1
  · convert Set.finite_empty
    ext ⟨x, y⟩
    simp only [E2_set, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro ⟨_, h1, h3⟩
    have : (1 : ℝ) ≤ (|(↑↑x : ℤ) ^ 11 - y ^ 2| : ℝ) := by exact_mod_cast h1
    linarith
  · push_neg at hX1
    obtain ⟨Cx, hCx, X₁, hX₁, hx_bound⟩ := E2_x_bound habc 1 one_pos
    set X' := max (X₁ + 1) X with hX'_def
    have hX'_gt : X₁ < X' := lt_max_of_lt_left (by linarith)
    have hX'_ge_X : X ≤ X' := le_max_right _ _
    set B := max (Cx * X' ^ ((4 : ℝ) / 9 + 1 / 2)) (X' ^ ((2 : ℝ) / 11)) with hB_def
    apply Set.Finite.subset (s := ⋃ x ∈ {x : ℕ+ | (x : ℝ) ≤ B},
      (Prod.mk x) '' {y : ℤ | (x, y) ∈ E2_set X})
    · exact Set.Finite.biUnion (pnat_bounded_finite B) (fun x _ => (E2_y_fiber_finite X x).image _)
    · intro ⟨x, y⟩ hxy
      simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq, Prod.mk.injEq]
      refine ⟨x, ?_, y, hxy, rfl, rfl⟩
      simp only [E2_set, Set.mem_setOf_eq] at hxy
      obtain ⟨hgt, h1, h3⟩ := hxy
      by_cases hx_small : (x : ℝ) ≤ X' ^ ((2 : ℝ) / 11)
      · exact le_trans hx_small (le_max_right _ _)
      · push_neg at hx_small
        have hxy' : (⟨x, y⟩ : ℕ+ × ℤ) ∈ E2_set X' :=
          ⟨hx_small, h1, le_trans h3 hX'_ge_X⟩
        exact le_trans (hx_bound X' hX'_gt ⟨x, y⟩ hxy') (le_max_left _ _)
/-! ## k = 1 contribution: injection into E₂ -/

lemma tau_p_sq (R : RamanujanTau) (p : ℕ+) (hp : (p : ℕ).Prime) :
    R.τ (p ^ 2) = R.τ p * R.τ p - (↑(p : ℕ) : ℤ) ^ 11 := by
  have hrec := R.hecke_rec p hp 2 le_rfl
  simp only [show 2 - 1 = 1 from rfl, show 2 - 2 = 0 from rfl, pow_one] at hrec
  rw [show (p : ℕ+) ^ (0 : ℕ) = 1 from pow_zero p, tau_one_eq_one] at hrec
  linarith

lemma p11_not_sq (p : ℕ+) (hp : (p : ℕ).Prime) (a : ℤ) :
    a * a ≠ (↑(p : ℕ) : ℤ) ^ 11 := by
  intro h
  have h_nat : a.natAbs * a.natAbs = (p : ℕ) ^ 11 := by
    have := congr_arg Int.natAbs h
    simpa only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] using this
  have hp' : Prime (p : ℕ) := hp.prime
  have hfin_prod : FiniteMultiplicity (p : ℕ) (a.natAbs * a.natAbs) := by
    rw [h_nat]
    exact FiniteMultiplicity.of_prime_left hp' (pow_ne_zero 11 hp.ne_zero)
  have hfin_a : FiniteMultiplicity (p : ℕ) a.natAbs :=
    ((FiniteMultiplicity.mul_iff hp').mp hfin_prod).1
  have h_lhs := multiplicity_mul hp' hfin_prod
  have h_rhs : multiplicity (p : ℕ) ((p : ℕ) ^ 11) = 11 :=
    multiplicity_pow_self_of_prime hp' 11
  rw [h_nat] at h_lhs
  omega

lemma injection_maps_to_E2 (R : RamanujanTau) (X : ℝ) (p : ℕ+)
    (hp : (p : ℕ).Prime)
    (hpX : (p : ℝ) > X ^ ((2 : ℝ) / 11))
    (habs : (|R.τ (p ^ 2)| : ℝ) ≤ X) :
    (⟨p, R.τ p⟩ : ℕ+ × ℤ) ∈ E2_set X := by
  simp only [E2_set, Set.mem_setOf_eq]
  have key_eq : (↑(p : ℕ) : ℤ) ^ 11 - R.τ p ^ 2 = -(R.τ (p ^ 2)) := by
    rw [tau_p_sq R p hp]
    ring
  exact ⟨hpX,
    by rw [key_eq, abs_neg]
       exact Int.one_le_abs (fun h0 => p11_not_sq p hp (R.τ p)
         (by have := tau_p_sq R p hp; linarith)),
    calc (|((↑(↑(↑p : ℕ) : ℤ) : ℝ) ^ 11 - (↑(R.τ p) : ℝ) ^ 2)| : ℝ)
        = |(↑((↑(p : ℕ) : ℤ) ^ 11 - R.τ p ^ 2 : ℤ) : ℝ)| := by push_cast; ring_nf
      _ = |(↑(-(R.τ (p ^ 2)) : ℤ) : ℝ)| := by rw [key_eq]
      _ = |(↑(R.τ (p ^ 2)) : ℝ)| := by rw [Int.cast_neg]; exact abs_neg _
      _ ≤ X := habs⟩

lemma P_large_mapsTo_E2 (R : RamanujanTau) (X : ℝ) :
    Set.MapsTo (fun p : ℕ+ => (p, R.τ p))
      {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) > X ^ ((2 : ℝ) / 11) ∧
        (|R.τ (p ^ 2)| : ℝ) ≤ X}
      (E2_set X) :=
  fun p ⟨hprime, hgt, hle⟩ => injection_maps_to_E2 R X p hprime hgt hle

lemma target_subset_small_union_large (R : RamanujanTau) (X : ℝ) :
    {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ((ℓ : ℤ) ∈ X2k R 1 ∨ (-(ℓ : ℤ)) ∈ X2k R 1)} ⊆
    {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((2 : ℝ) / 11) ∧
        (R.τ (p ^ 2) = ℓ ∨ R.τ (p ^ 2) = -(ℓ : ℤ))} ∪
    {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      (∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) > X ^ ((2 : ℝ) / 11) ∧
        (R.τ (p ^ 2) = ℓ ∨ R.τ (p ^ 2) = -(ℓ : ℤ))) ∧
      ¬∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((2 : ℝ) / 11) ∧
        (R.τ (p ^ 2) = ℓ ∨ R.τ (p ^ 2) = -(ℓ : ℤ))} := by
  intro ℓ ⟨hprime, hle, hmem⟩
  have hp : ∃ p : ℕ+, (p : ℕ).Prime ∧
      (R.τ (p ^ 2) = (ℓ : ℤ) ∨ R.τ (p ^ 2) = -(ℓ : ℤ)) := by
    rcases hmem with ⟨p, hp, heq⟩ | ⟨p, hp, heq⟩ <;>
      exact ⟨p, hp, by simp_all⟩
  by_cases hsmall : ∃ q : ℕ+, (q : ℕ).Prime ∧ (q : ℝ) ≤ X ^ ((2 : ℝ) / 11) ∧
      (R.τ (q ^ 2) = (ℓ : ℤ) ∨ R.τ (q ^ 2) = -(ℓ : ℤ))
  · exact Set.mem_union_left _ ⟨hprime, hle, hsmall⟩
  · obtain ⟨p, hpprime, htau⟩ := hp
    have hplarge : (p : ℝ) > X ^ ((2 : ℝ) / 11) := by
      by_contra h
      push_neg at h
      exact hsmall ⟨p, hpprime, h, htau⟩
    exact Set.mem_union_right _ ⟨hprime, hle, ⟨p, hpprime, hplarge, htau⟩, hsmall⟩

lemma nats_le_X_finite (X : ℝ) : {ℓ : ℕ | (ℓ : ℝ) ≤ X}.Finite := by
  apply (Set.finite_Iic ⌈X⌉₊).subset
  intro n (hn : (n : ℝ) ≤ X)
  simp only [Set.mem_Iic]
  calc (n : ℕ) = ⌈(n : ℝ)⌉₊ := (Nat.ceil_natCast n).symm
    _ ≤ ⌈X⌉₊ := Nat.ceil_le_ceil hn

lemma T_small_subset_image (R : RamanujanTau) (X : ℝ) :
    {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((2 : ℝ) / 11) ∧
        (R.τ (p ^ 2) = ℓ ∨ R.τ (p ^ 2) = -(ℓ : ℤ))} ⊆
    (fun p : ℕ+ => (R.τ (p ^ 2)).natAbs) ''
      {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((2 : ℝ) / 11)} := by
  intro ℓ ⟨_, _, p, hp_prime, hp_le, htau⟩
  exact ⟨p, ⟨hp_prime, hp_le⟩, by cases htau with | inl h => simp [h] | inr h => simp [h]⟩

lemma small_witness_bound (R : RamanujanTau) (X : ℝ) :
    {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((2 : ℝ) / 11) ∧
        (R.τ (p ^ 2) = ℓ ∨ R.τ (p ^ 2) = -(ℓ : ℤ))}.ncard ≤
    {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((2 : ℝ) / 11)}.ncard := by
  have hfin : {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((2 : ℝ) / 11)}.Finite :=
    Set.Finite.subset ((Set.finite_Iic _).preimage PNat.coe_injective.injOn)
      fun p ⟨_, hp⟩ => Nat.cast_le.mp (hp.trans (Nat.le_ceil _))
  calc {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((2 : ℝ) / 11) ∧
        (R.τ (p ^ 2) = ℓ ∨ R.τ (p ^ 2) = -(ℓ : ℤ))}.ncard
      ≤ ((fun p : ℕ+ => (R.τ (p ^ 2)).natAbs) ''
          {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((2 : ℝ) / 11)}).ncard :=
        Set.ncard_le_ncard (T_small_subset_image R X) (hfin.image _)
    _ ≤ {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((2 : ℝ) / 11)}.ncard :=
        Set.ncard_image_le hfin

lemma abs_tau_eq_of_pm (τval : ℤ) (ℓ : ℕ) (h : τval = ↑ℓ ∨ τval = -(↑ℓ : ℤ)) :
    (|τval| : ℝ) = (ℓ : ℝ) := by
  rcases h with rfl | rfl <;> simp

lemma nat_eq_of_pm_eq (ℓ₁ ℓ₂ : ℕ) (hℓ₁ : Nat.Prime ℓ₁) (τval : ℤ)
    (h₁ : τval = ↑ℓ₁ ∨ τval = -(↑ℓ₁ : ℤ))
    (h₂ : τval = ↑ℓ₂ ∨ τval = -(↑ℓ₂ : ℤ)) : ℓ₁ = ℓ₂ := by
  have hpos := Int.natCast_pos.mpr hℓ₁.pos
  rcases h₁ with rfl | rfl <;> rcases h₂ with h₂ | h₂ <;>
    first | exact Nat.cast_injective h₂ | exact Nat.cast_injective (neg_inj.mp h₂) | omega

lemma large_witness_bound (R : RamanujanTau) (X : ℝ)
    (hfin : {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) > X ^ ((2 : ℝ) / 11) ∧
      (|R.τ (p ^ 2)| : ℝ) ≤ X}.Finite) :
    {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      (∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) > X ^ ((2 : ℝ) / 11) ∧
        (R.τ (p ^ 2) = ℓ ∨ R.τ (p ^ 2) = -(ℓ : ℤ))) ∧
      ¬∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((2 : ℝ) / 11) ∧
        (R.τ (p ^ 2) = ℓ ∨ R.τ (p ^ 2) = -(ℓ : ℤ))}.ncard ≤
    {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) > X ^ ((2 : ℝ) / 11) ∧
      (|R.τ (p ^ 2)| : ℝ) ≤ X}.ncard := by
  let g : ℕ → ℕ+ := fun ℓ =>
    if h : ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) > X ^ ((2 : ℝ) / 11) ∧
      (R.τ (p ^ 2) = ℓ ∨ R.τ (p ^ 2) = -(ℓ : ℤ))
    then Classical.choose h
    else 1
  refine Set.ncard_le_ncard_of_injOn g ?_ ?_ hfin
  · intro ℓ ⟨_, hle, ⟨p, hp_prime, hp_big, hp_val⟩, _⟩
    have hex : ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) > X ^ ((2 : ℝ) / 11) ∧
      (R.τ (p ^ 2) = ℓ ∨ R.τ (p ^ 2) = -(ℓ : ℤ)) := ⟨p, hp_prime, hp_big, hp_val⟩
    rw [show g ℓ = Classical.choose hex from dif_pos hex]
    exact ⟨(Classical.choose_spec hex).1, (Classical.choose_spec hex).2.1, by
      rw [abs_tau_eq_of_pm _ ℓ (Classical.choose_spec hex).2.2]
      exact_mod_cast hle⟩
  · intro ℓ₁ hℓ₁ ℓ₂ hℓ₂ hgeq
    obtain ⟨hprime₁, _, ⟨p₁, hp₁_prime, hp₁_big, hp₁_val⟩, _⟩ := hℓ₁
    obtain ⟨_, _, ⟨p₂, hp₂_prime, hp₂_big, hp₂_val⟩, _⟩ := hℓ₂
    have hex₁ : ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) > X ^ ((2 : ℝ) / 11) ∧
      (R.τ (p ^ 2) = ℓ₁ ∨ R.τ (p ^ 2) = -(ℓ₁ : ℤ)) := ⟨p₁, hp₁_prime, hp₁_big, hp₁_val⟩
    have hex₂ : ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) > X ^ ((2 : ℝ) / 11) ∧
      (R.τ (p ^ 2) = ℓ₂ ∨ R.τ (p ^ 2) = -(ℓ₂ : ℤ)) := ⟨p₂, hp₂_prime, hp₂_big, hp₂_val⟩
    rw [show g ℓ₁ = Classical.choose hex₁ from dif_pos hex₁,
      show g ℓ₂ = Classical.choose hex₂ from dif_pos hex₂] at hgeq
    have hval₁ := (Classical.choose_spec hex₁).2.2
    rw [hgeq] at hval₁
    exact nat_eq_of_pm_eq ℓ₁ ℓ₂ hprime₁ _ hval₁ (Classical.choose_spec hex₂).2.2

lemma k1_ncard_le_small_plus_large (habc : ABC) (R : RamanujanTau) (X : ℝ) (hX : 1 < X) :
    ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ((ℓ : ℤ) ∈ X2k R 1 ∨ (-(ℓ : ℤ)) ∈ X2k R 1)}.ncard : ℝ) ≤
    ({p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((2 : ℝ) / 11)}.ncard : ℝ) +
    ({p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) > X ^ ((2 : ℝ) / 11) ∧
      (|R.τ (p ^ 2)| : ℝ) ≤ X}.ncard : ℝ) := by
  have hPfin : {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) > X ^ ((2 : ℝ) / 11) ∧
      (|R.τ (p ^ 2)| : ℝ) ≤ X}.Finite :=
    Set.Finite.of_injOn (f := fun p : ℕ+ => (p, R.τ p))
      (P_large_mapsTo_E2 R X) (fun _ _ _ _ h => (Prod.mk.inj h).1)
      (E2_set_finite habc X (by linarith))
  have h5 := le_trans
    (Set.ncard_le_ncard (target_subset_small_union_large R X)
      (((nats_le_X_finite X).subset fun ℓ hℓ => hℓ.2.1).union
        ((nats_le_X_finite X).subset fun ℓ hℓ => hℓ.2.1)))
    (Set.ncard_union_le _ _)
  exact_mod_cast le_trans h5 (Nat.add_le_add (small_witness_bound R X)
    (large_witness_bound R X hPfin))

lemma ncard_pnat_le (N : ℕ) :
    {p : ℕ+ | (p : ℕ) ≤ N}.ncard ≤ N := by
  apply le_trans (Set.ncard_le_ncard_of_injOn
    (fun p : ℕ+ => (p : ℕ) - 1)
    (s := {p : ℕ+ | (p : ℕ) ≤ N}) (t := ↑(Finset.range N))
    (fun p hp => by
      simp only [Set.mem_setOf_eq] at hp
      simp only [Finset.coe_range, Set.mem_Iio]
      have := p.pos; omega)
    (fun p₁ _ p₂ _ h => by
      apply PNat.eq
      show (p₁ : ℕ) = (p₂ : ℕ)
      have h1 := p₁.pos
      have h2 := p₂.pos
      have : (p₁ : ℕ) - 1 = (p₂ : ℕ) - 1 := h
      omega)
    (Set.toFinite _))
  rw [Set.ncard_coe_finset, Finset.card_range]

lemma small_primes_bound (X : ℝ) (hX : 1 < X) :
    ({p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((2 : ℝ) / 11)}.ncard : ℝ) ≤
    X ^ ((13 : ℝ) / 22) := by
  set Y := X ^ ((2 : ℝ) / 11) with hY_def
  have h_ncard_le : {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) ≤ Y}.ncard ≤ ⌊Y⌋₊ :=
    le_trans (Set.ncard_le_ncard (fun p ⟨_, hp⟩ => Nat.le_floor hp)
      (show {p : ℕ+ | (p : ℕ) ≤ ⌊Y⌋₊}.Finite by
        rw [show {p : ℕ+ | (p : ℕ) ≤ ⌊Y⌋₊} = PNat.val ⁻¹' {n : ℕ | n ≤ ⌊Y⌋₊} by ext p; simp]
        exact (Set.finite_le_nat _).preimage (fun a _ b _ h => PNat.eq h))) (ncard_pnat_le _)
  calc (({p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) ≤ Y}.ncard : ℝ))
      ≤ (⌊Y⌋₊ : ℝ) := by exact_mod_cast h_ncard_le
    _ ≤ Y := Nat.floor_le (by positivity)
    _ ≤ X ^ ((13 : ℝ) / 22) :=
        Real.rpow_le_rpow_of_exponent_le (le_of_lt hX) (by norm_num)

lemma k1_contribution_bound (habc : ABC) (R : RamanujanTau) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ X₁ : ℝ, 0 < X₁ ∧
      ∀ X : ℝ, X₁ < X →
        ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
          ((ℓ : ℤ) ∈ X2k R 1 ∨ (-(ℓ : ℤ)) ∈ X2k R 1)}.ncard : ℝ) ≤
        C₁ * X ^ ((13 : ℝ) / 22) + (E2 X : ℝ) := by
  refine ⟨1, one_pos, 1, one_pos, fun X hX => ?_⟩
  have hX1 : (1 : ℝ) < X := by linarith
  have large_primes : ({p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) > X ^ ((2 : ℝ) / 11) ∧
      (|R.τ (p ^ 2)| : ℝ) ≤ X}.ncard : ℝ) ≤ (E2 X : ℝ) :=
    Nat.cast_le.mpr (Set.ncard_le_ncard_of_injOn (fun p : ℕ+ => (⟨p, R.τ p⟩ : ℕ+ × ℤ))
      (fun p hp => injection_maps_to_E2 R X p hp.1 hp.2.1 hp.2.2)
      (fun p₁ _ p₂ _ h => (Prod.mk.inj h).1) (E2_set_finite habc X (by linarith)))
  linarith [k1_ncard_le_small_plus_large habc R X hX1, small_primes_bound X hX1, large_primes]
/-! ## ABC-based bounds for E₄ -/

lemma gcd_normalized_product_dvd (a b : ℕ) (ha : 0 < a) (_hb : 0 < b) :
    (a / Nat.gcd a b) * (b / Nat.gcd a b) * ((a + b) / Nat.gcd a b) ∣
    a * b * (a + b) := by
  set g := a.gcd b with hg_def
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left b ha
  have hga : g ∣ a := Nat.gcd_dvd_left a b
  have hgb : g ∣ b := Nat.gcd_dvd_right a b
  have hgab : g ∣ (a + b) := dvd_add hga hgb
  set a' := a / g
  set b' := b / g
  set c' := (a + b) / g
  have ha' : a = a' * g := (Nat.div_mul_cancel hga).symm
  have hb' : b = b' * g := (Nat.div_mul_cancel hgb).symm
  have hab' : a + b = c' * g := (Nat.div_mul_cancel hgab).symm
  refine ⟨g ^ 3, ?_⟩
  conv_lhs => rw [show a * b * (a + b) = (a' * g) * (b' * g) * (c' * g) by rw [← ha', ← hb', ← hab']]
  ring

lemma coprime_triple_exists (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ∃ a' b' c' : ℕ, 0 < a' ∧ 0 < b' ∧ 0 < c' ∧
      Nat.Coprime a' b' ∧ a' + b' = c' ∧
      (Nat.radical (a' * b' * c') ≤ Nat.radical (a * b * (a + b))) ∧
      a + b ≤ c' * Nat.gcd a b := by
  have hg_pos : 0 < a.gcd b := Nat.gcd_pos_of_pos_left b ha
  have hga : a.gcd b ∣ a := Nat.gcd_dvd_left a b
  have hgb : a.gcd b ∣ b := Nat.gcd_dvd_right a b
  have hgab : a.gcd b ∣ (a + b) := dvd_add hga hgb
  refine ⟨a / a.gcd b, b / a.gcd b, (a + b) / a.gcd b,
    Nat.div_pos (Nat.le_of_dvd ha hga) hg_pos,
    Nat.div_pos (Nat.le_of_dvd hb hgb) hg_pos,
    Nat.div_pos (Nat.le_of_dvd (by omega) hgab) hg_pos,
    Nat.coprime_div_gcd_div_gcd hg_pos,
    (Nat.add_div_of_dvd_left hgb).symm, ?_, ?_⟩
  · have hdvd := gcd_normalized_product_dvd a b ha hb
    have hne1 : a / a.gcd b * (b / a.gcd b) * ((a + b) / a.gcd b) ≠ 0 :=
      Nat.pos_iff_ne_zero.mp (Nat.mul_pos (Nat.mul_pos
        (Nat.div_pos (Nat.le_of_dvd ha hga) hg_pos)
        (Nat.div_pos (Nat.le_of_dvd hb hgb) hg_pos))
        (Nat.div_pos (Nat.le_of_dvd (by omega) hgab) hg_pos))
    have hne2 : a * b * (a + b) ≠ 0 := by positivity
    simp only [Nat.radical, hne1, hne2, ite_false]
    exact Finset.prod_le_prod_of_subset_of_one_le'
      (Nat.primeFactors_mono hdvd (by omega))
      (fun p hp _ => Nat.Prime.one_le (Nat.prime_of_mem_primeFactors hp))
  · exact le_of_eq (Nat.div_mul_cancel hgab).symm

lemma prod_union_le {ι : Type*} [DecidableEq ι] (s₁ s₂ : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s₁ ∪ s₂, 1 ≤ f i) :
    ∏ i ∈ s₁ ∪ s₂, f i ≤ (∏ i ∈ s₁, f i) * (∏ i ∈ s₂, f i) := by
  have h := @Finset.prod_union_inter ι ℕ s₁ s₂ _ (fun i => f i) _
  have hinter : 1 ≤ ∏ i ∈ s₁ ∩ s₂, f i :=
    Finset.one_le_prod' fun i hi => hf i (Finset.mem_union.mpr (Or.inl (Finset.mem_of_mem_inter_left hi)))
  calc ∏ i ∈ s₁ ∪ s₂, f i
      _ ≤ (∏ i ∈ s₁ ∪ s₂, f i) * (∏ i ∈ s₁ ∩ s₂, f i) := le_mul_of_one_le_right' hinter
      _ = (∏ i ∈ s₁, f i) * (∏ i ∈ s₂, f i) := h

lemma radical_product_le (a b c : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    Nat.radical (a * b * c) ≤ Nat.radical a * Nat.radical b * Nat.radical c := by
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  simp only [Nat.radical, ha, hb, hc, mul_ne_zero hab hc, ite_false]
  rw [Nat.primeFactors_mul hab hc, Nat.primeFactors_mul ha hb]
  have hprime_ge_one : ∀ i ∈ a.primeFactors ∪ b.primeFactors ∪ c.primeFactors, 1 ≤ i := by
    intro i hi
    simp only [Finset.mem_union] at hi
    rcases hi with ((hi | hi) | hi) <;> exact (Nat.mem_primeFactors.mp hi).1.one_le
  calc ∏ i ∈ a.primeFactors ∪ b.primeFactors ∪ c.primeFactors, i
      _ ≤ (∏ i ∈ a.primeFactors ∪ b.primeFactors, i) * (∏ i ∈ c.primeFactors, i) :=
          prod_union_le _ _ _ hprime_ge_one
      _ ≤ ((∏ i ∈ a.primeFactors, i) * (∏ i ∈ b.primeFactors, i)) * (∏ i ∈ c.primeFactors, i) :=
          Nat.mul_le_mul_right _ (prod_union_le _ _ _ (fun i hi => by
            rcases Finset.mem_union.mp hi with hi | hi <;>
              exact (Nat.mem_primeFactors.mp hi).1.one_le))
      _ = (∏ i ∈ a.primeFactors, i) * (∏ i ∈ b.primeFactors, i) * (∏ i ∈ c.primeFactors, i) := by ring

lemma radical_pow_eq (n k : ℕ) (hk : 0 < k) :
    Nat.radical (n ^ k) = Nat.radical n := by
  by_cases hn : n = 0
  · subst hn
    simp [Nat.radical, zero_pow (by omega : k ≠ 0)]
  · simp only [Nat.radical, if_neg hn, if_neg (pow_ne_zero k hn)]
    congr 1
    exact Nat.primeFactors_pow n (by omega)

abbrev dv (x : ℕ+) (u : ℤ) : ℤ := u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22

lemma u_sq_lt_six_x22
    (x : ℕ+) (u : ℤ) (X : ℝ)
    (hX : 4 < X)
    (hx_large : (x : ℝ) > X ^ ((1 : ℝ) / 11))
    (hd_bound : (|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22| : ℝ) ≤ 4 * X) :
    (u : ℤ) ^ 2 < 6 * (↑(x : ℕ) : ℤ) ^ 22 := by
  have hx_pos : (0 : ℝ) < (↑(x : ℕ) : ℝ) := by positivity
  have hx22_gt_X2 : (↑(x : ℕ) : ℝ) ^ 22 > X ^ 2 := by
    have hx11 : (↑(x : ℕ) : ℝ) ^ 11 > X := by
      calc (↑(x : ℕ) : ℝ) ^ 11 > (X ^ ((1 : ℝ) / 11)) ^ 11 :=
            pow_lt_pow_left₀ hx_large (by positivity) (by omega)
        _ = X := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
          norm_num
    nlinarith [sq_nonneg ((↑(x : ℕ) : ℝ) ^ 11)]
  have h4X_lt : 4 * X < (↑(x : ℕ) : ℝ) ^ 22 := by nlinarith
  have hu_upper : (u : ℝ) ^ 2 ≤ 5 * (↑(x : ℕ) : ℝ) ^ 22 + 4 * X := by
    have := le_abs_self (u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22 : ℝ)
    push_cast at this hd_bound ⊢
    linarith
  exact_mod_cast show (u : ℝ) ^ 2 < 6 * (↑(x : ℕ) : ℝ) ^ 22 by linarith

lemma radical_five_mul_pow22_le (n : ℕ) (hn : 0 < n) :
    Nat.radical (5 * n ^ 22) ≤ 5 * n := by
  have hfact : (5 * n ^ 22).primeFactors = (5 * n).primeFactors := by
    rw [Nat.primeFactors_mul (by omega) (by positivity),
        Nat.primeFactors_mul (by omega) (by omega),
        Nat.primeFactors_pow n (by omega : (22 : ℕ) ≠ 0)]
  rw [show Nat.radical (5 * n ^ 22) = Nat.radical (5 * n) by
    simp only [Nat.radical, if_neg (by positivity : 5 * n ^ 22 ≠ 0), if_neg (by omega : 5 * n ≠ 0)]
    rw [hfact]]
  exact radical_le (5 * n) (by omega)

lemma construct_triple_pos
    (x : ℕ+) (u : ℤ)
    (hu_ne : u ≠ 0)
    (hd : 0 < dv x u)
    (_hu2 : u ^ 2 < 6 * (↑(x : ℕ) : ℤ) ^ 22) :
    ∃ a₀ b₀ : ℕ, 0 < a₀ ∧ 0 < b₀ ∧
      5 * (x : ℕ) ^ 22 ≤ a₀ + b₀ ∧
      Nat.gcd a₀ b₀ ≤ (|dv x u|).natAbs ∧
      Nat.radical (a₀ * b₀ * (a₀ + b₀)) ≤
        5 * (x : ℕ) * (|dv x u|).natAbs * u.natAbs := by
  have hx_pos : 0 < (x : ℕ) := x.pos
  have hdna : 0 < (dv x u).natAbs := Int.natAbs_pos.mpr (ne_of_gt hd)
  have habs : (|dv x u|).natAbs = (dv x u).natAbs := by simp [abs_of_pos hd]
  have hsum : 5 * (x : ℕ) ^ 22 + (dv x u).natAbs = u.natAbs ^ 2 := by
    exact_mod_cast show (5 * (↑(x : ℕ) : ℤ) ^ 22 + ↑(dv x u).natAbs : ℤ) = ↑u.natAbs ^ 2 by
      rw [Int.natCast_natAbs, abs_of_pos hd, Int.natAbs_sq]
      unfold dv
      ring
  refine ⟨5 * (x : ℕ) ^ 22, (dv x u).natAbs, by positivity, hdna, ?_, ?_, ?_⟩
  · omega
  · rw [habs]
    exact Nat.le_of_dvd hdna (Nat.gcd_dvd_right _ _)
  · rw [hsum]
    calc Nat.radical (5 * (x : ℕ) ^ 22 * (dv x u).natAbs * (u.natAbs ^ 2))
        ≤ Nat.radical (5 * (x : ℕ) ^ 22) * Nat.radical (dv x u).natAbs *
          Nat.radical (u.natAbs ^ 2) :=
          radical_product_le _ _ _ (by positivity) (by omega) (by positivity)
      _ ≤ (5 * (x : ℕ)) * (dv x u).natAbs * u.natAbs := by
          apply Nat.mul_le_mul (Nat.mul_le_mul _ _) _
          · exact radical_five_mul_pow22_le _ hx_pos
          · exact radical_le _ (by omega)
          · rw [radical_pow_eq _ 2 (by omega)]
            exact radical_le _ (by omega)
      _ = 5 * (x : ℕ) * (|dv x u|).natAbs * u.natAbs := by rw [habs]

lemma construct_triple_neg
    (x : ℕ+) (u : ℤ)
    (hu_ne : u ≠ 0)
    (hd : dv x u < 0)
    (_hu2 : u ^ 2 < 6 * (↑(x : ℕ) : ℤ) ^ 22) :
    ∃ a₀ b₀ : ℕ, 0 < a₀ ∧ 0 < b₀ ∧
      5 * (x : ℕ) ^ 22 ≤ a₀ + b₀ ∧
      Nat.gcd a₀ b₀ ≤ (|dv x u|).natAbs ∧
      Nat.radical (a₀ * b₀ * (a₀ + b₀)) ≤
        5 * (x : ℕ) * (|dv x u|).natAbs * u.natAbs := by
  have hx_pos : 0 < (x : ℕ) := x.pos
  have hdna : 0 < (dv x u).natAbs := Int.natAbs_pos.mpr (ne_of_lt hd)
  have habs : (|dv x u|).natAbs = (dv x u).natAbs := Int.natAbs_abs _
  have hsum : u.natAbs ^ 2 + (dv x u).natAbs = 5 * (x : ℕ) ^ 22 := by
    exact_mod_cast show (↑u.natAbs ^ 2 + ↑(dv x u).natAbs : ℤ) = 5 * (↑(x : ℕ) : ℤ) ^ 22 by
      rw [Int.natAbs_sq, Int.natCast_natAbs, abs_of_nonpos (le_of_lt hd)]
      unfold dv
      ring
  refine ⟨u.natAbs ^ 2, (dv x u).natAbs, by positivity, hdna, ?_, ?_, ?_⟩
  · omega
  · rw [habs]
    exact Nat.le_of_dvd hdna (Nat.gcd_dvd_right _ _)
  · rw [hsum]
    calc Nat.radical (u.natAbs ^ 2 * (dv x u).natAbs * (5 * (x : ℕ) ^ 22))
        ≤ Nat.radical (u.natAbs ^ 2) * Nat.radical (dv x u).natAbs *
          Nat.radical (5 * (x : ℕ) ^ 22) :=
          radical_product_le _ _ _ (by positivity) (by omega) (by positivity)
      _ ≤ u.natAbs * (dv x u).natAbs * (5 * (x : ℕ)) := by
          apply Nat.mul_le_mul (Nat.mul_le_mul _ _) _
          · rw [radical_pow_eq _ 2 (by omega)]
            exact radical_le _ (by omega)
          · exact radical_le _ (by omega)
          · exact radical_five_mul_pow22_le _ hx_pos
      _ = 5 * (x : ℕ) * (|dv x u|).natAbs * u.natAbs := by rw [habs]; ring

lemma construct_triple
    (x : ℕ+) (u : ℤ)
    (hu_ne : u ≠ 0)
    (hd_pos : 1 ≤ |u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22|)
    (hu2 : u ^ 2 < 6 * (↑(x : ℕ) : ℤ) ^ 22) :
    ∃ a₀ b₀ : ℕ, 0 < a₀ ∧ 0 < b₀ ∧
      5 * (x : ℕ) ^ 22 ≤ a₀ + b₀ ∧
      Nat.gcd a₀ b₀ ≤ (|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22|).natAbs ∧
      Nat.radical (a₀ * b₀ * (a₀ + b₀)) ≤
        5 * (x : ℕ) * (|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22|).natAbs * u.natAbs := by
  by_cases hd : 0 < dv x u
  · exact construct_triple_pos x u hu_ne hd hu2
  · exact construct_triple_neg x u hu_ne (by
      push_neg at hd
      rcases eq_or_lt_of_le hd with h | h
      · exfalso
        unfold dv at h
        simp [h] at hd_pos
      · exact h) hu2

lemma u_ne_zero_of_bounds
    (x : ℕ+) (u : ℤ) (X : ℝ)
    (hX : 4 < X)
    (hx_large : (x : ℝ) > X ^ ((1 : ℝ) / 11))
    (hd_bound : (|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22| : ℝ) ≤ 4 * X) :
    u ≠ 0 := by
  intro hu
  subst hu
  have h5x22 : (5 * (x : ℝ) ^ 22 : ℝ) ≤ 4 * X := by
    calc 5 * (x : ℝ) ^ 22
        = -(((0 : ℤ) ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22 : ℤ) : ℝ) := by push_cast; ring
      _ ≤ (|(0 : ℤ) ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22| : ℝ) := by exact_mod_cast neg_le_abs _
      _ ≤ 4 * X := hd_bound
  have hX_pos : (0 : ℝ) < X := by linarith
  have hx22 : (x : ℝ) ^ 22 > X ^ 2 := by
    have := pow_lt_pow_left₀ hx_large (by positivity : (0 : ℝ) ≤ X ^ ((1 : ℝ) / 11)) (by norm_num : 22 ≠ 0)
    linarith [show (X ^ ((1 : ℝ) / 11)) ^ (22 : ℕ) = X ^ (2 : ℕ) by
      rw [← Real.rpow_natCast (X ^ ((1 : ℝ) / 11)) 22, ← Real.rpow_mul hX_pos.le]; norm_num]
  nlinarith [sq_nonneg X]

lemma abc_bound_c'
    (K : ℝ) (hK : 0 < K) (ε : ℝ) (_hε : 0 < ε)
    (hABC_K : ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
        Nat.Coprime a b → a + b = c →
          (c : ℝ) ≤ K * ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε))
    (a' b' c' : ℕ) (ha' : 0 < a') (hb' : 0 < b') (hc' : 0 < c')
    (hcop : Nat.Coprime a' b') (hsum : a' + b' = c')
    (R_bound : ℕ) (hrad : Nat.radical (a' * b' * c') ≤ R_bound) :
    (c' : ℝ) ≤ K * (R_bound : ℝ) ^ (1 + ε) :=
  le_trans (hABC_K a' b' c' ha' hb' hc' hcop hsum)
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hrad) (by linarith)) hK.le)

lemma combine_bounds
    (x : ℕ+) (u : ℤ) (X : ℝ)
    (_hX : 4 < X)
    (hd_bound : (|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22| : ℝ) ≤ 4 * X)
    (hu_lt : (u.natAbs : ℝ) < Real.sqrt 6 * (x : ℝ) ^ 11) :
    (5 * (x : ℕ) * (|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22|).natAbs * u.natAbs : ℝ) ≤
      20 * Real.sqrt 6 * X * (x : ℝ) ^ (12 : ℝ) := by
  have natabs_d : ((|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22|).natAbs : ℝ) =
      |((u : ℝ) ^ 2 - 5 * (x : ℝ) ^ 22)| := by
    rw [Int.natAbs_abs, Nat.cast_natAbs]
    push_cast
    ring_nf
  have natabs_u : (u.natAbs : ℝ) = |(u : ℝ)| := by
    rw [Nat.cast_natAbs]
    push_cast
    ring_nf
  rw [natabs_d, natabs_u]
  rw [natabs_u] at hu_lt
  rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hd2 : |((u : ℝ) ^ 2 - 5 * (x : ℝ) ^ 22)| ≤ 4 * X := by
    rw [show ((u : ℤ) : ℝ) ^ 2 - 5 * ((x : ℕ) : ℝ) ^ 22 =
        ((u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22 : ℤ) : ℝ) from by push_cast; ring]
    exact_mod_cast hd_bound
  calc 5 * (x : ℝ) * |((u : ℝ) ^ 2 - 5 * (x : ℝ) ^ 22)| * |(u : ℝ)|
      ≤ 5 * (x : ℝ) * (4 * X) * (Real.sqrt 6 * (x : ℝ) ^ 11) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hd2 (by positivity)) hu_lt.le
          (abs_nonneg _) (by positivity)
    _ = 20 * Real.sqrt 6 * X * (x : ℝ) ^ 12 := by ring

lemma u_abs_lt_sqrt6_mul_x11
    (x : ℕ+) (u : ℤ)
    (hu2 : u ^ 2 < 6 * (↑(x : ℕ) : ℤ) ^ 22) :
    (u.natAbs : ℝ) < Real.sqrt 6 * (x : ℝ) ^ 11 := by
  rw [Nat.cast_natAbs]
  push_cast
  apply abs_lt_of_sq_lt_sq
  · rw [mul_pow, Real.sq_sqrt (by norm_num : (6:ℝ) ≥ 0), ← pow_mul]
    exact_mod_cast hu2
  · positivity

lemma abc_core_combine
    (K : ℝ) (hK : 0 < K) (ε : ℝ) (hε : 0 < ε)
    (hABC_K : ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
        Nat.Coprime a b → a + b = c →
          (c : ℝ) ≤ K * ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε))
    (x : ℕ+) (u : ℤ) (X : ℝ)
    (hX : 4 < X)
    (_hd_pos : 1 ≤ |u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22|)
    (hd_bound : (|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22| : ℝ) ≤ 4 * X)
    (hu2 : u ^ 2 < 6 * (↑(x : ℕ) : ℤ) ^ 22)
    (_hu_ne : u ≠ 0)
    (a₀ b₀ : ℕ) (ha₀ : 0 < a₀) (hb₀ : 0 < b₀)
    (hsum : 5 * (x : ℕ) ^ 22 ≤ a₀ + b₀)
    (hgcd : Nat.gcd a₀ b₀ ≤ (|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22|).natAbs)
    (hrad : Nat.radical (a₀ * b₀ * (a₀ + b₀)) ≤
        5 * (x : ℕ) * (|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22|).natAbs * u.natAbs) :
    5 * (x : ℝ) ^ (22 : ℝ) ≤ 4 * X * K * (20 * Real.sqrt 6 * X * (x : ℝ) ^ (12 : ℝ)) ^ (1 + ε) := by
  obtain ⟨a', b', c', ha', hb', hc', hcop, hsum_abc, hrad_le, hab_le_cg⟩ :=
    coprime_triple_exists a₀ b₀ ha₀ hb₀
  have hc'_raw := abc_bound_c' K hK ε hε hABC_K a' b' c' ha' hb' hc' hcop hsum_abc
      (5 * (x : ℕ) * (|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22|).natAbs * u.natAbs)
      (le_trans hrad_le hrad)
  set R' := (5 * (x : ℕ) * (|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22|).natAbs * u.natAbs : ℕ)
  set T := 20 * Real.sqrt 6 * X * (x : ℝ) ^ (12 : ℝ)
  have hRT : (R' : ℝ) ≤ T := by
    push_cast [R']
    exact combine_bounds x u X hX hd_bound (u_abs_lt_sqrt6_mul_x11 x u hu2)
  have hc'_final : (c' : ℝ) ≤ K * T ^ (1 + ε) :=
    le_trans hc'_raw (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg R') hRT (by linarith)) hK.le)
  have hg_pos : 0 < Nat.gcd a₀ b₀ := Nat.pos_of_ne_zero (by
    intro h; simp [Nat.gcd_eq_zero_iff] at h; omega)
  have hg_real_le : (Nat.gcd a₀ b₀ : ℝ) ≤ 4 * X := by
    calc (Nat.gcd a₀ b₀ : ℝ) ≤ ((|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22|).natAbs : ℝ) := by
            exact_mod_cast hgcd
      _ = (|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22| : ℝ) := by
            simp [Int.natAbs_abs, Nat.cast_natAbs]
      _ ≤ 4 * X := hd_bound
  calc 5 * (x : ℝ) ^ (22 : ℝ) = 5 * ((x : ℕ) : ℝ) ^ (22 : ℕ) := by norm_cast
    _ ≤ (c' : ℝ) * (Nat.gcd a₀ b₀ : ℝ) := by exact_mod_cast le_trans hsum hab_le_cg
    _ ≤ K * T ^ (1 + ε) * (4 * X) := by nlinarith
    _ = 4 * X * K * T ^ (1 + ε) := by ring

lemma real_rearrange
    (K : ℝ) (_hK : 0 < K) (ε : ℝ) (_hε : 0 < ε) (_hε2 : (10 : ℝ) - 12 * ε > 0)
    (x : ℝ) (hx : 0 < x) (X : ℝ) (hXpos : 0 < X)
    (h : 5 * x ^ (22 : ℝ) ≤ 4 * X * K * (20 * Real.sqrt 6 * X * x ^ (12 : ℝ)) ^ (1 + ε)) :
    x ^ (10 - 12 * ε) ≤
      (4 * K / 5 * (20 * Real.sqrt 6) ^ (1 + ε)) * X ^ (2 + ε) := by
  have _hx12e : (0 : ℝ) < x ^ (12 + 12 * ε) := Real.rpow_pos_of_pos hx _
  have hx_combine : x ^ (10 - 12 * ε) * x ^ (12 + 12 * ε) = x ^ (22 : ℝ) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have hexp : (20 * Real.sqrt 6 * X * x ^ (12 : ℝ)) ^ (1 + ε) =
      (20 * Real.sqrt 6) ^ (1 + ε) * X ^ (1 + ε) * x ^ (12 + 12 * ε) := by
    rw [show 20 * Real.sqrt 6 * X * x ^ (12 : ℝ) = (20 * Real.sqrt 6) * X * x ^ (12 : ℝ) by ring, Real.mul_rpow (by positivity : (0:ℝ) ≤ (20 * Real.sqrt 6) * X) (by positivity), Real.mul_rpow (by positivity : (0:ℝ) ≤ 20 * Real.sqrt 6) (by positivity), ← Real.rpow_mul (le_of_lt hx)]
    ring_nf
  rw [hexp] at h
  have h2 : 5 * x ^ (22 : ℝ) ≤
      4 * K * (20 * Real.sqrt 6) ^ (1 + ε) * X ^ (2 + ε) * x ^ (12 + 12 * ε) := by
    calc 5 * x ^ (22 : ℝ)
        ≤ 4 * X * K * ((20 * Real.sqrt 6) ^ (1 + ε) * X ^ (1 + ε) * x ^ (12 + 12 * ε)) := h
      _ = 4 * K * (20 * Real.sqrt 6) ^ (1 + ε) * (X * X ^ (1 + ε)) * x ^ (12 + 12 * ε) := by ring
      _ = 4 * K * (20 * Real.sqrt 6) ^ (1 + ε) * X ^ (2 + ε) * x ^ (12 + 12 * ε) := by
          rw [rpow_mul_self X hXpos ε]
  suffices 5 * (x ^ (10 - 12 * ε) * x ^ (12 + 12 * ε)) ≤
      5 * ((4 * K / 5 * (20 * Real.sqrt 6) ^ (1 + ε)) * X ^ (2 + ε) * x ^ (12 + 12 * ε)) by
    nlinarith [Real.rpow_pos_of_pos hx (10 - 12 * ε)]
  rw [hx_combine]
  nlinarith [Real.rpow_pos_of_pos hx (12 + 12 * ε),
             Real.rpow_pos_of_pos hXpos (2 + ε),
             Real.rpow_pos_of_pos (show (0:ℝ) < 20 * Real.sqrt 6 by positivity) (1 + ε)]

lemma abc_pointwise_bound_core
    (K : ℝ) (hK : 0 < K) (ε : ℝ) (hε : 0 < ε) (hε2 : (10 : ℝ) - 12 * ε > 0)
    (hABC_K : ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
        Nat.Coprime a b → a + b = c →
          (c : ℝ) ≤ K * ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε))
    (x : ℕ+) (u : ℤ) (X : ℝ)
    (hX : 4 < X)
    (hx_large : (x : ℝ) > X ^ ((1 : ℝ) / 11))
    (hd_pos : 1 ≤ |u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22|)
    (hd_bound : (|u ^ 2 - 5 * (↑(x : ℕ) : ℤ) ^ 22| : ℝ) ≤ 4 * X) :
    (x : ℝ) ^ (10 - 12 * ε) ≤
      (4 * K / 5 * (20 * Real.sqrt 6) ^ (1 + ε)) * X ^ (2 + ε) := by
  have hXpos : (0 : ℝ) < X := by linarith
  have hx_pos : (0 : ℝ) < (x : ℝ) := by positivity
  have hu_ne := u_ne_zero_of_bounds x u X hX hx_large hd_bound
  have hu2 := u_sq_lt_six_x22 x u X hX hx_large hd_bound
  obtain ⟨a₀, b₀, ha₀, hb₀, hsum, hgcd, hrad⟩ := construct_triple x u hu_ne hd_pos hu2
  exact real_rearrange K hK ε hε hε2 (x : ℝ) hx_pos X hXpos
    (abc_core_combine K hK ε hε hABC_K x u X hX hd_pos hd_bound hu2 hu_ne
      a₀ b₀ ha₀ hb₀ hsum hgcd hrad)

lemma abc_pointwise_power_bound
    (habc : ABC) (ε : ℝ) (hε : 0 < ε) (hε2 : (10 : ℝ) - 12 * ε > 0) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ X : ℝ, X₀ < X →
        ∀ p : ℕ+ × ℤ, p ∈ E4_set X →
          (p.1 : ℝ) ^ (10 - 12 * ε) ≤ C₁ * X ^ (2 + ε) := by
  obtain ⟨K, hK, hABC_K⟩ := habc ε hε
  refine ⟨4 * K / 5 * (20 * Real.sqrt 6) ^ (1 + ε), by positivity, 4, by norm_num, ?_⟩
  intro X hX p ⟨hx_large, hd_pos, hd_bound⟩
  exact abc_pointwise_bound_core K hK ε hε hε2 hABC_K p.1 p.2 X hX hx_large hd_pos hd_bound

lemma power_bound_to_linear_bound
    (α β C₁ : ℝ) (hα : 0 < α) (hC₁ : 0 < C₁) :
    ∃ C₂ : ℝ, 0 < C₂ ∧
      ∀ (x : ℕ+) (X : ℝ), 0 < X →
        (x : ℝ) ^ α ≤ C₁ * X ^ β →
          (x : ℝ) ≤ C₂ * X ^ (β / α) := by
  refine ⟨C₁ ^ (1 / α), by positivity, fun x X hX hbound => ?_⟩
  have hx_pos : (0 : ℝ) < (x : ℝ) := by positivity
  rw [show (x : ℝ) = ((x : ℝ) ^ α) ^ (1 / α) by
    rw [← Real.rpow_mul (le_of_lt hx_pos), show α * (1 / α) = 1 by field_simp, Real.rpow_one]]
  calc ((x : ℝ) ^ α) ^ (1 / α)
      ≤ (C₁ * X ^ β) ^ (1 / α) :=
        Real.rpow_le_rpow (by positivity) hbound (by positivity)
    _ = C₁ ^ (1 / α) * (X ^ β) ^ (1 / α) :=
        Real.mul_rpow (le_of_lt hC₁) (by positivity)
    _ = C₁ ^ (1 / α) * X ^ (β / α) := by
        rw [← Real.rpow_mul (le_of_lt hX)]
        ring_nf

lemma abc_x_upper_bound
    (habc : ABC) (ε : ℝ) (hε : 0 < ε) (hε2 : (10 : ℝ) - 12 * ε > 0) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ X : ℝ, X₀ < X →
        ∀ p : ℕ+ × ℤ, p ∈ E4_set X →
          (p.1 : ℝ) ≤ C₂ * X ^ ((2 + ε) / (10 - 12 * ε)) := by
  obtain ⟨C₁, hC₁, X₀, hX₀, hpow⟩ := abc_pointwise_power_bound habc ε hε hε2
  obtain ⟨C₂, hC₂, hlin⟩ := power_bound_to_linear_bound (10 - 12 * ε) (2 + ε) C₁ hε2 hC₁
  exact ⟨C₂, hC₂, X₀, hX₀, fun X hXX₀ p hp => hlin p.1 X (by linarith) (hpow X hXX₀ p hp)⟩

lemma E4_x_bounded (habc : ABC) (X : ℝ) (_hX : 0 < X) :
    ∃ N : ℕ, ∀ p ∈ E4_set X, (p.1 : ℕ) ≤ N := by
  obtain ⟨C₂, _hC₂, X₀, _hX₀, hbound⟩ := abc_x_upper_bound habc (1/100) (by positivity) (by norm_num)
  set X' := max X (X₀ + 1) with hX'_def
  have hX'_gt_X₀ : X₀ < X' := lt_max_of_lt_right (by linarith)
  have hX'_ge_X : X ≤ X' := le_max_left X (X₀ + 1)
  set α : ℝ := (2 + 1/100) / (10 - 12 * (1/100))
  refine ⟨max ⌈X' ^ ((1 : ℝ) / 11)⌉₊ ⌈C₂ * X' ^ α⌉₊, ?_⟩
  intro p hp
  by_cases hle : (p.1 : ℝ) ≤ X' ^ ((1 : ℝ) / 11)
  · exact le_trans (Nat.cast_le.mp (le_trans hle (Nat.le_ceil _))) (le_max_left _ _)
  · push_neg at hle
    have hp' : p ∈ E4_set X' := by
      simp only [E4_set, Set.mem_setOf_eq] at hp ⊢
      exact ⟨hle, hp.2.1, by linarith⟩
    exact le_trans (Nat.cast_le.mp (le_trans (hbound X' hX'_gt_X₀ p hp') (Nat.le_ceil _)))
      (le_max_right _ _)

lemma E4_u_bounded (X : ℝ) (N : ℕ) (x : ℕ+) (u : ℤ)
    (hx : (x : ℕ) ≤ N) (hu : (|u ^ 2 - 5 * (↑↑x : ℤ) ^ 22| : ℝ) ≤ 4 * X) :
    u.natAbs ≤ Nat.sqrt (5 * N ^ 22 + 4 * ⌈X⌉₊ + 1) + 1 := by
  set B : ℕ := 5 * N ^ 22 + 4 * ⌈X⌉₊ with hB_def
  suffices h : u.natAbs ^ 2 ≤ B by
    exact le_trans (Nat.le_sqrt'.mpr (by omega)) (Nat.le_add_right _ 1)
  have h3 : u ^ 2 - 5 * (↑↑x : ℤ) ^ 22 ≤ 4 * (⌈X⌉₊ : ℤ) := by
    exact_mod_cast show (u ^ 2 - 5 * (↑↑x : ℤ) ^ 22 : ℝ) ≤ 4 * ↑⌈X⌉₊ by
      linarith [(abs_le.mp hu).2, Nat.le_ceil X]
  have h5 : u ^ 2 ≤ (B : ℤ) := by
    rw [hB_def]
    push_cast
    linarith [show (↑↑x : ℤ) ^ 22 ≤ (N : ℤ) ^ 22 from
      by exact_mod_cast Nat.pow_le_pow_left hx 22]
  exact_mod_cast show (u.natAbs : ℤ) ^ 2 ≤ (B : ℤ) from Int.natAbs_sq u ▸ h5

lemma pnat_int_finite_of_bounded (N M : ℕ) :
    {p : ℕ+ × ℤ | (p.1 : ℕ) ≤ N ∧ p.2.natAbs ≤ M}.Finite := by
  apply Set.Finite.subset (Set.Finite.prod
    (Set.finite_Iio (⟨N + 1, by omega⟩ : ℕ+))
    (Set.finite_Icc (-(M : ℤ)) M))
  intro ⟨x, u⟩ ⟨hx, hu⟩
  simp only [Set.mem_prod, Set.mem_Iio, Set.mem_Icc]
  exact ⟨by exact_mod_cast Nat.lt_succ_of_le hx,
    by linarith [neg_abs_le u, show (u.natAbs : ℤ) ≤ M from Int.ofNat_le.mpr hu],
    le_trans (Int.le_natAbs) (Int.ofNat_le.mpr hu)⟩

lemma E4_set_finite (habc : ABC) (X : ℝ) : (E4_set X).Finite := by
  by_cases hX : X ≤ 0
  · apply Set.Finite.subset Set.finite_empty
    intro ⟨x, u⟩ ⟨_, h1, h2⟩
    have h1' : (1 : ℝ) ≤ (|u ^ 2 - 5 * (↑↑x : ℤ) ^ 22| : ℝ) := by exact_mod_cast h1
    linarith
  · push_neg at hX
    obtain ⟨N, hN⟩ := E4_x_bounded habc X hX
    set M := Nat.sqrt (5 * N ^ 22 + 4 * ⌈X⌉₊ + 1) + 1
    exact (pnat_int_finite_of_bounded N M).subset fun p hp =>
      ⟨hN p hp, E4_u_bounded X N p.1 p.2 (hN p hp) hp.2.2⟩

lemma target_subset_image (R : RamanujanTau) (X : ℝ) :
    {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((1 : ℝ) / 11) ∧
        (R.τ (p ^ (2 * 2)) = ℓ ∨ R.τ (p ^ (2 * 2)) = -(ℓ : ℤ))} ⊆
    (fun p : ℕ+ => (R.τ (p ^ (2 * 2))).natAbs) ''
      {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((1 : ℝ) / 11)} := by
  intro ℓ hℓ
  simp only [Set.mem_setOf_eq] at hℓ
  obtain ⟨_, _, p, hp_prime, hp_le, hp_tau⟩ := hℓ
  exact ⟨p, ⟨hp_prime, hp_le⟩, by cases hp_tau with | inl h => simp [h] | inr h => simp [h]⟩

lemma small_primes_set_finite (X : ℝ) :
    {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((1 : ℝ) / 11)}.Finite := by
  apply Set.Finite.subset (show {p : ℕ+ | (p : ℕ) ≤ ⌊X ^ ((1 : ℝ) / 11)⌋₊}.Finite from ?_)
  · intro p ⟨_, hp⟩
    simp only [Set.mem_setOf_eq]
    exact Nat.le_floor hp
  · have : {p : ℕ+ | (p : ℕ) ≤ ⌊X ^ ((1 : ℝ) / 11)⌋₊} ⊆
        (PNat.val ⁻¹' (Set.Iic ⌊X ^ ((1 : ℝ) / 11)⌋₊)) := fun p hp => hp
    exact Set.Finite.subset ((Set.finite_Iic _).preimage
      (fun a _ b _ h => PNat.eq (by exact_mod_cast h : (a : ℕ) = b))) this

lemma small_primes_ncard_le (X : ℝ) (_hX : 0 < X) :
    {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((1 : ℝ) / 11)}.ncard ≤ ⌊X ^ ((1 : ℝ) / 11)⌋₊ + 1 := by
  set S := {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((1 : ℝ) / 11)}
  set T := (Finset.Icc (1 : ℕ) (⌊X ^ ((1 : ℝ) / 11)⌋₊)) with hT_def
  have hinj : Set.InjOn PNat.val S := fun a _ b _ h => PNat.eq h
  have hmaps : ∀ p ∈ S, (p : ℕ) ∈ (T : Set ℕ) := fun p ⟨_, hp⟩ =>
    by simp only [hT_def, Finset.mem_coe, Finset.mem_Icc]; exact ⟨p.pos, Nat.le_floor hp⟩
  calc S.ncard ≤ (T : Set ℕ).ncard :=
        Set.ncard_le_ncard_of_injOn PNat.val hmaps hinj (Set.toFinite _)
    _ = T.card := by rw [Set.ncard_coe_finset]
    _ ≤ ⌊X ^ ((1 : ℝ) / 11)⌋₊ + 1 := by
        rw [hT_def, Nat.card_Icc]
        omega

lemma k2_small_primes_bound (R : RamanujanTau) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ X : ℝ, X₀ < X →
        ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
          ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((1 : ℝ) / 11) ∧
            (R.τ (p ^ (2 * 2)) = ℓ ∨ R.τ (p ^ (2 * 2)) = -(ℓ : ℤ))}.ncard : ℝ) ≤
        C * X ^ ((6 : ℝ) / 11) := by
  refine ⟨2, by norm_num, 1, by norm_num, fun X hX => ?_⟩
  have hX0 : 0 < X := by linarith
  have hfin := small_primes_set_finite X
  have h1 : ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((1 : ℝ) / 11) ∧
        (R.τ (p ^ (2 * 2)) = ℓ ∨ R.τ (p ^ (2 * 2)) = -(ℓ : ℤ))}).ncard ≤
    {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((1 : ℝ) / 11)}.ncard :=
    le_trans (Set.ncard_le_ncard (target_subset_image R X) (hfin.image _))
      (Set.ncard_image_le hfin)
  have h3 : (({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((1 : ℝ) / 11) ∧
        (R.τ (p ^ (2 * 2)) = ℓ ∨ R.τ (p ^ (2 * 2)) = -(ℓ : ℤ))}).ncard : ℝ) ≤
      X ^ ((1 : ℝ) / 11) + 1 := by
    calc _ ≤ (↑(⌊X ^ ((1 : ℝ) / 11)⌋₊ + 1) : ℝ) :=
          Nat.cast_le.mpr (le_trans h1 (small_primes_ncard_le X hX0))
      _ ≤ X ^ ((1 : ℝ) / 11) + 1 := by
          push_cast
          linarith [Nat.floor_le (Real.rpow_nonneg (le_of_lt hX0) ((1 : ℝ) / 11))]
  linarith [Real.one_le_rpow (by linarith : (1 : ℝ) ≤ X) (by norm_num : (0 : ℝ) ≤ 6 / 11),
    Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ X) (by norm_num : (1 : ℝ) / 11 ≤ 6 / 11)]
/-! ## k = 2 contribution: injection into E₄ -/

lemma tau_p4_identity (R : RamanujanTau) (p : ℕ+) (hp : (p : ℕ).Prime) :
    (2 * R.τ p ^ 2 - 3 * (↑(p : ℕ) : ℤ) ^ 11) ^ 2 - 5 * (↑(p : ℕ) : ℤ) ^ 22 =
    4 * R.τ (p ^ (2 * 2)) := by
  have h0 : R.τ (p ^ 0) = 1 := by simp [tau_one_eq_one R]
  have hp1 : R.τ (p ^ 1) = R.τ p := by simp
  have h2 : R.τ (p ^ 2) = R.τ p * R.τ (p ^ 1) - (↑(p : ℕ) : ℤ) ^ 11 * R.τ (p ^ 0) :=
    R.hecke_rec p hp 2 (by norm_num)
  rw [hp1, h0] at h2
  have h3 : R.τ (p ^ 3) = R.τ p * R.τ (p ^ 2) - (↑(p : ℕ) : ℤ) ^ 11 * R.τ (p ^ 1) :=
    R.hecke_rec p hp 3 (by norm_num)
  rw [hp1] at h3
  have h4 : R.τ (p ^ 4) = R.τ p * R.τ (p ^ 3) - (↑(p : ℕ) : ℤ) ^ 11 * R.τ (p ^ 2) :=
    R.hecke_rec p hp 4 (by norm_num)
  rw [show p ^ (2 * 2) = p ^ 4 from by norm_num, h4, h3, h2]
  ring

lemma not_sq_five_mul_sq (n : ℕ) (hn : 0 < n) : ¬ IsSquare (5 * n ^ 2) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro ⟨m, hm⟩
  have h5 : Nat.Prime 5 := by decide
  obtain ⟨k, rfl⟩ := h5.dvd_of_dvd_pow (show 5 ∣ m ^ 2 from ⟨n ^ 2, by nlinarith⟩)
  have h1 : n ^ 2 = 5 * k ^ 2 := by nlinarith
  have h5n : 5 ∣ n := h5.dvd_of_dvd_pow ⟨k ^ 2, by omega⟩
  obtain ⟨j, rfl⟩ := h5n
  exact ih j (by omega) (by omega) ⟨k, by nlinarith⟩

lemma five_mul_pow22_not_sq (p : ℕ+) :
    ∀ u : ℤ, u ^ 2 ≠ 5 * (↑(p : ℕ) : ℤ) ^ 22 := by
  intro u hu
  have hp : 0 < (p : ℕ) ^ 11 := by positivity
  have hunat : u.natAbs ^ 2 = 5 * ((p : ℕ) ^ 11) ^ 2 := by
    exact_mod_cast show (u.natAbs : ℤ) ^ 2 = 5 * ((↑(p : ℕ) : ℤ) ^ 11) ^ 2 by
      simp [sq_abs, hu]
      ring
  exact not_sq_five_mul_sq ((p : ℕ) ^ 11) hp ⟨u.natAbs, by linarith⟩

lemma injection_into_E4_set (R : RamanujanTau) (p : ℕ+) (hp : (p : ℕ).Prime)
    (X : ℝ) (hpX : (p : ℝ) > X ^ ((1 : ℝ) / 11))
    (ℓ : ℕ) (_hℓ : Nat.Prime ℓ) (hℓX : (ℓ : ℝ) ≤ X)
    (hτ : R.τ (p ^ (2 * 2)) = ℓ ∨ R.τ (p ^ (2 * 2)) = -(ℓ : ℤ)) :
    (⟨p, 2 * R.τ p ^ 2 - 3 * (↑(p : ℕ) : ℤ) ^ 11⟩ : ℕ+ × ℤ) ∈ E4_set X := by
  set u := 2 * R.τ p ^ 2 - 3 * (↑(p : ℕ) : ℤ) ^ 11 with hu_def
  refine ⟨hpX, ?_, ?_⟩
  · have hne : u ^ 2 - 5 * (↑(p : ℕ) : ℤ) ^ 22 ≠ 0 := by
      intro h
      exact five_mul_pow22_not_sq p u (by omega)
    exact Int.one_le_abs hne
  have hid : u ^ 2 - 5 * (↑(p : ℕ) : ℤ) ^ 22 = 4 * R.τ (p ^ (2 * 2)) :=
    tau_p4_identity R p hp
  rw [show (↑u : ℝ) ^ 2 - 5 * (↑(↑(p : ℕ) : ℤ) : ℝ) ^ 22 = (4 * R.τ (p ^ (2 * 2)) : ℤ) from by
    have := congr_arg (Int.cast : ℤ → ℝ) hid
    push_cast at this ⊢
    linarith]
  rcases hτ with h | h <;> rw [h] <;> push_cast
  · rw [abs_of_nonneg (by positivity)]
    linarith
  · rw [show (4 : ℝ) * -(ℓ : ℝ) = -(4 * ℓ) by ring,
       abs_neg, abs_of_nonneg (by positivity)]
    linarith

lemma ncard_ell_le_E4 (habc : ABC) (R : RamanujanTau) (X : ℝ) :
    {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) > X ^ ((1 : ℝ) / 11) ∧
        (R.τ (p ^ (2 * 2)) = ℓ ∨ R.τ (p ^ (2 * 2)) = -(ℓ : ℤ))}.ncard ≤
    E4 X := by
  set P_set := {p : ℕ+ | (p : ℕ).Prime ∧ (p : ℝ) > X ^ ((1 : ℝ) / 11) ∧
    ∃ ℓ : ℕ, Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      (R.τ (p ^ (2 * 2)) = ℓ ∨ R.τ (p ^ (2 * 2)) = -(ℓ : ℤ))}
  set L_set := {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
    ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) > X ^ ((1 : ℝ) / 11) ∧
      (R.τ (p ^ (2 * 2)) = ℓ ∨ R.τ (p ^ (2 * 2)) = -(ℓ : ℤ))}
  set f : ℕ+ → ℕ+ × ℤ := fun p => ⟨p, 2 * R.τ p ^ 2 - 3 * (↑(p : ℕ) : ℤ) ^ 11⟩
  have hf_maps : ∀ p ∈ P_set, f p ∈ E4_set X := fun p ⟨hp, hpX, ℓ, _hℓ, hℓX, hτ⟩ =>
    injection_into_E4_set R p hp X hpX ℓ _hℓ hℓX hτ
  have hf_inj : Set.InjOn f P_set := fun _ _ _ _ h => congr_arg Prod.fst h
  have hP_le : P_set.ncard ≤ E4 X :=
    Set.ncard_le_ncard_of_injOn f hf_maps hf_inj (E4_set_finite habc X)
  set g : ℕ+ → ℕ := fun p => (R.τ (p ^ (2 * 2))).natAbs
  have hL_sub : L_set ⊆ g '' P_set := by
    intro ℓ ⟨hℓ_prime, hℓ_le, p, hp, hpX, hτ⟩
    refine ⟨p, ⟨hp, hpX, ℓ, hℓ_prime, hℓ_le, hτ⟩, ?_⟩
    show (R.τ (p ^ (2 * 2))).natAbs = ℓ
    rcases hτ with h | h
    · rw [h, Int.natAbs_natCast]
    · rw [h, Int.natAbs_neg, Int.natAbs_natCast]
  have hP_fin : P_set.Finite := Set.Finite.of_injOn hf_maps hf_inj (E4_set_finite habc X)
  calc L_set.ncard ≤ (g '' P_set).ncard := Set.ncard_le_ncard hL_sub (hP_fin.image g)
    _ ≤ P_set.ncard := Set.ncard_image_le hP_fin
    _ ≤ E4 X := hP_le

lemma k2_set_subset_union (R : RamanujanTau) (X : ℝ) :
    {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ((ℓ : ℤ) ∈ X2k R 2 ∨ (-(ℓ : ℤ)) ∈ X2k R 2)} ⊆
    {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((1 : ℝ) / 11) ∧
        (R.τ (p ^ (2 * 2)) = ℓ ∨ R.τ (p ^ (2 * 2)) = -(ℓ : ℤ))} ∪
    {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) > X ^ ((1 : ℝ) / 11) ∧
        (R.τ (p ^ (2 * 2)) = ℓ ∨ R.τ (p ^ (2 * 2)) = -(ℓ : ℤ))} := by
  intro ℓ ⟨h₁, h₂, h₃⟩
  obtain ⟨p, hp, htau⟩ : ∃ (p : ℕ+), (p : ℕ).Prime ∧
      (R.τ (p ^ (2 * 2)) = ℓ ∨ R.τ (p ^ (2 * 2)) = -(ℓ : ℤ)) := by
    rcases h₃ with ⟨p, hp, h₇⟩ | ⟨p, hp, h₇⟩ <;>
      exact ⟨p, hp, by simp_all⟩
  rcases le_or_gt (p : ℝ) (X ^ ((1 : ℝ) / 11)) with h₉ | h₉
  · exact Set.mem_union_left _ ⟨h₁, h₂, p, hp, h₉, htau⟩
  · exact Set.mem_union_right _ ⟨h₁, h₂, p, hp, h₉, htau⟩

lemma k2_union_finite (R : RamanujanTau) (X : ℝ) :
    ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((1 : ℝ) / 11) ∧
        (R.τ (p ^ (2 * 2)) = ℓ ∨ R.τ (p ^ (2 * 2)) = -(ℓ : ℤ))} ∪
    {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) > X ^ ((1 : ℝ) / 11) ∧
        (R.τ (p ^ (2 * 2)) = ℓ ∨ R.τ (p ^ (2 * 2)) = -(ℓ : ℤ))}).Finite := by
  exact (nats_le_X_finite X).subset fun ℓ h => by
    rcases h with ⟨_, h, _⟩ | ⟨_, h, _⟩ <;> exact h

lemma k2_contribution_bound (habc : ABC) (R : RamanujanTau) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ X₂ : ℝ, 0 < X₂ ∧
      ∀ X : ℝ, X₂ < X →
        ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
          ((ℓ : ℤ) ∈ X2k R 2 ∨ (-(ℓ : ℤ)) ∈ X2k R 2)}.ncard : ℝ) ≤
        C₂ * X ^ ((6 : ℝ) / 11) + (E4 X : ℝ) := by
  obtain ⟨C, hCpos, X₁, hX₁pos, hsmall⟩ := k2_small_primes_bound R
  refine ⟨C, hCpos, X₁, hX₁pos, ?_⟩
  intro X hX
  have hcard := le_trans (Set.ncard_le_ncard (k2_set_subset_union R X) (k2_union_finite R X))
    (Set.ncard_union_le _ _)
  calc ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
          ((ℓ : ℤ) ∈ X2k R 2 ∨ (-(ℓ : ℤ)) ∈ X2k R 2)}.ncard : ℝ)
      ≤ ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
          ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) ≤ X ^ ((1 : ℝ) / 11) ∧
            (R.τ (p ^ (2 * 2)) = ℓ ∨ R.τ (p ^ (2 * 2)) = -(ℓ : ℤ))}.ncard : ℝ) +
        ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
          ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) > X ^ ((1 : ℝ) / 11) ∧
            (R.τ (p ^ (2 * 2)) = ℓ ∨ R.τ (p ^ (2 * 2)) = -(ℓ : ℤ))}.ncard : ℝ) := by
        exact_mod_cast hcard
    _ ≤ C * X ^ ((6 : ℝ) / 11) + (E4 X : ℝ) := by
        have h1 := hsmall X hX
        have h2 : ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
            ∃ p : ℕ+, (p : ℕ).Prime ∧ (p : ℝ) > X ^ ((1 : ℝ) / 11) ∧
              (R.τ (p ^ (2 * 2)) = ℓ ∨ R.τ (p ^ (2 * 2)) = -(ℓ : ℤ))}.ncard : ℝ) ≤
            (E4 X : ℝ) := Nat.cast_le.mpr (ncard_ell_le_E4 habc R X)
        linarith
/-! ## k ≥ 3 contribution via Proposition 5.4 -/

lemma per_k_odd_prime_bound (R : RamanujanTau) (c₄ : ℝ) (_hc₄ : 0 < c₄)
    (h54 : ∀ N : ℝ, c₄ < N →
      ∀ k : ℕ, 3 ≤ k → (k : ℝ) < Real.log N / (2 * Real.log 2) →
        ((oddPrimesSigned ∩ X2k R k ∩ {z : ℤ | (|z| : ℝ) ≤ N}).ncard : ℝ) < N ^ ((9 : ℝ) / 10))
    (X : ℝ) (hX : c₄ < X) (k : ℕ) (hk3 : 3 ≤ k)
    (hklog : (k : ℝ) < Real.log X / (2 * Real.log 2)) :
    ({ℓ : ℕ | Nat.Prime ℓ ∧ ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ X ∧
      ((ℓ : ℤ) ∈ X2k R k ∨ (-(ℓ : ℤ)) ∈ X2k R k)}.ncard : ℝ) < X ^ ((9 : ℝ) / 10) := by
  have hT := h54 X hX k hk3 hklog
  set S := {ℓ : ℕ | Nat.Prime ℓ ∧ ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ X ∧
    ((ℓ : ℤ) ∈ X2k R k ∨ (-(ℓ : ℤ)) ∈ X2k R k)}
  set T := oddPrimesSigned ∩ X2k R k ∩ {z : ℤ | (|z| : ℝ) ≤ X}
  suffices h : S.ncard ≤ T.ncard by
    calc (S.ncard : ℝ) ≤ (T.ncard : ℝ) := by exact_mod_cast h
      _ < X ^ ((9 : ℝ) / 10) := hT
  set f : ℕ → ℤ := fun ℓ => if (ℓ : ℤ) ∈ X2k R k then (ℓ : ℤ) else -(ℓ : ℤ)
  have hTfin : T.Finite :=
    (show {z : ℤ | (|z| : ℝ) ≤ X}.Finite from
      (Set.finite_Icc ⌈-X⌉ ⌊X⌋).subset fun z hz => by
        simp only [Set.mem_setOf_eq] at hz
        exact Set.mem_Icc.mpr ⟨Int.ceil_le.mpr (by linarith [neg_abs_le (z : ℝ)]),
          Int.le_floor.mpr (le_abs_self (z : ℝ) |>.trans hz)⟩).subset (Set.inter_subset_right)
  have hmaps : ∀ ℓ ∈ S, f ℓ ∈ T := by
    intro ℓ ⟨hprime, hne2, hle, hor⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [f, oddPrimesSigned, Set.mem_setOf_eq]
      split_ifs <;> exact ⟨ℓ, hprime, hne2, by tauto⟩
    · simp only [f]
      split_ifs with h
      · exact h
      · exact hor.resolve_left h
    · show (|↑(f ℓ)| : ℝ) ≤ X
      simp only [f]; split_ifs with h
      · rwa [Int.cast_natCast ℓ, abs_of_nonneg (Nat.cast_nonneg' ℓ)]
      · rwa [show (↑(-(ℓ : ℤ)) : ℝ) = -(ℓ : ℝ) by push_cast; ring,
          abs_neg, abs_of_nonneg (Nat.cast_nonneg' ℓ)]
  have hinj : Set.InjOn f S := by
    intro a ⟨ha_prime, _, _, _⟩ b ⟨_, _, _, _⟩ heq
    simp only [f] at heq
    split_ifs at heq with h1 _ h1 <;>
      first | exact_mod_cast heq | exact_mod_cast neg_inj.mp heq |
        (exfalso; linarith [show (0 : ℤ) < a from by exact_mod_cast ha_prime.pos])
  exact Set.ncard_le_ncard_of_injOn f hmaps hinj hTfin

lemma target_ncard_le_one_plus_odd (R : RamanujanTau) (X : ℝ) :
    ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ k : ℕ, 3 ≤ k ∧ (k : ℝ) < Real.log X / (2 * Real.log 2) ∧
        ((ℓ : ℤ) ∈ X2k R k ∨ (-(ℓ : ℤ)) ∈ X2k R k)}.ncard : ℝ) ≤
    1 + ({ℓ : ℕ | Nat.Prime ℓ ∧ ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ X ∧
      ∃ k : ℕ, 3 ≤ k ∧ (k : ℝ) < Real.log X / (2 * Real.log 2) ∧
        ((ℓ : ℤ) ∈ X2k R k ∨ (-(ℓ : ℤ)) ∈ X2k R k)}.ncard : ℝ) := by
  set S₁ := {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
    ∃ k : ℕ, 3 ≤ k ∧ (k : ℝ) < Real.log X / (2 * Real.log 2) ∧
      ((ℓ : ℤ) ∈ X2k R k ∨ (-(ℓ : ℤ)) ∈ X2k R k)} with hS₁_def
  set S₂ := {ℓ : ℕ | Nat.Prime ℓ ∧ ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ X ∧
    ∃ k : ℕ, 3 ≤ k ∧ (k : ℝ) < Real.log X / (2 * Real.log 2) ∧
      ((ℓ : ℤ) ∈ X2k R k ∨ (-(ℓ : ℤ)) ∈ X2k R k)} with hS₂_def
  by_cases hfin : S₁.Finite
  · have hS₁_sub : S₁ ⊆ {2} ∪ S₂ := by
      intro ℓ hℓ
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, S₁, S₂] at hℓ ⊢
      by_cases h2 : ℓ = 2
      · left
        exact h2
      · right
        exact ⟨hℓ.1, h2, hℓ.2⟩
    have hS₂_sub : S₂ ⊆ S₁ := by
      intro ℓ hℓ
      simp only [Set.mem_setOf_eq, S₂, S₁] at hℓ ⊢
      exact ⟨hℓ.1, hℓ.2.2⟩
    have hfin_union := (Set.finite_singleton 2).union (hfin.subset hS₂_sub)
    have h := le_trans (Set.ncard_le_ncard hS₁_sub hfin_union) (Set.ncard_union_le {2} S₂)
    rw [Set.ncard_singleton] at h
    exact_mod_cast (show S₁.ncard ≤ 1 + S₂.ncard by omega)
  · simp [Set.Infinite.ncard (Set.not_finite.mp hfin)]
    linarith [Nat.cast_nonneg (α := ℝ) S₂.ncard]

lemma sum_ncard_bound (R : RamanujanTau) (X : ℝ) (hX : 1 < X)
    (bound_per_k : ∀ k : ℕ, 3 ≤ k → (k : ℝ) < Real.log X / (2 * Real.log 2) →
      ({ℓ : ℕ | Nat.Prime ℓ ∧ ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ X ∧
        ((ℓ : ℤ) ∈ X2k R k ∨ (-(ℓ : ℤ)) ∈ X2k R k)}.ncard : ℝ) < X ^ ((9 : ℝ) / 10)) :
    (∑ k ∈ Finset.Ico 3 ⌈Real.log X / (2 * Real.log 2)⌉₊,
      ({ℓ : ℕ | Nat.Prime ℓ ∧ ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ X ∧
        ((ℓ : ℤ) ∈ X2k R k ∨ (-(ℓ : ℤ)) ∈ X2k R k)}.ncard) : ℝ) ≤
    Real.log X / (2 * Real.log 2) * X ^ ((9 : ℝ) / 10) := by
  set M := Real.log X / (2 * Real.log 2) with hM_def
  set I := Finset.Ico 3 ⌈M⌉₊ with hI_def
  set f := fun k => {ℓ : ℕ | Nat.Prime ℓ ∧ ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ X ∧
    ((ℓ : ℤ) ∈ X2k R k ∨ (-(ℓ : ℤ)) ∈ X2k R k)}.ncard with hf_def
  have h_per_k : ∀ k ∈ I, f k ≤ ⌊X ^ ((9 : ℝ) / 10)⌋₊ := by
    intro k hk
    rw [hI_def, Finset.mem_Ico] at hk
    exact Nat.le_floor (bound_per_k k hk.1 (Nat.lt_ceil.mp hk.2)).le
  have h_sum_le : ∑ k ∈ I, f k ≤ I.card * ⌊X ^ ((9 : ℝ) / 10)⌋₊ :=
    le_trans (Finset.sum_le_sum h_per_k) (by rw [Finset.sum_const, smul_eq_mul])
  have h_cast : (↑(I.card * ⌊X ^ ((9 : ℝ) / 10)⌋₊) : ℝ) ≤ (I.card : ℝ) * X ^ ((9 : ℝ) / 10) := by
    rw [Nat.cast_mul]; exact mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) (Nat.cast_nonneg _)
  have hM_nn : (0 : ℝ) ≤ M := div_nonneg (Real.log_nonneg (le_of_lt hX)) (by positivity)
  have h_card : (I.card : ℝ) ≤ M := by
    rw [hI_def, Nat.card_Ico]
    by_cases h3 : 3 ≤ ⌈M⌉₊
    · rw [show (↑(⌈M⌉₊ - 3) : ℝ) = (⌈M⌉₊ : ℝ) - 3 by push_cast [Nat.cast_sub h3]; ring]
      linarith [Nat.ceil_lt_add_one hM_nn]
    · rw [show ⌈M⌉₊ - 3 = 0 from Nat.sub_eq_zero_of_le (by omega), Nat.cast_zero]
      exact hM_nn
  calc (∑ k ∈ I, f k : ℝ) ≤ ↑(I.card * ⌊X ^ ((9 : ℝ) / 10)⌋₊) := by exact_mod_cast h_sum_le
    _ ≤ (I.card : ℝ) * X ^ ((9 : ℝ) / 10) := h_cast
    _ ≤ M * X ^ ((9 : ℝ) / 10) := mul_le_mul_of_nonneg_right h_card (by positivity)

lemma odd_prime_union_bound (R : RamanujanTau) (X : ℝ) (hX : 1 < X)
    (bound_per_k : ∀ k : ℕ, 3 ≤ k → (k : ℝ) < Real.log X / (2 * Real.log 2) →
      ({ℓ : ℕ | Nat.Prime ℓ ∧ ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ X ∧
        ((ℓ : ℤ) ∈ X2k R k ∨ (-(ℓ : ℤ)) ∈ X2k R k)}.ncard : ℝ) < X ^ ((9 : ℝ) / 10)) :
    ({ℓ : ℕ | Nat.Prime ℓ ∧ ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ X ∧
      ∃ k : ℕ, 3 ≤ k ∧ (k : ℝ) < Real.log X / (2 * Real.log 2) ∧
        ((ℓ : ℤ) ∈ X2k R k ∨ (-(ℓ : ℤ)) ∈ X2k R k)}.ncard : ℝ) ≤
    Real.log X / (2 * Real.log 2) * X ^ ((9 : ℝ) / 10) := by
  calc ({ℓ : ℕ | Nat.Prime ℓ ∧ ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ X ∧
      ∃ k : ℕ, 3 ≤ k ∧ (k : ℝ) < Real.log X / (2 * Real.log 2) ∧
        ((ℓ : ℤ) ∈ X2k R k ∨ (-(ℓ : ℤ)) ∈ X2k R k)}.ncard : ℝ)
      ≤ ((⋃ k ∈ Finset.Ico 3 ⌈Real.log X / (2 * Real.log 2)⌉₊,
        {ℓ : ℕ | Nat.Prime ℓ ∧ ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ X ∧
          ((ℓ : ℤ) ∈ X2k R k ∨ (-(ℓ : ℤ)) ∈ X2k R k)}).ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard (fun ℓ hℓ => by
          simp only [Set.mem_setOf_eq] at hℓ
          obtain ⟨hprime, hne2, hle, k, hk3, hklt, hmem⟩ := hℓ
          simp only [Set.mem_iUnion, Finset.mem_Ico, Set.mem_setOf_eq]
          exact ⟨k, ⟨hk3, Nat.lt_ceil.mpr hklt⟩, hprime, hne2, hle, hmem⟩) <|
          (Set.finite_Iic ⌊X⌋₊).subset fun ℓ hℓ => by
            simp only [Set.mem_iUnion, Finset.mem_Ico, Set.mem_setOf_eq] at hℓ
            obtain ⟨k, _, _, _, hle, _⟩ := hℓ
            exact Set.mem_Iic.mpr (Nat.le_floor hle)
    _ ≤ (∑ k ∈ Finset.Ico 3 ⌈Real.log X / (2 * Real.log 2)⌉₊,
        ({ℓ : ℕ | Nat.Prime ℓ ∧ ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ X ∧
          ((ℓ : ℤ) ∈ X2k R k ∨ (-(ℓ : ℤ)) ∈ X2k R k)}.ncard) : ℝ) := by
        exact_mod_cast Finset.set_ncard_biUnion_le _ _
    _ ≤ Real.log X / (2 * Real.log 2) * X ^ ((9 : ℝ) / 10) :=
        sum_ncard_bound R X hX bound_per_k

lemma absorb_bound (X : ℝ) (hX : Real.exp 6 ≤ X) :
    1 + Real.log X / (2 * Real.log 2) * X ^ ((9 : ℝ) / 10) ≤
    3 * (X ^ ((9 : ℝ) / 10) * Real.log X) := by
  have hX1 : 1 ≤ X := le_trans (Real.one_le_exp (by norm_num)) hX
  have hlogX : 6 ≤ Real.log X := by
    linarith [Real.log_le_log (Real.exp_pos 6) hX, Real.log_exp (6 : ℝ)]
  have hXrpow : 1 ≤ X ^ ((9 : ℝ) / 10) := Real.one_le_rpow hX1 (by norm_num)
  have h_prod_ge1 : 1 ≤ X ^ ((9 : ℝ) / 10) * Real.log X :=
    le_trans (by norm_num : (1 : ℝ) ≤ 1 * 1) (mul_le_mul hXrpow (by linarith) (by norm_num) (by linarith))
  have h_2log2 : 1 ≤ 2 * Real.log 2 := by
    rw [show (1 : ℝ) = 2 * (1/2) by ring]
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    rw [← Real.log_exp (1/2 : ℝ)]
    apply Real.log_le_log (Real.exp_pos _)
    nlinarith [Real.exp_one_lt_d9, sq_nonneg (Real.exp (1/2) - 2), Real.exp_pos (1/2 : ℝ),
               show Real.exp (1/2) * Real.exp (1/2) = Real.exp 1 by rw [← Real.exp_add]; ring_nf]
  have h_div_le := div_le_self (by linarith : 0 ≤ Real.log X) h_2log2
  nlinarith [mul_le_mul_of_nonneg_right h_div_le (by linarith : 0 ≤ X ^ ((9 : ℝ) / 10))]

lemma intermediate_k_contribution_bound (R : RamanujanTau)
    (h54_part1 : ∃ c₄ : ℝ, 0 < c₄ ∧
      ∀ N : ℝ, c₄ < N →
        ∀ k : ℕ, 3 ≤ k → (k : ℝ) < Real.log N / (2 * Real.log 2) →
          ((oddPrimesSigned ∩ X2k R k ∩ {z : ℤ | (|z| : ℝ) ≤ N}).ncard : ℝ) < N ^ ((9 : ℝ) / 10)) :
    ∃ C₃ : ℝ, 0 < C₃ ∧ ∃ X₃ : ℝ, 0 < X₃ ∧
      ∀ X : ℝ, X₃ < X →
        ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
          ∃ k : ℕ, 3 ≤ k ∧ (k : ℝ) < Real.log X / (2 * Real.log 2) ∧
            ((ℓ : ℤ) ∈ X2k R k ∨ (-(ℓ : ℤ)) ∈ X2k R k)}.ncard : ℝ) ≤
        C₃ * (X ^ ((9 : ℝ) / 10) * Real.log X) := by
  obtain ⟨c₄, hc₄, h54⟩ := h54_part1
  refine ⟨3, by norm_num, max c₄ (Real.exp 6), lt_max_iff.mpr (Or.inl hc₄), ?_⟩
  intro X hX
  have hXc : c₄ < X := lt_of_le_of_lt (le_max_left _ _) hX
  have hXe : Real.exp 6 ≤ X := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hX)
  have hX1 : 1 < X := lt_of_lt_of_le (by linarith [Real.add_one_le_exp (6 : ℝ)]) hXe
  calc ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
          ∃ k : ℕ, 3 ≤ k ∧ (k : ℝ) < Real.log X / (2 * Real.log 2) ∧
            ((ℓ : ℤ) ∈ X2k R k ∨ (-(ℓ : ℤ)) ∈ X2k R k)}.ncard : ℝ)
      ≤ 1 + ({ℓ : ℕ | Nat.Prime ℓ ∧ ℓ ≠ 2 ∧ (ℓ : ℝ) ≤ X ∧
          ∃ k : ℕ, 3 ≤ k ∧ (k : ℝ) < Real.log X / (2 * Real.log 2) ∧
            ((ℓ : ℤ) ∈ X2k R k ∨ (-(ℓ : ℤ)) ∈ X2k R k)}.ncard : ℝ) :=
        target_ncard_le_one_plus_odd R X
    _ ≤ 1 + Real.log X / (2 * Real.log 2) * X ^ ((9 : ℝ) / 10) := by
        linarith [odd_prime_union_bound R X hX1
          (fun k hk3 hklog => per_k_odd_prime_bound R c₄ hc₄ h54 X hXc k hk3 hklog)]
    _ ≤ 3 * (X ^ ((9 : ℝ) / 10) * Real.log X) := absorb_bound X hXe

lemma S_odd_ncard_le_sum (R : RamanujanTau) (h54 : Proposition5_4 R) :
    ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, X₀ < X →
      ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
        ∃ k : ℕ, 1 ≤ k ∧ ((ℓ : ℤ) ∈ X2k R k ∨ (-(ℓ : ℤ)) ∈ X2k R k)}.ncard : ℝ) ≤
      ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
        ((ℓ : ℤ) ∈ X2k R 1 ∨ (-(ℓ : ℤ)) ∈ X2k R 1)}.ncard : ℝ) +
      ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
        ((ℓ : ℤ) ∈ X2k R 2 ∨ (-(ℓ : ℤ)) ∈ X2k R 2)}.ncard : ℝ) +
      ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
        ∃ k : ℕ, 3 ≤ k ∧ (k : ℝ) < Real.log X / (2 * Real.log 2) ∧
          ((ℓ : ℤ) ∈ X2k R k ∨ (-(ℓ : ℤ)) ∈ X2k R k)}.ncard : ℝ) := by
  obtain ⟨_, ⟨c₅, hc₅pos, hc₅⟩⟩ := h54
  refine ⟨c₅, hc₅pos, fun X hXgt => ?_⟩
  set S_all := {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
    ∃ k : ℕ, 1 ≤ k ∧ ((ℓ : ℤ) ∈ X2k R k ∨ (-(ℓ : ℤ)) ∈ X2k R k)}
  set S1 := {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
    ((ℓ : ℤ) ∈ X2k R 1 ∨ (-(ℓ : ℤ)) ∈ X2k R 1)}
  set S2 := {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
    ((ℓ : ℤ) ∈ X2k R 2 ∨ (-(ℓ : ℤ)) ∈ X2k R 2)}
  set S3 := {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
    ∃ k : ℕ, 3 ≤ k ∧ (k : ℝ) < Real.log X / (2 * Real.log 2) ∧
      ((ℓ : ℤ) ∈ X2k R k ∨ (-(ℓ : ℤ)) ∈ X2k R k)}
  have hsub : S_all ⊆ S1 ∪ S2 ∪ S3 := by
    intro ℓ hℓ
    simp only [S_all, Set.mem_setOf_eq] at hℓ
    obtain ⟨hprime, hle, k, hk1, hmem⟩ := hℓ
    by_cases hklt : (k : ℝ) < Real.log X / (2 * Real.log 2)
    · rcases k, hk1 with ⟨_ | _ | _ | k, hk1⟩
      · omega
      · left
        left
        exact ⟨hprime, hle, hmem⟩
      · left
        right
        exact ⟨hprime, hle, hmem⟩
      · right
        exact ⟨hprime, hle, k + 3, by omega, hklt, hmem⟩
    · push_neg at hklt
      have hempty := hc₅ X hXgt k hklt
      exfalso
      have hℓ_le : (|↑ℓ| : ℝ) ≤ X := by simp [Nat.abs_cast]; exact hle
      rcases hmem with hmem | hmem
      · have h : (ℓ : ℤ) ∈ X2k R k ∩ {z : ℤ | (|z| : ℝ) ≤ X} := ⟨hmem, hℓ_le⟩
        rw [hempty] at h
        exact Set.notMem_empty _ h
      · have h : (-(ℓ : ℤ)) ∈ X2k R k ∩ {z : ℤ | (|z| : ℝ) ≤ X} :=
          ⟨hmem, by simpa [abs_neg] using hℓ_le⟩
        rw [hempty] at h
        exact Set.notMem_empty _ h
  have hfin : (S1 ∪ S2 ∪ S3).Finite := by
    apply Set.Finite.subset (nats_le_X_finite X)
    intro ℓ hℓ
    simp only [S1, S2, S3, Set.mem_union, Set.mem_setOf_eq] at hℓ ⊢
    rcases hℓ with ((⟨_, hle, _⟩ | ⟨_, hle, _⟩) | ⟨_, hle, _⟩) <;> exact hle
  exact_mod_cast le_trans (Set.ncard_le_ncard hsub hfin)
    (le_trans (Set.ncard_union_le (S1 ∪ S2) S3)
      (Nat.add_le_add_right (Set.ncard_union_le S1 S2) _))

lemma S_le_one_plus_odd (R : RamanujanTau) (X : ℝ) :
    (S R X : ℝ) ≤ 1 +
      ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
        ∃ k : ℕ, 1 ≤ k ∧ ((ℓ : ℤ) ∈ X2k R k ∨ (-(ℓ : ℤ)) ∈ X2k R k)}.ncard : ℝ) := by
  unfold S
  have hfin : ({2} ∪ {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ k : ℕ, 1 ≤ k ∧ ((ℓ : ℤ) ∈ X2k R k ∨ (-(ℓ : ℤ)) ∈ X2k R k)} : Set ℕ).Finite :=
    Set.Finite.union (Set.finite_singleton 2)
      ((Set.finite_Iic (⌈X⌉₊)).subset fun ℓ hℓ =>
        Set.mem_Iic.mpr (Nat.cast_le.mp (hℓ.2.1.trans (Nat.le_ceil X))))
  have h := le_trans (Set.ncard_le_ncard (S_set_subset_union R X) hfin)
    (Set.ncard_union_le ({2} : Set ℕ) {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
      ∃ k : ℕ, 1 ≤ k ∧ ((ℓ : ℤ) ∈ X2k R k ∨ (-(ℓ : ℤ)) ∈ X2k R k)})
  rw [Set.ncard_singleton] at h
  exact_mod_cast show (S_set R X).ncard ≤ 1 + _ by omega

lemma reduction_lemma_helper (habc : ABC) (R : RamanujanTau) (h54 : Proposition5_4 R) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ X : ℝ, X₀ < X →
        (S R X : ℝ) ≤ C * (X ^ ((9 : ℝ) / 10) * Real.log X +
          X ^ ((13 : ℝ) / 22) + X ^ ((6 : ℝ) / 11) +
          (E2 X : ℝ) + (E4 X : ℝ)) := by
  obtain ⟨C₁, hC₁_pos, X₁, hX₁_pos, hk1⟩ := k1_contribution_bound habc R
  obtain ⟨C₂, hC₂_pos, X₂, hX₂_pos, hk2⟩ := k2_contribution_bound habc R
  obtain ⟨C₃, hC₃_pos, X₃, hX₃_pos, hk3⟩ :=
    intermediate_k_contribution_bound R h54.1
  obtain ⟨X₄, hX₄_pos, hdecomp⟩ := S_odd_ncard_le_sum R h54
  refine ⟨C₁ + C₂ + C₃ + 1, by linarith,
    max (max (max X₁ X₂) (max X₃ X₄)) (Real.exp 1),
    by positivity, fun X hX => ?_⟩
  have hm := le_max_left (max (max X₁ X₂) (max X₃ X₄)) (Real.exp 1)
  have hXe : Real.exp 1 ≤ X := (le_max_right _ _).trans (le_of_lt hX)
  have hX₁ : X₁ < X := lt_of_le_of_lt (le_trans (le_max_left _ X₂) (le_trans (le_max_left _ _) hm)) hX
  have hX₂ : X₂ < X := lt_of_le_of_lt (le_trans (le_max_right X₁ _) (le_trans (le_max_left _ _) hm)) hX
  have hX₃ : X₃ < X := lt_of_le_of_lt (le_trans (le_max_left _ X₄) (le_trans (le_max_right _ _) hm)) hX
  have hX₄ : X₄ < X := lt_of_le_of_lt (le_trans (le_max_right X₃ _) (le_trans (le_max_right _ _) hm)) hX
  have h_decomp := hdecomp X hX₄
  calc (S R X : ℝ) ≤ 1 + ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
        ∃ k : ℕ, 1 ≤ k ∧ ((ℓ : ℤ) ∈ X2k R k ∨ (-(ℓ : ℤ)) ∈ X2k R k)}.ncard : ℝ) :=
      S_le_one_plus_odd R X
    _ ≤ 1 + (({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
          ((ℓ : ℤ) ∈ X2k R 1 ∨ (-(ℓ : ℤ)) ∈ X2k R 1)}.ncard : ℝ) +
        ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
          ((ℓ : ℤ) ∈ X2k R 2 ∨ (-(ℓ : ℤ)) ∈ X2k R 2)}.ncard : ℝ) +
        ({ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧
          ∃ k : ℕ, 3 ≤ k ∧ (k : ℝ) < Real.log X / (2 * Real.log 2) ∧
            ((ℓ : ℤ) ∈ X2k R k ∨ (-(ℓ : ℤ)) ∈ X2k R k)}.ncard : ℝ)) := by linarith
    _ ≤ 1 + (C₁ * X ^ ((13 : ℝ) / 22) + (E2 X : ℝ) +
        (C₂ * X ^ ((6 : ℝ) / 11) + (E4 X : ℝ)) +
        C₃ * (X ^ ((9 : ℝ) / 10) * Real.log X)) := by
          linarith [hk1 X hX₁, hk2 X hX₂, hk3 X hX₃]
    _ = C₃ * (X ^ ((9 : ℝ) / 10) * Real.log X) +
        C₁ * X ^ ((13 : ℝ) / 22) + C₂ * X ^ ((6 : ℝ) / 11) +
        (E2 X : ℝ) + (E4 X : ℝ) + 1 := by ring
    _ ≤ (C₁ + C₂ + C₃ + 1) * (X ^ ((9 : ℝ) / 10) * Real.log X +
        X ^ ((13 : ℝ) / 22) + X ^ ((6 : ℝ) / 11) +
        (E2 X : ℝ) + (E4 X : ℝ)) := by
          have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
          have hX1322 := Real.rpow_nonneg hXpos.le ((13 : ℝ) / 22)
          have hX611 := Real.rpow_nonneg hXpos.le ((6 : ℝ) / 11)
          have h_one : 1 ≤ X ^ ((9 : ℝ) / 10) * Real.log X := by
            have hX1' : (1 : ℝ) ≤ X := le_trans (Real.one_lt_exp_iff.mpr one_pos).le hXe
            have hlog : 1 ≤ Real.log X := by
              rw [← Real.log_exp 1]
              exact Real.log_le_log (Real.exp_pos 1) hXe
            have hrpow := Real.one_le_rpow hX1' (by norm_num : (0 : ℝ) ≤ 9 / 10)
            exact le_trans (by norm_num) (mul_le_mul hrpow hlog zero_le_one (by linarith))
          have hlog' : (0 : ℝ) ≤ X ^ ((9 : ℝ) / 10) * Real.log X := by linarith
          nlinarith [Nat.cast_nonneg (α := ℝ) (E2 X),
                     Nat.cast_nonneg (α := ℝ) (E4 X),
                     mul_nonneg hC₁_pos.le hX1322,
                     mul_nonneg hC₂_pos.le hX611,
                     mul_nonneg hC₃_pos.le hlog',
                     mul_nonneg hC₁_pos.le hlog',
                     mul_nonneg hC₂_pos.le hlog']
/-! ## Counting E₂ elements: fiber bound -/

lemma at_most_one_pos_sq_near (M h : ℤ) (hM : h ^ 2 < M) (hh : 2 ≤ h)
    (y₁ y₂ : ℤ) (hy₁_pos : 0 < y₁) (hy₂_pos : 0 < y₂)
    (hy₁_lb : M - h ≤ y₁ ^ 2) (hy₁_ub : y₁ ^ 2 ≤ M + h)
    (hy₂_lb : M - h ≤ y₂ ^ 2) (hy₂_ub : y₂ ^ 2 ≤ M + h) :
    y₁ = y₂ := by
  by_contra h_ne
  rcases lt_or_gt_of_ne h_ne with h_lt | h_lt
  · have hy₁_ge_h : h ≤ y₁ := by
      by_contra h_neg
      push_neg at h_neg
      nlinarith [sq_nonneg (y₁ - (h - 1))]
    nlinarith [sq_nonneg (y₂ - y₁ - 1)]
  · have hy₂_ge_h : h ≤ y₂ := by
      by_contra h_neg
      push_neg at h_neg
      nlinarith [sq_nonneg (y₂ - (h - 1))]
    nlinarith [sq_nonneg (y₁ - y₂ - 1)]

lemma sq_interval_ncard_le_two (M h : ℤ) (hM : h ^ 2 < M) (hh : 2 ≤ h) :
    {y : ℤ | M - h ≤ y ^ 2 ∧ y ^ 2 ≤ M + h}.ncard ≤ 2 := by
  have hMh_pos : 0 < M - h := by nlinarith
  set S := {y : ℤ | M - h ≤ y ^ 2 ∧ y ^ 2 ≤ M + h} with hS_def
  set S_pos := {y : ℤ | 0 < y ∧ M - h ≤ y ^ 2 ∧ y ^ 2 ≤ M + h} with hS_pos_def
  set S_neg := {y : ℤ | y < 0 ∧ M - h ≤ y ^ 2 ∧ y ^ 2 ≤ M + h} with hS_neg_def
  have hS_eq : S = S_pos ∪ S_neg := by
    ext y
    simp only [hS_def, hS_pos_def, hS_neg_def, Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro ⟨h1, h2⟩
      rcases lt_trichotomy y 0 with hy | hy | hy
      · right
        exact ⟨hy, h1, h2⟩
      · subst hy
        simp at h1
        linarith
      · left
        exact ⟨hy, h1, h2⟩
    · rintro (⟨-, h1, h2⟩ | ⟨-, h1, h2⟩) <;> exact ⟨h1, h2⟩
  rw [hS_eq]
  have hS_pos_le : S_pos.ncard ≤ 1 := by
    rw [Set.ncard_le_one_iff (by
      apply Set.Finite.subset (Set.finite_Icc 0 (M + h))
      intro y ⟨hy, _, hy2⟩
      simp only [Set.mem_Icc]
      exact ⟨by linarith, by nlinarith [show y * 1 ≤ y * y by nlinarith]⟩)]
    intro a b ha hb
    simp only [hS_pos_def, Set.mem_setOf_eq] at ha hb
    exact at_most_one_pos_sq_near M h hM hh a b ha.1 hb.1 ha.2.1 ha.2.2 hb.2.1 hb.2.2
  have hS_neg_le : S_neg.ncard ≤ 1 := by
    rw [Set.ncard_le_one_iff (by
      apply Set.Finite.subset (Set.finite_Icc (-(M + h)) 0)
      intro y ⟨hy, _, hy2⟩
      simp only [Set.mem_Icc]
      exact ⟨by nlinarith [sq_nonneg y], le_of_lt hy⟩)]
    intro a b ha hb
    simp only [hS_neg_def, Set.mem_setOf_eq] at ha hb
    have := at_most_one_pos_sq_near M h hM hh (-a) (-b)
      (by linarith [ha.1]) (by linarith [hb.1])
      (by rw [neg_sq]; exact ha.2.1) (by rw [neg_sq]; exact ha.2.2)
      (by rw [neg_sq]; exact hb.2.1) (by rw [neg_sq]; exact hb.2.2)
    linarith
  linarith [Set.ncard_union_le S_pos S_neg]

lemma E2_y_count_bounded :
    ∃ Cy : ℕ, 0 < Cy ∧ ∃ X₂ : ℝ, 0 < X₂ ∧
      ∀ X : ℝ, X₂ < X → ∀ x : ℕ+, (x : ℝ) > X ^ ((2 : ℝ) / 11) →
        {y : ℤ | (x, y) ∈ E2_set X}.ncard ≤ Cy := by
  refine ⟨8, by norm_num, 2, by norm_num, fun X hX x hx => ?_⟩
  set M : ℤ := (↑(x : ℕ) : ℤ) ^ 11 with hM_def
  set h : ℤ := ⌊X⌋ with hh_def
  have hX_pos : (0 : ℝ) < X := by linarith
  have hh_ge_2 : 2 ≤ h := by
    rw [hh_def]; exact Int.le_floor.mpr (by exact_mod_cast (show (2 : ℝ) ≤ X by linarith))
  have h_fiber_sub : {y : ℤ | (x, y) ∈ E2_set X} ⊆
      {y : ℤ | M - h ≤ y ^ 2 ∧ y ^ 2 ≤ M + h} := by
    intro y hy
    simp only [E2_set, Set.mem_setOf_eq] at hy
    obtain ⟨_, _, hy_ub⟩ := hy
    have h_int_bound : |M - y ^ 2| ≤ h := by
      rw [hh_def]; refine Int.le_floor.mpr ?_
      rw [show (↑|M - y ^ 2| : ℝ) = |↑M - (↑y : ℝ) ^ 2| by rw [Int.cast_abs]; push_cast; ring_nf]
      convert hy_ub using 2
      simp [hM_def]
    exact ⟨by linarith [abs_le.mp h_int_bound], by linarith [abs_le.mp h_int_bound]⟩
  have hM_gt_h_sq : h ^ 2 < M := by
    have hx11_gt_X2 : X ^ 2 < (↑(x : ℕ) : ℝ) ^ 11 := by
      rw [show X ^ 2 = (X ^ ((2 : ℝ) / 11)) ^ 11 by
        rw [← Real.rpow_natCast (X ^ ((2:ℝ)/11)) 11, ← Real.rpow_mul hX_pos.le]; norm_num]
      exact pow_lt_pow_left₀ hx (by positivity) (by norm_num : 11 ≠ 0)
    exact_mod_cast show (h : ℝ) ^ 2 < (↑(x : ℕ) : ℝ) ^ 11 from lt_of_le_of_lt
      (sq_le_sq₀ (by exact_mod_cast le_trans (by norm_num : (0 : ℤ) ≤ 2) hh_ge_2) hX_pos.le
        |>.mpr (Int.floor_le X)) hx11_gt_X2
  have h_sup_finite : {y : ℤ | M - h ≤ y ^ 2 ∧ y ^ 2 ≤ M + h}.Finite :=
    Set.Finite.subset (Set.finite_Icc (-(M + h)) (M + h))
      (fun y ⟨_, hy_ub⟩ => Set.mem_Icc.mpr ⟨by nlinarith [sq_nonneg y], by nlinarith [sq_nonneg y]⟩)
  calc {y : ℤ | (x, y) ∈ E2_set X}.ncard
      ≤ {y : ℤ | M - h ≤ y ^ 2 ∧ y ^ 2 ≤ M + h}.ncard :=
        Set.ncard_le_ncard h_fiber_sub h_sup_finite
    _ ≤ 2 := sq_interval_ncard_le_two M h hM_gt_h_sq hh_ge_2
    _ ≤ 8 := by norm_num

lemma ncard_le_of_fiber_bound {α β : Type*}
    (S : Set (α × β))
    (N M : ℕ)
    (hfin : S.Finite)
    (hproj : (Prod.fst '' S).ncard ≤ N)
    (hfiber : ∀ a, {b | (a, b) ∈ S}.ncard ≤ M) :
    S.ncard ≤ N * M := by
  classical
  set Sf := hfin.toFinset with hSf_def
  rw [Set.ncard_eq_toFinset_card S hfin]
  set projF := Sf.image Prod.fst
  have hSf_sub : Sf ⊆ projF.biUnion (fun a => Sf.filter (fun p => p.1 = a)) := by
    intro ⟨a, b⟩ hab
    rw [Finset.mem_biUnion]
    exact ⟨a, Finset.mem_image_of_mem _ hab, Finset.mem_filter.mpr ⟨hab, rfl⟩⟩
  have hfiber_card : ∀ a ∈ projF, (Sf.filter (fun p => p.1 = a)).card ≤ M := by
    intro a _
    have hinj : Set.InjOn Prod.snd (↑(Sf.filter (fun p => p.1 = a)) : Set (α × β)) := by
      intro ⟨a1, b1⟩ h1 ⟨a2, b2⟩ h2 hb
      simp only [Finset.mem_coe, Finset.mem_filter] at h1 h2
      exact Prod.ext (h1.2.trans h2.2.symm) hb
    have hsub_fiber : ↑(Finset.image Prod.snd (Sf.filter (fun p => p.1 = a))) ⊆
        ({b | (a, b) ∈ S} : Set β) := by
      intro b hb
      simp only [Finset.coe_image, Finset.coe_filter, Set.mem_image, Set.mem_setOf_eq] at hb
      obtain ⟨⟨a', b'⟩, ⟨hmem, ha'⟩, hb'⟩ := hb
      rw [Set.Finite.mem_toFinset] at hmem
      simp at ha' hb'
      rw [← ha', ← hb']
      exact hmem
    calc (Sf.filter (fun p => p.1 = a)).card
        ≤ (Finset.image Prod.snd (Sf.filter (fun p => p.1 = a))).card := by
            rw [Finset.card_image_of_injOn hinj]
      _ = (↑(Finset.image Prod.snd (Sf.filter (fun p => p.1 = a))) : Set β).ncard := by
            rw [Set.ncard_coe_finset]
      _ ≤ ({b | (a, b) ∈ S} : Set β).ncard :=
            Set.ncard_le_ncard hsub_fiber
              (Set.Finite.subset (hfin.image Prod.snd) (fun b hb => ⟨⟨a, b⟩, hb, rfl⟩))
      _ ≤ M := hfiber a
  calc Sf.card
      ≤ (projF.biUnion (fun a => Sf.filter (fun p => p.1 = a))).card :=
        Finset.card_le_card hSf_sub
    _ ≤ projF.card * M := Finset.card_biUnion_le_card_mul _ _ M hfiber_card
    _ ≤ N * M := by
        apply Nat.mul_le_mul_right
        calc projF.card = (Prod.fst '' S).ncard := by
              rw [← Set.ncard_coe_finset]
              congr 1
              ext a
              simp [projF, Sf, Set.mem_image]
          _ ≤ N := hproj

lemma E2_proj_ncard_le (X B : ℝ) (_hB : 0 < B)
    (hx_bound : ∀ p ∈ E2_set X, (p.1 : ℝ) ≤ B) :
    (Prod.fst '' E2_set X).ncard ≤ ⌈B⌉₊ := by
  apply le_trans (Set.ncard_le_ncard_of_injOn (fun x : ℕ+ => (x : ℕ))
    (s := Prod.fst '' E2_set X) (t := ↑(Finset.Icc 1 ⌈B⌉₊))
    ?maps_to ?inj_on (Finset.finite_toSet _))
  case inj_on =>
    intro x _ y _ hxy
    exact PNat.coe_injective hxy
  case maps_to =>
    intro x hx
    simp only [Finset.coe_Icc, Set.mem_Icc]
    obtain ⟨p, hp, rfl⟩ := hx
    exact ⟨p.1.pos, by exact_mod_cast le_trans (hx_bound p hp) (Nat.le_ceil B)⟩
  · rw [Set.ncard_eq_toFinset_card', Finset.toFinset_coe, Nat.card_Icc]
    omega

lemma E2_combine_final (η : ℝ) (hη : 0 < η)
    (Cx : ℝ) (hCx : 0 < Cx) (Cy : ℕ) (hCy : 0 < Cy)
    (X : ℝ) (hX1 : 1 ≤ X)
    (hx : ∀ p ∈ E2_set X, (p.1 : ℝ) ≤ Cx * X ^ ((4 : ℝ) / 9 + η / 2))
    (hy : ∀ x : ℕ+, {y : ℤ | (x, y) ∈ E2_set X}.ncard ≤ Cy) :
    (E2 X : ℝ) ≤ (Cx * X ^ ((4 : ℝ) / 9 + η) + 1) * Cy := by
  set B := Cx * X ^ ((4 : ℝ) / 9 + η / 2) with hB_def
  have hB_pos : 0 < B := by positivity
  by_cases hfin : (E2_set X).Finite
  · have h_cast : (E2 X : ℝ) ≤ (⌈B⌉₊ : ℝ) * (Cy : ℝ) := by
      exact_mod_cast ncard_le_of_fiber_bound (E2_set X) ⌈B⌉₊ Cy hfin
        (E2_proj_ncard_le X B hB_pos hx) hy
    calc (E2 X : ℝ)
      ≤ (⌈B⌉₊ : ℝ) * (Cy : ℝ) := h_cast
      _ ≤ (B + 1) * (Cy : ℝ) :=
          mul_le_mul_of_nonneg_right (le_of_lt (Nat.ceil_lt_add_one hB_pos.le)) (Nat.cast_nonneg Cy)
      _ ≤ (Cx * X ^ ((4 : ℝ) / 9 + η) + 1) * (Cy : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg Cy)
          linarith [mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hX1 (show (4 : ℝ) / 9 + η / 2 ≤ 4 / 9 + η by linarith))
            hCx.le]
  · unfold E2
    rw [Set.Infinite.ncard hfin, Nat.cast_zero]
    positivity

lemma E2_combine_bounds (η : ℝ) (hη : 0 < η)
    (Cx : ℝ) (hCx : 0 < Cx) (X₁ : ℝ) (hX₁ : 0 < X₁)
    (hx_bound : ∀ X : ℝ, X₁ < X → ∀ (p : ℕ+ × ℤ), p ∈ E2_set X →
      (p.1 : ℝ) ≤ Cx * X ^ ((4 : ℝ) / 9 + η / 2))
    (Cy : ℕ) (hCy : 0 < Cy) (X₂ : ℝ) (_hX₂ : 0 < X₂)
    (hy_bound : ∀ X : ℝ, X₂ < X → ∀ x : ℕ+, (x : ℝ) > X ^ ((2 : ℝ) / 11) →
      {y : ℤ | (x, y) ∈ E2_set X}.ncard ≤ Cy) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ X : ℝ, X₀ < X →
        (E2 X : ℝ) ≤ C * X ^ ((4 : ℝ) / 9 + η) := by
  refine ⟨(Cx + 1) * Cy, by positivity, max X₁ (max X₂ 1), by positivity, ?_⟩
  intro X hX
  have hX1 : X₁ < X := lt_of_le_of_lt (le_max_left _ _) hX
  have hX2 : X₂ < X := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hX_ge1 : 1 ≤ X := le_of_lt (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hX)
  have hfiber : ∀ x : ℕ+, {y : ℤ | (x, y) ∈ E2_set X}.ncard ≤ Cy := by
    intro x
    by_cases hx : (x : ℝ) > X ^ ((2 : ℝ) / 11)
    · exact hy_bound X hX2 x hx
    · rw [show {y : ℤ | (x, y) ∈ E2_set X} = ∅ from
        Set.eq_empty_of_forall_notMem fun y hy => hx (by exact_mod_cast hy.1), Set.ncard_empty]
      exact Nat.zero_le Cy
  have habsorb : (Cx * X ^ ((4 : ℝ) / 9 + η) + 1) * Cy ≤
      (Cx + 1) * Cy * X ^ ((4 : ℝ) / 9 + η) := by
    have h1 : (1 : ℝ) ≤ X ^ ((4 : ℝ) / 9 + η) := Real.one_le_rpow (by linarith) (by positivity)
    have h2 : (Cx * X ^ ((4 : ℝ) / 9 + η) + 1 : ℝ) ≤ (Cx + 1 : ℝ) * X ^ ((4 : ℝ) / 9 + η) := by
      nlinarith [mul_nonneg hCx.le (show (0 : ℝ) ≤ X ^ ((4 : ℝ) / 9 + η) by positivity)]
    exact le_trans (mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg Cy))
      (le_of_eq (by ring))
  linarith [E2_combine_final η hη Cx hCx Cy hCy X hX_ge1 (hx_bound X hX1) hfiber]
/-! ## Counting E₄ elements: fiber bound -/

lemma sqrt_diff_lt_four (a c : ℝ) (_hc : 0 < c) (hac : c < a)
    (hkey : c ^ 2 / 16 < a - c) :
    Real.sqrt (a + c) - Real.sqrt (a - c) < 4 := by
  have hac' : 0 < a - c := by linarith
  have hsqrt_pos : 0 < Real.sqrt (a - c) + 4 := by positivity
  suffices h : Real.sqrt (a + c) < Real.sqrt (a - c) + 4 by linarith
  rw [Real.sqrt_lt' hsqrt_pos, add_sq, Real.sq_sqrt (le_of_lt hac')]
  by_cases hc8 : c ≤ 8
  · have : 0 < Real.sqrt (a - c) := Real.sqrt_pos_of_pos hac'
    nlinarith
  · push_neg at hc8
    have h1 : ((c - 8) / 4) ^ 2 < a - c := by nlinarith
    have h2 : (c - 8) / 4 < Real.sqrt (a - c) := Real.lt_sqrt_of_sq_lt h1
    nlinarith

lemma x22_gt_X2 (X : ℝ) (hX : 1 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((1 : ℝ) / 11)) :
    (x : ℝ) ^ 22 > X ^ 2 := by
  have := pow_lt_pow_left₀ hx (by positivity : (0 : ℝ) ≤ X ^ ((1 : ℝ) / 11)) (by norm_num : 22 ≠ 0)
  linarith [show (X ^ ((1 : ℝ) / 11)) ^ (22 : ℕ) = X ^ (2 : ℕ) by
    rw [← Real.rpow_natCast (X ^ ((1 : ℝ) / 11)) 22, ← Real.rpow_mul (by linarith : (0:ℝ) ≤ X)]; norm_num]

lemma five_x22_gt_four_X (X : ℝ) (hX : 1 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((1 : ℝ) / 11)) :
    5 * (x : ℝ) ^ 22 > 4 * X := by
  nlinarith [x22_gt_X2 X hX x hx]

lemma pos_u_count (X : ℝ) (hX : 1 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((1 : ℝ) / 11)) :
    {u : ℤ | 0 < u ∧ 1 ≤ |u ^ 2 - 5 * (↑↑x : ℤ) ^ 22| ∧
      (|u ^ 2 - 5 * (↑↑x : ℤ) ^ 22| : ℝ) ≤ 4 * X}.ncard ≤ 5 := by
  set S_pos := {u : ℤ | 0 < u ∧ 1 ≤ |u ^ 2 - 5 * (↑↑x : ℤ) ^ 22| ∧
    (|u ^ 2 - 5 * (↑↑x : ℤ) ^ 22| : ℝ) ≤ 4 * X}
  set a := 5 * (↑↑x : ℝ) ^ 22
  set c := 4 * X
  set lo : ℤ := max 1 ⌈Real.sqrt (a - c)⌉
  set hi : ℤ := lo + 4
  have hc_pos : 0 < c := by positivity
  have hca : c < a := five_x22_gt_four_X X hX x hx
  have hsqrt_diff : Real.sqrt (a + c) - Real.sqrt (a - c) < 4 := by
    apply sqrt_diff_lt_four a c hc_pos hca
    nlinarith [x22_gt_X2 X hX x hx]
  have hsub : S_pos ⊆ ↑(Finset.Icc lo hi) := by
    intro u ⟨hu_pos, _, h2⟩
    simp only [Finset.coe_Icc, Set.mem_Icc]
    simp only [Int.cast_natCast] at h2
    have hab := abs_le.mp (show |(↑u : ℝ) ^ 2 - a| ≤ c from h2)
    have hu_pos' : (0 : ℝ) < (u : ℤ) := Int.cast_pos.mpr hu_pos
    have hu_le : (u : ℝ) ≤ Real.sqrt (a + c) := by
      rw [← Real.sqrt_sq hu_pos'.le]; exact Real.sqrt_le_sqrt (by linarith [hab.2])
    have hu_ge : Real.sqrt (a - c) ≤ (u : ℝ) := by
      rw [← Real.sqrt_sq hu_pos'.le]; exact Real.sqrt_le_sqrt (by linarith [hab.1])
    exact ⟨max_le (by omega) (Int.ceil_le.mpr (by exact_mod_cast hu_ge)), by
      exact_mod_cast (show (u : ℝ) < (lo : ℤ) + 4 from
        calc (u : ℝ) ≤ Real.sqrt (a + c) := hu_le
          _ < Real.sqrt (a - c) + 4 := by linarith [hsqrt_diff]
          _ ≤ ↑⌈Real.sqrt (a - c)⌉ + 4 := by linarith [Int.le_ceil (Real.sqrt (a - c))]
          _ ≤ (lo : ℝ) + 4 := by
              linarith [show (⌈Real.sqrt (a - c)⌉ : ℝ) ≤ (lo : ℝ) by
                exact_mod_cast le_max_right 1 ⌈Real.sqrt (a - c)⌉]).le⟩
  calc S_pos.ncard ≤ (↑(Finset.Icc lo hi) : Set ℤ).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = (Finset.Icc lo hi).card := Set.ncard_coe_finset _
    _ = (hi + 1 - lo).toNat := Int.card_Icc lo hi
    _ = 5 := by
        simp [hi]
        omega

lemma neg_u_count (X : ℝ) (hX : 1 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((1 : ℝ) / 11)) :
    {u : ℤ | u < 0 ∧ 1 ≤ |u ^ 2 - 5 * (↑↑x : ℤ) ^ 22| ∧
      (|u ^ 2 - 5 * (↑↑x : ℤ) ^ 22| : ℝ) ≤ 4 * X}.ncard ≤ 5 := by
  set S_neg := {u : ℤ | u < 0 ∧ 1 ≤ |u ^ 2 - 5 * (↑↑x : ℤ) ^ 22| ∧
    (|u ^ 2 - 5 * (↑↑x : ℤ) ^ 22| : ℝ) ≤ 4 * X}
  set S_pos := {u : ℤ | 0 < u ∧ 1 ≤ |u ^ 2 - 5 * (↑↑x : ℤ) ^ 22| ∧
    (|u ^ 2 - 5 * (↑↑x : ℤ) ^ 22| : ℝ) ≤ 4 * X}
  have h_eq : S_neg = (fun u => -u) '' S_pos := by
    ext u
    simp only [Set.mem_image]
    constructor
    · intro ⟨hu_neg, h1, h2⟩
      exact ⟨-u, ⟨by omega, by rwa [neg_sq], by rwa [Int.cast_neg, neg_sq]⟩, by ring⟩
    · rintro ⟨v, ⟨hv_pos, h1, h2⟩, rfl⟩
      exact ⟨by omega, by rwa [neg_sq], by rwa [Int.cast_neg, neg_sq]⟩
  rw [h_eq, Set.ncard_image_of_injOn (fun a _ b _ h => by simp only [neg_inj] at h; exact h)]
  exact pos_u_count X hX x hx

lemma target_subset_pos_neg (X : ℝ) (hX : 1 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((1 : ℝ) / 11)) :
    {u : ℤ | 1 ≤ |u ^ 2 - 5 * (↑↑x : ℤ) ^ 22| ∧
      (|u ^ 2 - 5 * (↑↑x : ℤ) ^ 22| : ℝ) ≤ 4 * X} ⊆
    {u : ℤ | 0 < u ∧ 1 ≤ |u ^ 2 - 5 * (↑↑x : ℤ) ^ 22| ∧
      (|u ^ 2 - 5 * (↑↑x : ℤ) ^ 22| : ℝ) ≤ 4 * X} ∪
    {u : ℤ | u < 0 ∧ 1 ≤ |u ^ 2 - 5 * (↑↑x : ℤ) ^ 22| ∧
      (|u ^ 2 - 5 * (↑↑x : ℤ) ^ 22| : ℝ) ≤ 4 * X} := by
  intro u ⟨h1, h2⟩
  rcases lt_trichotomy u 0 with hu | rfl | hu
  · exact Set.mem_union_right _ ⟨hu, h1, h2⟩
  · simp only [Int.cast_natCast, Int.cast_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_sub, abs_neg] at h2
    linarith [five_x22_gt_four_X X hX x hx,
      abs_of_pos (show (0 : ℝ) < 5 * (↑↑x : ℝ) ^ 22 by positivity)]
  · exact Set.mem_union_left _ ⟨hu, h1, h2⟩

lemma pos_neg_finite (X : ℝ) (_hX : 1 < X) (x : ℕ+)
    (_hx : (x : ℝ) > X ^ ((1 : ℝ) / 11)) :
    ({u : ℤ | 0 < u ∧ 1 ≤ |u ^ 2 - 5 * (↑↑x : ℤ) ^ 22| ∧
      (|u ^ 2 - 5 * (↑↑x : ℤ) ^ 22| : ℝ) ≤ 4 * X} ∪
    {u : ℤ | u < 0 ∧ 1 ≤ |u ^ 2 - 5 * (↑↑x : ℤ) ^ 22| ∧
      (|u ^ 2 - 5 * (↑↑x : ℤ) ^ 22| : ℝ) ≤ 4 * X}).Finite := by
  set N : ℤ := ⌊Real.sqrt (5 * (x : ℝ) ^ 22 + 4 * X)⌋ + 1
  apply Set.Finite.subset (Set.finite_Icc (-N) N)
  intro u hu
  have h2 : (|u ^ 2 - 5 * (↑↑x : ℤ) ^ 22| : ℝ) ≤ 4 * X := by
    simp only [Set.mem_union, Set.mem_setOf_eq] at hu
    rcases hu with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> exact h
  have hbnd : (u : ℝ) ^ 2 ≤ 5 * (↑↑x : ℝ) ^ 22 + 4 * X := by
    simp only [Int.cast_natCast] at h2
    linarith [(abs_le.mp (show |(↑u : ℝ) ^ 2 - 5 * (↑↑x : ℝ) ^ 22| ≤ 4 * X from h2)).2]
  have habs := abs_le.mp (Real.abs_le_sqrt hbnd)
  simp only [Set.mem_Icc]
  constructor <;> linarith [show (u : ℤ) ≤ N from
    calc u = ⌊((u : ℤ) : ℝ)⌋ := (Int.floor_intCast u).symm
      _ ≤ ⌊Real.sqrt (5 * (↑↑x : ℝ) ^ 22 + 4 * X)⌋ := Int.floor_le_floor (by exact_mod_cast habs.2)
      _ ≤ N := le_add_of_nonneg_right (by norm_num),
    show (-u : ℤ) ≤ N from
    calc (-u : ℤ) = ⌊((-u : ℤ) : ℝ)⌋ := (Int.floor_intCast (-u)).symm
      _ ≤ ⌊Real.sqrt (5 * (↑↑x : ℝ) ^ 22 + 4 * X)⌋ := Int.floor_le_floor (by push_cast; linarith [habs.1])
      _ ≤ N := le_add_of_nonneg_right (by norm_num)]

lemma E4_u_count_per_x (X : ℝ) (hX : 1 < X) (x : ℕ+)
    (hx : (x : ℝ) > X ^ ((1 : ℝ) / 11)) :
    {u : ℤ | 1 ≤ |u ^ 2 - 5 * (↑↑x : ℤ) ^ 22| ∧
      (|u ^ 2 - 5 * (↑↑x : ℤ) ^ 22| : ℝ) ≤ 4 * X}.ncard ≤ 10 :=
  le_trans (le_trans
    (Set.ncard_le_ncard (target_subset_pos_neg X hX x hx) (pos_neg_finite X hX x hx))
    (Set.ncard_union_le _ _))
    (le_trans (Nat.add_le_add (pos_u_count X hX x hx) (neg_u_count X hX x hx)) (by norm_num))

lemma E4_set_finite_of_x_bound (X B : ℝ) (_hB : 0 < B)
    (hbound : ∀ p ∈ E4_set X, (p.1 : ℝ) ≤ B) :
    (E4_set X).Finite := by
  set N := ⌈B⌉₊ with hN_def
  set M := ⌈5 * (N : ℝ) ^ 22 + 4 * |X|⌉₊ with hM_def
  have hfin : {p : ℕ+ × ℤ | (p.1 : ℕ) ≤ N ∧ p.2.natAbs ≤ M}.Finite := by
    apply Set.Finite.subset (Set.Finite.prod (Set.finite_Iio (⟨N + 1, by omega⟩ : ℕ+))
      (Set.finite_Icc (-(M : ℤ)) M))
    intro ⟨x, u⟩ ⟨hx, hu⟩
    simp only [Set.mem_prod, Set.mem_Iio, Set.mem_Icc]
    exact ⟨by exact_mod_cast Nat.lt_succ_of_le hx,
           by rw [← abs_le, Int.abs_eq_natAbs]; exact_mod_cast hu⟩
  apply hfin.subset
  intro ⟨x, u⟩ hxu
  simp only [Set.mem_setOf_eq] at hxu ⊢
  obtain ⟨_, _, hu_upper⟩ := hxu
  have hxB : (x : ℝ) ≤ B := hbound (x, u) ⟨‹_›, ‹_›, hu_upper⟩
  have hxN : (x : ℕ) ≤ N := by exact_mod_cast le_trans hxB (Nat.le_ceil B)
  refine ⟨hxN, ?_⟩
  have hu_sq_M : (u : ℝ) ^ 2 ≤ (M : ℝ) := le_trans
    (show (u : ℝ) ^ 2 ≤ 5 * (N : ℝ) ^ 22 + 4 * |X| by
      have : ((↑↑x : ℤ) : ℝ) ^ 22 ≤ (N : ℝ) ^ 22 := by gcongr; exact_mod_cast hxN
      linarith [(abs_le.mp hu_upper).2, le_abs_self X])
    (Nat.le_ceil _)
  exact_mod_cast le_trans (show (u.natAbs : ℝ) ≤ (u : ℝ) ^ 2 by
    rw [Nat.cast_natAbs]; push_cast; exact_mod_cast Int.natAbs_le_self_sq u) hu_sq_M

lemma E4_fiber_ncard_le (X : ℝ) (hX : 1 < X) (n : ℕ) :
    {p : ℕ+ × ℤ | p ∈ E4_set X ∧ (p.1 : ℕ) = n}.ncard ≤ 10 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [show {p : ℕ+ × ℤ | p ∈ E4_set X ∧ (p.1 : ℕ) = 0} = ∅ from
      Set.eq_empty_of_forall_notMem fun ⟨x, _⟩ ⟨_, h⟩ => x.pos.ne' h, Set.ncard_empty]
    exact Nat.zero_le _
  · set x : ℕ+ := ⟨n, hn⟩
    by_cases hle : (x : ℝ) ≤ X ^ ((1 : ℝ) / 11)
    · have : {p : ℕ+ × ℤ | p ∈ E4_set X ∧ (p.1 : ℕ) = n} = ∅ := by
        ext ⟨a, u⟩
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro hmem heq
        rw [show a = x from Subtype.ext heq] at hmem
        linarith [hmem.1]
      rw [this, Set.ncard_empty]
      exact Nat.zero_le _
    · push_neg at hle
      set U := {u : ℤ | 1 ≤ |u ^ 2 - 5 * (↑↑x : ℤ) ^ 22| ∧
          (|u ^ 2 - 5 * (↑↑x : ℤ) ^ 22| : ℝ) ≤ 4 * X}
      have hfiber_eq : {p : ℕ+ × ℤ | p ∈ E4_set X ∧ (p.1 : ℕ) = n} =
          (fun u => (x, u)) '' U := by
        ext ⟨a, u⟩
        simp only [Set.mem_image, Prod.mk.injEq, Set.mem_setOf_eq]
        constructor
        · intro ⟨hmem, heq⟩
          have hax : a = x := Subtype.ext heq
          subst hax
          exact ⟨u, ⟨hmem.2.1, hmem.2.2⟩, rfl, rfl⟩
        · intro ⟨v, hv, hax, huv⟩
          subst hax
          subst huv
          exact ⟨⟨hle, hv.1, hv.2⟩, rfl⟩
      rw [hfiber_eq, Set.ncard_image_of_injective U (fun _ _ h => (Prod.mk.inj h).2)]
      exact E4_u_count_per_x X hX x hle

lemma E4_ncard_le_floor_mul (X B : ℝ) (hX : 1 < X) (hB : 0 < B)
    (hbound : ∀ p ∈ E4_set X, (p.1 : ℝ) ≤ B) :
    E4 X ≤ 10 * ⌊B⌋₊ := by
  unfold E4
  have hfin := E4_set_finite_of_x_bound X B hB hbound
  have hsub : E4_set X ⊆ ⋃ (n ∈ Finset.Icc 1 ⌊B⌋₊),
      {p : ℕ+ × ℤ | p ∈ E4_set X ∧ (p.1 : ℕ) = n} := fun p hp =>
    Set.mem_iUnion.mpr ⟨(p.1 : ℕ), Set.mem_iUnion.mpr
      ⟨Finset.mem_Icc.mpr ⟨p.1.one_le, Nat.le_floor (hbound p hp)⟩, hp, rfl⟩⟩
  have hfin_union : (⋃ n ∈ Finset.Icc 1 ⌊B⌋₊,
    {p : ℕ+ × ℤ | p ∈ E4_set X ∧ (p.1 : ℕ) = n}).Finite :=
    Set.Finite.subset hfin (fun p hp => by
      simp only [Set.mem_iUnion] at hp
      obtain ⟨n, _, hp_mem, _⟩ := hp
      exact hp_mem)
  calc (E4_set X).ncard
      ≤ (⋃ n ∈ Finset.Icc 1 ⌊B⌋₊,
          {p : ℕ+ × ℤ | p ∈ E4_set X ∧ (p.1 : ℕ) = n}).ncard :=
        Set.ncard_le_ncard hsub hfin_union
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊B⌋₊,
          {p : ℕ+ × ℤ | p ∈ E4_set X ∧ (p.1 : ℕ) = n}.ncard :=
        Finset.set_ncard_biUnion_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊B⌋₊, 10 :=
        Finset.sum_le_sum fun n _ => E4_fiber_ncard_le X hX n
    _ = 10 * ⌊B⌋₊ := by
        simp [Finset.sum_const, smul_eq_mul]
        omega

lemma abc_bound_E4_with_alpha
    (habc : ABC) (ε : ℝ) (hε : 0 < ε) (hε2 : (10 : ℝ) - 12 * ε > 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ X : ℝ, X₀ < X →
        (E4 X : ℝ) ≤ C * X ^ ((2 + ε) / (10 - 12 * ε)) := by
  obtain ⟨C₂, hC₂, X₀, hX₀, hbound⟩ := abc_x_upper_bound habc ε hε hε2
  refine ⟨10 * C₂, by positivity, max X₀ 1, by positivity, fun X hX => ?_⟩
  rw [mul_assoc]
  set B := C₂ * X ^ ((2 + ε) / (10 - 12 * ε))
  have hX1 : 1 < X := lt_of_le_of_lt (le_max_right X₀ 1) hX
  have hB_pos : 0 < B := by positivity
  have hxb := hbound X (lt_of_le_of_lt (le_max_left X₀ 1) hX)
  calc (E4 X : ℝ) ≤ ↑(10 * ⌊B⌋₊) := Nat.cast_le.mpr (E4_ncard_le_floor_mul X B hX1 hB_pos hxb)
    _ = 10 * ↑⌊B⌋₊ := by
        push_cast
        ring
    _ ≤ 10 * B := mul_le_mul_of_nonneg_left (Nat.floor_le hB_pos.le) (by norm_num)
/-! ## Main theorems -/

theorem reduction_lemma (habc : ABC) (h54 : Proposition5_4 R) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ X : ℝ, X₀ < X →
        (S R X : ℝ) ≤ C * (X ^ ((9 : ℝ) / 10) * Real.log X +
          X ^ ((13 : ℝ) / 22) + X ^ ((6 : ℝ) / 11) +
          (E2 X : ℝ) + (E4 X : ℝ)) :=
  reduction_lemma_helper habc R h54

theorem abc_bound_E2 (habc : ABC) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ X : ℝ, X₀ < X →
        (E2 X : ℝ) ≤ C * X ^ ((4 : ℝ) / 9 + η) := by
  obtain ⟨Cx, hCx, X₁, hX₁, hx_bound⟩ := E2_x_bound habc η hη
  obtain ⟨Cy, hCy, X₂, hX₂, hy_bound⟩ := E2_y_count_bounded
  exact E2_combine_bounds η hη Cx hCx X₁ hX₁ hx_bound Cy hCy X₂ hX₂ hy_bound

theorem abc_bound_E4 (habc : ABC) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ X : ℝ, X₀ < X →
        (E4 X : ℝ) ≤ C * X ^ ((1 : ℝ) / 5 + η) := by
  obtain ⟨ε, hε, hε2, hα⟩ : ∃ ε : ℝ, 0 < ε ∧ (10 : ℝ) - 12 * ε > 0 ∧
      (2 + ε) / (10 - 12 * ε) ≤ 1 / 5 + η := by
    refine ⟨min (1/24) (η/10), lt_min (by norm_num) (by linarith), ?_, ?_⟩
    · linarith [min_le_left (1/24 : ℝ) (η/10)]
    · rw [div_le_iff₀ (by linarith [min_le_left (1/24 : ℝ) (η/10)])]
      nlinarith [min_le_left (1/24 : ℝ) (η/10), min_le_right (1/24 : ℝ) (η/10)]
  obtain ⟨C, hC, X₀, hX₀, hbound⟩ := abc_bound_E4_with_alpha habc ε hε hε2
  exact ⟨C, hC, max X₀ 1, by positivity, fun X hX =>
    le_trans (hbound X (lt_of_le_of_lt (le_max_left X₀ 1) hX))
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le
          (le_of_lt (lt_of_le_of_lt (le_max_right X₀ 1) hX)) hα) hC.le)⟩

theorem main_theorem (habc : ABC) (h54 : Proposition5_4 R) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ X : ℝ, X₀ < X →
        (S R X : ℝ) ≤ C * X ^ ((9 : ℝ) / 10) * Real.log X := by
  obtain ⟨C₀, hC₀, X₀_red, hX₀_red, hred⟩ := reduction_lemma (R := R) habc h54
  obtain ⟨C₂, hC₂, X₀_2, hX₀_2, hE2_bound⟩ := abc_bound_E2 habc (1/10) (by norm_num)
  obtain ⟨C₄, hC₄, X₀_4, hX₀_4, hE4_bound⟩ := abc_bound_E4 habc (1/10) (by norm_num)
  refine ⟨C₀ * (3 + C₂ + C₄), by positivity,
    max (max (max X₀_red X₀_2) (max X₀_4 (Real.exp 1))) 2, by positivity, ?_⟩
  intro X hX_big
  have hX_exp : Real.exp 1 < X :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hX_big
  have hX1 : 1 < X := lt_trans (Real.one_lt_exp_iff.mpr one_pos) hX_exp
  have hlog : 1 ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX_exp.le
  have h910_nn : (0 : ℝ) ≤ X ^ ((9 : ℝ) / 10) := Real.rpow_nonneg (by linarith) _
  have hS := hred X (lt_of_le_of_lt (le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) (le_max_left _ _))) hX_big)
  have hE2 := hE2_bound X (lt_of_le_of_lt (le_trans (le_max_right _ _)
    (le_trans (le_max_left _ _) (le_max_left _ _))) hX_big)
  have hE4 := hE4_bound X (lt_of_le_of_lt (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_left _ _))) hX_big)
  have absorb (e : ℝ) (he : e ≤ (9 : ℝ) / 10) : X ^ e ≤ X ^ ((9 : ℝ) / 10) * Real.log X :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hX1.le he) (le_mul_of_one_le_right h910_nn hlog)
  have hcomb : X ^ ((9 : ℝ) / 10) * Real.log X +
      X ^ ((13 : ℝ) / 22) + X ^ ((6 : ℝ) / 11) +
      (E2 X : ℝ) + (E4 X : ℝ) ≤
      (3 + C₂ + C₄) * (X ^ ((9 : ℝ) / 10) * Real.log X) := by
    have h910log_nn : (0 : ℝ) ≤ X ^ ((9 : ℝ) / 10) * Real.log X :=
      mul_nonneg h910_nn (le_trans (by norm_num) hlog)
    calc X ^ ((9 : ℝ) / 10) * Real.log X +
          X ^ ((13 : ℝ) / 22) + X ^ ((6 : ℝ) / 11) +
          (E2 X : ℝ) + (E4 X : ℝ)
        ≤ X ^ ((9 : ℝ) / 10) * Real.log X +
          (X ^ ((9 : ℝ) / 10) * Real.log X) +
          (X ^ ((9 : ℝ) / 10) * Real.log X) +
          (C₂ * (X ^ ((9 : ℝ) / 10) * Real.log X)) +
          (C₄ * (X ^ ((9 : ℝ) / 10) * Real.log X)) := by
            gcongr
            · exact absorb _ (by norm_num)
            · exact absorb _ (by norm_num)
            · exact le_trans hE2 (by gcongr; exact absorb _ (by norm_num))
            · exact le_trans hE4 (by gcongr; exact absorb _ (by norm_num))
        _ = (3 + C₂ + C₄) * (X ^ ((9 : ℝ) / 10) * Real.log X) := by ring
  calc (S R X : ℝ)
      ≤ C₀ * (X ^ ((9 : ℝ) / 10) * Real.log X +
          X ^ ((13 : ℝ) / 22) + X ^ ((6 : ℝ) / 11) +
          (E2 X : ℝ) + (E4 X : ℝ)) := hS
    _ ≤ C₀ * ((3 + C₂ + C₄) * (X ^ ((9 : ℝ) / 10) * Real.log X)) :=
        mul_le_mul_of_nonneg_left hcomb hC₀.le
    _ = C₀ * (3 + C₂ + C₄) * X ^ ((9 : ℝ) / 10) * Real.log X := by ring
