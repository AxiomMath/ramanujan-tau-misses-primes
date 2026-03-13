import Mathlib

/-
# Problem: Bounding prime values of Ramanujan's tau function

Assuming the ABC conjecture and Xiong's Proposition 5.4, we prove that the counting function
$S(X) := \#\{\ell \le X : \ell \text{ prime}, |\tau(n)| = \ell \text{ for some } n \ge 1\}$
satisfies $S(X) = O(X^{9/10} \log X)$ as $X \to +\infty$.

The Ramanujan tau function $\tau$ is axiomatized (not concretely defined) via five properties:
Hecke multiplicativity, Hecke recurrence, parity, Deligne's bound, and non-unit property.

The domain of $\tau$ is the positive integers (ℕ+), matching the mathematical definition τ : ℤ_{≥1} → ℤ.
-/

open Filter Asymptotics

-- =====================================================================
-- Auxiliary: radical of a natural number = $\prod_{p \mid n} p$
-- =====================================================================
noncomputable def Nat.radical (n : ℕ) : ℕ :=
  if n = 0 then 0 else ∏ p ∈ n.primeFactors, p

-- =====================================================================
-- Definition 1: Ramanujan's tau function (axiomatic)
-- Domain: ℕ+ (positive integers), avoiding the problematic τ(0)
-- =====================================================================

/-- An axiomatic Ramanujan tau function: a function $\tau : \mathbb{N}^+ \to \mathbb{Z}$
satisfying Hecke multiplicativity, Hecke recurrence, parity, Deligne's bound,
and the non-unit property. -/
structure RamanujanTau where
  τ : ℕ+ → ℤ
  /-- Hecke multiplicativity: $\gcd(m,n)=1 \implies \tau(mn) = \tau(m)\tau(n)$ -/
  hecke_mult : ∀ m n : ℕ+, Nat.Coprime (m : ℕ) (n : ℕ) → τ (m * n) = τ m * τ n
  /-- Hecke recurrence: for $p$ prime and $m \ge 2$,
      $\tau(p^m) = \tau(p)\tau(p^{m-1}) - p^{11}\tau(p^{m-2})$ -/
  hecke_rec : ∀ (p : ℕ+), (p : ℕ).Prime → ∀ (m : ℕ), 2 ≤ m →
    τ (p ^ m) = τ p * τ (p ^ (m - 1)) - (↑(p : ℕ) : ℤ) ^ 11 * τ (p ^ (m - 2))
  /-- Parity: $\tau(n)$ is odd if and only if $n$ is an odd perfect square -/
  parity : ∀ n : ℕ+, ¬(2 ∣ τ n) ↔ (Odd (n : ℕ) ∧ IsSquare (n : ℕ))
  /-- Deligne's bound: $|\tau(p)| \le 2 p^{11/2}$ for $p$ prime -/
  deligne_bound : ∀ (p : ℕ+), (p : ℕ).Prime →
    (|τ p| : ℝ) ≤ 2 * (p : ℝ) ^ ((11 : ℝ) / 2)
  /-- Non-unit property: $\tau(n) \ne \pm 1$ for $n \ge 2$ -/
  non_unit : ∀ (n : ℕ+), 2 ≤ (n : ℕ) → τ n ≠ 1 ∧ τ n ≠ -1

variable (R : RamanujanTau)

-- =====================================================================
-- Definition 2: The counting function $S(X)$
-- $S(X) = \#\{\ell \le X : \ell \text{ prime}, |\tau(n)| = \ell \text{ for some } n \ge 1\}$
-- =====================================================================

/-- The set of positive primes $\ell \le X$ such that $|\tau(n)| = \ell$ for some $n \ge 1$. -/
noncomputable def S_set (X : ℝ) : Set ℕ :=
  {ℓ : ℕ | Nat.Prime ℓ ∧ (ℓ : ℝ) ≤ X ∧ ∃ n : ℕ+, (R.τ n).natAbs = ℓ}

/-- $S(X) = \#\{\ell \le X : \ell \text{ prime}, |\tau(n)| = \ell \text{ for some } n \ge 1\}$ -/
noncomputable def S (X : ℝ) : ℕ := (S_set R X).ncard

-- =====================================================================
-- Definition 3: The sets $E_2(X)$ and $E_4(X)$
-- Note: We explicitly enforce the domain constraint 1 ≤ x via ℕ+
-- =====================================================================

/-- $E_2(X) = \#\{(x,y) \in \mathbb{Z}_{\ge 1} \times \mathbb{Z} :
    x > X^{2/11}, 1 \le |x^{11} - y^2| \le X\}$

    We enforce x ∈ ℕ+ to ensure x ≥ 1 by definition. -/
noncomputable def E2_set (X : ℝ) : Set (ℕ+ × ℤ) :=
  {p : ℕ+ × ℤ | (p.1 : ℝ) > X ^ ((2 : ℝ) / 11) ∧
    1 ≤ |(↑p.1 : ℤ) ^ 11 - p.2 ^ 2| ∧
    (|(↑p.1 : ℤ) ^ 11 - p.2 ^ 2| : ℝ) ≤ X}

noncomputable def E2 (X : ℝ) : ℕ := (E2_set X).ncard

/-- $E_4(X) = \#\{(x,u) \in \mathbb{Z}_{\ge 1} \times \mathbb{Z} :
    x > X^{1/11}, 1 \le |u^2 - 5x^{22}| \le 4X\}$

    We enforce x ∈ ℕ+ to ensure x ≥ 1 by definition. -/
noncomputable def E4_set (X : ℝ) : Set (ℕ+ × ℤ) :=
  {p : ℕ+ × ℤ | (p.1 : ℝ) > X ^ ((1 : ℝ) / 11) ∧
    1 ≤ |p.2 ^ 2 - 5 * (↑p.1 : ℤ) ^ 22| ∧
    (|p.2 ^ 2 - 5 * (↑p.1 : ℤ) ^ 22| : ℝ) ≤ 4 * X}

noncomputable def E4 (X : ℝ) : ℕ := (E4_set X).ncard

-- =====================================================================
-- Definition 4: ABC Conjecture
-- For every $\varepsilon > 0$, there exists $K_\varepsilon > 0$ such that for all
-- coprime positive integers $a, b, c$ with $a + b = c$,
-- $c \le K_\varepsilon \cdot \mathrm{rad}(abc)^{1+\varepsilon}$.
-- =====================================================================

def ABC : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ K : ℝ, 0 < K ∧
      ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
        Nat.Coprime a b → a + b = c →
          (c : ℝ) ≤ K * ((Nat.radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε)

-- =====================================================================
-- Definition 5: Xiong's Proposition 5.4
-- Let $P = \{\pm \ell : \ell \text{ odd prime}\}$ and
-- $X_{2k} = \{\tau(p^{2k}) : p \text{ prime}\}$.
-- There exists $c_4 > 0$ such that for all $N > c_4$ and $3 \le k < \log N / (2 \log 2)$,
-- $\#(P \cap X_{2k} \cap [-N, N]) < N^{9/10}$.
-- =====================================================================

/-- The set of signed odd primes $P = \{\pm \ell : \ell \text{ is an odd prime}\}$ -/
def oddPrimesSigned : Set ℤ :=
  {z : ℤ | ∃ p : ℕ, Nat.Prime p ∧ p ≠ 2 ∧ (z = ↑p ∨ z = -↑p)}

/-- $X_{2k} = \{\tau(p^{2k}) : p \text{ is a positive prime}\}$ -/
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

-- =====================================================================
-- Main Statements
-- =====================================================================

/-- **Lemma 1 (Reduction lemma).** Assuming Proposition 5.4:
$S(X) \ll X^{9/10} \log X + X^{13/22} + X^{6/11} + E_2(X) + E_4(X)$. -/
theorem reduction_lemma (habc : ABC) (h54 : Proposition5_4 R) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ X : ℝ, X₀ < X →
        (S R X : ℝ) ≤ C * (X ^ ((9 : ℝ) / 10) * Real.log X +
          X ^ ((13 : ℝ) / 22) + X ^ ((6 : ℝ) / 11) +
          (E2 X : ℝ) + (E4 X : ℝ)) := by
  sorry

/-- **Lemma 2(i) (ABC bound on $E_2$).** Assuming ABC, for every $\eta > 0$,
$E_2(X) \ll_\eta X^{4/9+\eta}$. -/
theorem abc_bound_E2 (habc : ABC) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ X : ℝ, X₀ < X →
        (E2 X : ℝ) ≤ C * X ^ ((4 : ℝ) / 9 + η) := by
  sorry

/-- **Lemma 2(ii) (ABC bound on $E_4$).** Assuming ABC, for every $\eta > 0$,
$E_4(X) \ll_\eta X^{1/5+\eta}$. -/
theorem abc_bound_E4 (habc : ABC) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ X : ℝ, X₀ < X →
        (E4 X : ℝ) ≤ C * X ^ ((1 : ℝ) / 5 + η) := by
  sorry

/-- **Theorem 1 (Main theorem).** Assuming the ABC conjecture and Xiong's Proposition 5.4,
$S(X) = O(X^{9/10} \log X)$ as $X \to +\infty$.
Equivalently, there exist $C > 0$ and $X_0 > 0$ such that for all $X > X_0$,
$S(X) \le C \cdot X^{9/10} \cdot \log X$. -/
theorem main_theorem (habc : ABC) (h54 : Proposition5_4 R) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ X : ℝ, X₀ < X →
        (S R X : ℝ) ≤ C * X ^ ((9 : ℝ) / 10) * Real.log X := by
  sorry
