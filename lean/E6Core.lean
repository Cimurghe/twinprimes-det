/-
  E6 core (twin-prime program, exp24). Roy Sulaiman, 2026-11-24.
  Conditional plumbing only: the analytic input HypC is a HYPOTHESIS, never an axiom.
  1. identity      : t(kt+2k+1) + 2 = (t+2)(kt+1)
  2. sign_split    : sgn N = sgn t * f(u) f(u+2k),  u = kt+1   (f completely multiplicative on ℕ⁺)
  3. dichotomy     : if f(u)f(u+2k) = -1, exactly one of the pairs (t,t+2), (N,N+2) has sign +1
  4. fake_refuted  : HypC f z  ⇒  arbitrarily large z-rough pairs with sgn = +1
  5. chi4_fails    : the χ₋₄ fake never fires on 3-rough configurations, so HypC χ₋₄ z is false (z ≥ 3)
-/
import Mathlib

namespace TwinE6

theorem identity (t k : ℕ) : t * (k * t + 2 * k + 1) + 2 = (t + 2) * (k * t + 1) := by ring

/-- sign of the pair (m, m+2) under f -/
def sgn (f : ℕ → ℤ) (m : ℕ) : ℤ := f m * f (m + 2)

/-- n has no prime factor below z -/
def Rough (z n : ℕ) : Prop := ∀ p, p.Prime → p ∣ n → z ≤ p

lemma rough_mul {z a b : ℕ} (ha : Rough z a) (hb : Rough z b) : Rough z (a * b) := by
  intro p hp hd
  rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
  exacts [ha p hp h, hb p hp h]

lemma rough_mono {z n : ℕ} (hz : 3 ≤ z) (h : Rough z n) : Rough 3 n :=
  fun p hp hd => le_trans hz (h p hp hd)

section General
variable (f : ℕ → ℤ) (hf : ∀ a b, a ≠ 0 → b ≠ 0 → f (a * b) = f a * f b)
  (hpm : ∀ n, f n = 1 ∨ f n = -1)

include hf in
theorem sign_split (t k : ℕ) (ht : t ≠ 0) :
    sgn f (t * (k * t + 2 * k + 1)) = sgn f t * (f (k * t + 1) * f (k * t + 1 + 2 * k)) := by
  unfold sgn
  have e : k * t + 2 * k + 1 = k * t + 1 + 2 * k := by ring
  rw [identity, hf t (k * t + 2 * k + 1) ht (by omega), hf (t + 2) (k * t + 1) (by omega) (by omega), e]
  ring

include hpm in
lemma sgn_pm (m : ℕ) : sgn f m = 1 ∨ sgn f m = -1 := by
  unfold sgn
  rcases hpm m with h | h <;> rcases hpm (m + 2) with h' | h' <;> simp [h, h']

include hf hpm in
theorem dichotomy (t k : ℕ) (ht : t ≠ 0) (hfire : f (k * t + 1) * f (k * t + 1 + 2 * k) = -1) :
    (sgn f t = 1 ∧ sgn f (t * (k * t + 2 * k + 1)) = -1) ∨
    (sgn f t = -1 ∧ sgn f (t * (k * t + 2 * k + 1)) = 1) := by
  rw [sign_split f hf t k ht, hfire]
  rcases sgn_pm f hpm t with h | h <;> simp [h]

/-- Hypothesis C(f, z): firing configurations exist at arbitrarily large t. -/
def HypC (z : ℕ) : Prop :=
  ∀ M, ∃ t k, M ≤ t ∧ Rough z t ∧ Rough z (t + 2) ∧ Rough z (k * t + 1) ∧
    Rough z (k * t + 1 + 2 * k) ∧ f (k * t + 1) * f (k * t + 1 + 2 * k) = -1

include hf hpm in
theorem fake_refuted (z : ℕ) (hC : HypC f z) :
    ∀ M, ∃ m, M ≤ m ∧ Rough z m ∧ Rough z (m + 2) ∧ sgn f m = 1 := by
  intro M
  obtain ⟨t, k, hM, ht, ht2, hu, hu2, hfire⟩ := hC (M + 1)
  have ht0 : t ≠ 0 := by omega
  rcases dichotomy f hf hpm t k ht0 hfire with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact ⟨t, by omega, ht, ht2, h1⟩
  · refine ⟨t * (k * t + 2 * k + 1), ?_, ?_, ?_, h2⟩
    · calc M ≤ t := by omega
        _ = t * 1 := (mul_one t).symm
        _ ≤ t * (k * t + 2 * k + 1) := Nat.mul_le_mul (le_refl t) (by omega)
    · have e : k * t + 2 * k + 1 = k * t + 1 + 2 * k := by ring
      rw [e]; exact rough_mul ht hu2
    · rw [identity]; exact rough_mul ht2 hu

end General

/-- Liouville λ(n) = (-1)^Ω(n) -/
def liou (n : ℕ) : ℤ := (-1) ^ (ArithmeticFunction.cardFactors n)

lemma liou_mul (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : liou (a * b) = liou a * liou b := by
  simp only [liou, ArithmeticFunction.cardFactors_mul ha hb, pow_add]

lemma liou_pm (n : ℕ) : liou n = 1 ∨ liou n = -1 := neg_one_pow_eq_or ℤ _

/-- The target instance: HypC for Liouville at roughness z gives z-rough pairs with λλ = +1. -/
theorem liouville_instance (z : ℕ) (hC : HypC liou z) :
    ∀ M, ∃ m, M ≤ m ∧ Rough z m ∧ Rough z (m + 2) ∧ liou m * liou (m + 2) = 1 :=
  fake_refuted liou liou_mul liou_pm z hC

/-- χ₋₄ as a function on ℕ -/
def chi4 (n : ℕ) : ℤ := if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0

lemma odd_of_rough3 {n : ℕ} (h : Rough 3 n) : n % 2 = 1 := by
  by_contra hc
  have h2 : 2 ∣ n := by omega
  have := h 2 Nat.prime_two h2
  omega

theorem chi4_never_fires (t k : ℕ) (ht : Rough 3 t) (hu : Rough 3 (k * t + 1)) :
    chi4 (k * t + 1) * chi4 (k * t + 1 + 2 * k) = 1 := by
  have h1 := odd_of_rough3 ht
  have h2 := odd_of_rough3 hu
  have hk : k % 2 = 0 := by
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · omega
    · exfalso
      obtain ⟨i, hi⟩ : ∃ i, t = 2 * i + 1 := ⟨t / 2, by omega⟩
      subst hj; subst hi
      have e : (2 * j + 1) * (2 * i + 1) + 1 = 2 * (2 * i * j + i + j + 1) := by ring
      rw [e] at h2
      omega
  obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
  have hmod : (2 * j * t + 1 + 2 * (2 * j)) % 4 = (2 * j * t + 1) % 4 := by omega
  have h4 : (2 * j * t + 1) % 4 = 1 ∨ (2 * j * t + 1) % 4 = 3 := by omega
  unfold chi4
  rw [hmod]
  rcases h4 with h | h <;> simp [h]

theorem chi4_fails_hypC (z : ℕ) (hz : 3 ≤ z) : ¬ HypC chi4 z := by
  intro h
  obtain ⟨t, k, -, ht, -, hu, -, hfire⟩ := h 0
  rw [chi4_never_fires t k (rough_mono hz ht) (rough_mono hz hu)] at hfire
  norm_num at hfire

end TwinE6
