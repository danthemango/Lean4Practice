import Lean4PracticeWithMathlib.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- practice with https://www.youtube.com/watch?v=0QZI_m8WZ0Q

def PrimeNum (n : Nat) : Prop :=
  n ≥ 2 ∧ ∀ (m : Nat), m ∣ n → m = 1 ∨ m = n

def Rational (n : ℝ) : Prop :=
  ∃ (p q : ℝ), (p / q) = n

-- def Irrational ()

theorem not_prime1 : ¬ PrimeNum 1 := by
  unfold PrimeNum
  intro pr1
  obtain ⟨ h1, h2 ⟩ := pr1
  contradiction

-- theorem prime2 : PrimeNum 2 := by
--   unfold PrimeNum
--   constructor
--   left
--   intro m
--   intro pr2
  -- right

theorem not_prime9 : ¬ PrimeNum 9 := by
  unfold PrimeNum
  intro pr1
  obtain ⟨ h1, h2 ⟩ := pr1
  have hr3 := h2 3
  have div : 3 ∣ 9 := by decide
  have one_or_nine := hr3 div
  cases one_or_nine
  · contradiction
  · contradiction

#check Classical.em
#check irrational_sqrt_two
#check Real.rpow_mul
#check Real.sqrt_nonneg
#check irrational_iff_ne_rational

lemma sqrt2_to_sqrt2_to_sqrt2_is_two : (√2 ^ √2) ^ √2 = (2 : ℝ) := by
  have zero_le_sqrt2 : 0 ≤ √2 := by exact Real.sqrt_nonneg 2
  rw [← Real.rpow_mul zero_le_sqrt2 √2 √2]
  norm_num

lemma two_is_rat : Rational (2 : ℝ) := by
  unfold Rational
  use 2, 1
  norm_num

lemma sqrt2_rpow_mul_is_rational : Rational ((√2 ^ √2) ^ √2) := by
  rw [sqrt2_to_sqrt2_to_sqrt2_is_two]
  exact two_is_rat

lemma not_rat_is_irrat : ¬Rational (x : ℝ) -> Irrational (x : ℝ) := by
  -- by definition
  sorry

-- proceed with the proof that there exists two irrat numbers where irrat^irrat = rational
-- either sqrt2^sqrt2 is rational, then QED
-- or ((sqrt2^sqrt2)^sqrt2 is rational, since it's equal to 2)
theorem exist_irrat_pow_irrat_eq_rat :
  ∃ (a b : ℝ), Irrational a ∧ Irrational b ∧ Rational (a ^ b) := by
    have irrat_sqrt_two := irrational_sqrt_two
    by_cases rat_or_not : Rational (√2^√2)
    · use √2, √2
    have sqrt2_rpow_mul_is_rational := sqrt2_rpow_mul_is_rational
    have irrat_sq2_pow_sq2 : Irrational (√2 ^ √2) := by
      exact not_rat_is_irrat rat_or_not
    use √2^√2, √2
