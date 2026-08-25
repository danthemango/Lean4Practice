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

-- norm_num isn't working
theorem n_div_k (n : Nat) (k : Nat):  n ∣ k ↔ ∃ (c : Nat), n = c * k := by
  sorry

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

-- import from mathlib seems to be broken, so I'll pretend I have all knowledge


#check Classical.em
#check irrational_sqrt_two
#check Real.rpow_mul

-- proceed with the proof that there exists two irrat numbers where irrat^irrat = rational
