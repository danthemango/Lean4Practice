import Lean4PracticeWithMathlib.NaturalNumberGameBasic

-- note: this game will attempt to not use Nat
-- but i'll just use Nat to get used to it

-- x+1=y+1⟹x=y.
example (x y : Nat) : x + 1 = y + 1 → x = y := by
  intro h
  rw [← succ_inj x y]
  rw [succ_eq_add_one]
  rw [succ_eq_add_one]
  exact h

-- If x=y and x  =y then we can deduce a contradiction.
example (x y : Nat) (h1 : x = y) (h2 : x ≠ y) : False := by
  apply h2
  exact h1

-- Theorem zero_ne_one: 0  =1.
theorem zero_ne_one : (0 : Nat) ≠ 1 := by
  intro h
  rw [one_eq_succ_zero] at h
  apply zero_ne_succ 0
  exact h

-- Theorem one_ne_zero: 1  =0.
theorem one_ne_zero : (1 : Nat) ≠ 0 := by
  symm
  exact zero_ne_one

-- 2+2  =5.
example : Nat.succ (Nat.succ 0) + Nat.succ (Nat.succ 0) ≠ Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ 0)))) := by
  -- rw [add_succ]
  -- rw [add_succ]
  -- rw [add_zero]
  -- intro h
  -- apply succ_inj at h
  -- apply succ_inj at h
  -- apply succ_inj at h
  -- apply succ_inj at h
  -- apply zero_ne_succ 0
  -- exact h
  sorry
