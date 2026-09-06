abbrev succ := Nat.succ
abbrev ℕ := Nat
abbrev MyNat := Nat
abbrev MyNat.succ := Nat.succ

-- addition world theorems
theorem zero_add (n : ℕ) : 0 + n = n := by
  sorry


theorem add_zero (a : ℕ) : a + 0 = a := by
  sorry

theorem one_eq_succ_zero : 1 = MyNat.succ 0 := by
  sorry

-- multiplication world
theorem mul_succ (a b : ℕ) : a * MyNat.succ b = a * b + a := by
  sorry

theorem mul_zero (a : ℕ) : a * 0 = 0 := by
  sorry

-- Theorem mul_one: For any natural number m, we have m×1=m.
theorem mul_one (m : ℕ) : m * 1 = m := by
  rw [one_eq_succ_zero]
  rw [mul_succ]
  rw [mul_zero]
  rw [zero_add]
  -- rfl

-- Theorem zero_mul: For all natural numbers m, we have 0×m=0.
theorem zero_mul (m : ℕ) : 0 * m = 0 := by
  induction m with
  | zero =>
    rw [mul_zero]
    -- rfl
  | succ m hm =>
    rw [mul_succ 0 m]
    rw [add_zero]
    exact hm

-- Theorem succ_mul: For all natural numbers a and b, we have (succ a)×b=a×b+b.
theorem succ_mul (a b : ℕ) : succ a * b = a * b + b := by
