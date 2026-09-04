-- prime number adoration

def PrimeNum (n : Nat) : Prop :=
  n ≥ 2 ∧ ∀ (m : Nat), m ∣ n → m = 1 ∨ m = n

theorem prime_def : (PrimeNum p) ↔ 2 ≤ p ∧ ∀ (m : Nat), m ∣ p → m = 1 ∨ m = p := by
  sorry

example (a p : Nat) (hp : PrimeNum p) (h : 2 ≤ a) (ha : a ∣ p) : a = p := by
  rw [prime_def] at hp
  obtain ⟨h₁, h₂⟩ := hp
  have hp' := h₂ a
  have hp'' := hp' ha
  obtain ha1 | ha2 := hp''
  have ha3 := h
  rw [ha1] at ha3
  contradiction
  assumption

theorem Prime.dvd_mul {p m n} (pp : PrimeNum p) : p ∣ m * n ↔ p ∣ m ∨ p ∣ n := by
  sorry

example (a b : Nat) : 5 ∣ (a * b) ↔ 5 ∣ a ∨ 5 ∣ b := by
  apply Prime.dvd_mul
  -- decide
  sorry

def Even (n: Nat) : Prop :=
  ∃ r : Nat, n = r + r

def ExactlyOne (P : Prop) : Prop :=
  sorry

-- exists only one
example : ∃ (p : Nat), PrimeNum p ∧ Even p := by
  sorry
