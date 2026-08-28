import Lean4PracticeWithMathlib.Basic

example (P : Prop)(h'₁ : P) : ¬¬P := by
  intro h2
  exfalso
  apply h2
  assumption

example (P : Prop) : ¬(P ∧ ¬P) := by
  intro h
  cases h
  -- apply right
  sorry

-- Modus Tollens.
example (P Q : Prop)(h1 : P → Q)(h2 : ¬Q) : ¬P := by
  intro hp
  apply h2
  apply h1
  assumption

theorem modus_tollens {P Q} (h : P → Q) (nq : ¬Q) : ¬P := by
  intro hp
  apply nq
  exact h hp

-- self contradictory
-- Remember h: P → ¬P is actually h : P → P → False
example (P : Prop) (h: P → ¬P) : ¬P := by
  intro hnp
  apply h
  assumption
  assumption

-- anonymous intro
example (P Q : Prop) (h: ¬(P → Q)) : ¬Q := by
  intro hq
  apply h
  intro hp
  assumption

-- Negation into conjuction.
example (P Q : Prop) (h: Q) : ¬(¬Q ∧ P) := by
  intro ⟨ nq, p ⟩
  apply nq
  assumption

-- using: apply, assumption, cases, intro, repeat
-- Show ¬(P ∧ A)
example (P Q : Prop) (h : Q → ¬P) : ¬(Q ∧ P) := by
  intro ⟨ hq, hp ⟩
  apply h
  repeat assumption

-- Show P → ¬A.
example (P Q : Prop) (h: ¬(Q ∧ P)) : Q → ¬P := by
  intro p q
  apply h
  constructor
  repeat assumption

-- ¬A is stable.
example (P : Prop)(h : ¬¬¬P) : ¬P := by
  intro hp
  apply h
  intro hn2
  apply hn2
  assumption

-- not tactics boss
example (B C : Prop) (h : ¬(B → C)) : ¬¬B := by
  intro nb
  apply h
  intro hb
  contradiction
