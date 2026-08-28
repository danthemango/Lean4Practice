import Lean4PracticeWithMathlib.Basic

-- Commutativity of “∨”
example (P Q : Prop)(h : P ∨ Q) : Q ∨ P := by
  cases h
  right
  assumption
  left
  assumption

-- old hat
-- Implication across ∨
example (P Q R : Prop)(h1 : P → Q)(h2 : P ∨ R) : Q ∨ R := by
  cases h2
  left
  apply h1
  assumption
  right
  assumption


-- ∨ over ∧
example (P Q R : Prop)(h : P ∨ Q ∧ R) : (P ∨ Q) ∧ (P ∨ R) := by
  cases h
  constructor
  left
  assumption
  left
  assumption
  -- dw about it, I don't know how to give my hypes good names
  sorry

-- ∧ over ∨
example (P Q R : Prop)(h : P ∧ (Q ∨ R)) : (P ∧ Q) ∨ (P ∧ R) := by
  cases h
  -- cases right
  sorry
