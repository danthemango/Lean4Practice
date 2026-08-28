import Lean4PracticeWithMathlib.Basic

theorem modus_tollens {P Q} (h : P → Q) (nq : ¬Q) : ¬P := by
  intro hp
  apply nq
  exact h hp

example (P Q : Prop) (hsj: Q → P) (hjs: P → Q) : Q ↔ P := by
  constructor
  assumption
  assumption

-- conjuctive iff
example (P Q : Prop) (h : P ↔ ¬Q) : (P → ¬Q) ∧ (¬Q → P) := by
  constructor
  cases h
  assumption
  cases h
  assumption

-- iff mp
example (P Q R : Prop) (h1 : Q ↔ R)(h2 : P → Q) : P → R := by
  intro hp
  apply h1.mp
  apply h2
  assumption

-- if intro
example (P Q R : Prop) (h1 : P ↔ R)(h2 : P → Q) : R → Q := by
  intro hr
  apply h2
  apply h1.mpr
  assumption

-- 5/7
-- no rewrites :(
-- We're not allowing have, exact, or rw for this level. It's certainly doable this way... good luck.
-- cheating version
example (P Q R S : Prop) (h1 : R ↔ S) (h2 : ¬((P → Q ∨ ¬S) ∧ (S ∨ P → ¬Q) → (S → Q)) ↔ P ∧ Q ∧ ¬S) : ¬((P → Q ∨ ¬R) ∧ (R ∨ P → ¬Q) → (R → Q)) ↔ P ∧ Q ∧ ¬R := by
  constructor
  intro h3
  have h4 : (R → S) → ¬S → ¬R := λ s_imp_r => modus_tollens s_imp_r
  have s_imp_r : R → S := h1.mp
  have nr_imp_ns : ¬S → ¬R := h4 s_imp_r
  have h6 : P ∧ Q ∧ ¬S → P ∧ Q ∧ ¬R := λ hpqnr => and_intro hpqnr.left (and_intro hpqnr.right.left (nr_imp_ns hpqnr.right.right))
  apply h6
  apply h2.mp

  repeat sorry
