import Lean4PracticeWithMathlib.Basic

theorem false_elim {P : Prop} (h : False) : P := by
  have h2 (x : Prop) : False -> x := by
    intro p
    contradiction
  exact h2 P h

-- theorem and_intro {P Q} (left : P) (right : Q) : P ∧ Q := by


-- not s means s implies false

-- False implies anything
-- ¬S is enough to show S → B
-- only use have and exact
example (B S : Prop)(h : ¬S) : S → B := by
  have h1 : ¬S → S → False := λ a => a
  have h2 : S → False := by
    exact h1 h
  have h5 : S → B := λ s => false_elim (h2 s)
  exact h5

-- not not introduction.
-- only use have and exact
example (P : Prop)(p : P) : ¬¬P := by
  have h1 : P → ¬P → False := λ hp => λ np => np hp
  have h2 : P → ¬¬P := λ hp => h1 hp
  have h3 : ¬¬P := h2 p
  exact h3

-- The law of non-self-contradiction
example (L : Prop) : ¬(L ∧ ¬L) := by
  have h1 : ¬L → L → False := λ h => h
  have h2 : L ∧ ¬L → False := λ hb => (h1 hb.right) hb.left
  exact h2

-- Modus Tollens.
example (B S : Prop)(h1 : B → S)(h2 : ¬S) : ¬B := by
  -- exact λ hb => h2 (h1 hb)
  -- using function composition
  exact λ hb => (h2 ∘ h1) hb

example (A : Prop) (h: A → ¬A) : ¬A := by
  have h2 : (A → ¬A) → A → ¬A:= λ h => h
  have h3 : A → (A → ¬A) → ¬A := λ ha => λhan => (h2 han) ha
  have h4 : A → (A → ¬A) → False:= λ ha => λ_ => ((h3 ha) h) ha
  have h5 : ¬A := λ ha => (h4 ha) h
  exact h5

-- Nested λ↦s.
example (B C : Prop) (h: ¬(B → C)) : ¬C := by
  -- have h7 : (B → C) → ¬C := λ lbc => false_elim (h lbc)
  -- have h9 : (B → C) → False → ¬C := λ hbc => false_elim (h hbc)
  -- have h11 : ¬(B → C) → (B → C) → False → ¬C := λ hbc =>
  -- have h10 : ¬(B → C) → ¬ C := λ nbc => (h nbc)
  -- have h8 : ¬C := (h3 h)

  have the_goal : ¬C := by sorry
  exact the_goal


-- TODO more problems incompleted
