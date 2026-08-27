import Lean4PracticeWithMathlib.Basic

-- and introduction
example (P S : Prop)(p: P)(s : S) : P ∧ S := by
  exact and_intro p s

theorem false_elim {P : Prop} (h : False) : P := by
  have h2 (x : Prop) : False -> x := by
    intro p
    contradiction
  exact h2 P h

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
  have h2 : L ∧ ¬L → False := λ hlnl => (h1 hlnl.right) hlnl.left
  exact h2

-- Modus Tollens.
theorem modus_tollens (B S : Prop) (h1 : B → S) (h2 : ¬S) : ¬B := by
  -- exact λ hb => h2 (h1 hb)
  -- using function composition
  exact λ hb => (h2 ∘ h1) hb

theorem modus_ponens (B S : Prop) (h1 : B → S) (h2 : B) : S := by
  exact h1 h2

example (A : Prop) (h: A → ¬A) : ¬A := by
  have h2 : (A → ¬A) → A → ¬A:= λ h => h
  have h3 : A → (A → ¬A) → ¬A := λ ha => λhan => (h2 han) ha
  have h4 : A → (A → ¬A) → False:= λ ha => λ_ => ((h3 ha) h) ha
  have h5 : ¬A := λ ha => (h4 ha) h
  exact h5

-- Negation
-- Nested λ↦s.
example (B C : Prop) (h: ¬(B → C)) : ¬C := by
  -- ¬(B → C) ↔ ¬(¬B ∨ C) ↔ B ∧ ¬C
  -- have h1 : ¬(B → C) → B ∧ ¬C :=

  -- have h1 : B → C → (B ∧ C) := λ hb => λ hc => and_intro hb hc
  -- have h2 : (B → C) → (B ∧ C) := λ hbc => false_elim (h hbc)
  -- have h3 : (B → C) → ¬C := λ hbc => λ nc => false_elim (h hbc)

  have the_goal : ¬C := by sorry
  exact the_goal

-- Negation into conjuction.
example (C S : Prop) (s: S) : ¬(¬S ∧ C) := by
  -- ¬(¬S ∧ C) ↔ S ∨ ¬C
  -- S → (S ∨ ¬C)
  sorry

-- implies a negation
example (A P : Prop) (h : P → ¬A) : ¬(P ∧ A) := by
  have h4 : ¬A → A → False := λ h => h
  have h3 : A ∧ ¬A → False := λ hana => (h4 hana.right) hana.left
  have h17 : (P → ¬A) → (P ∧ A) → (A ∧ ¬A) := λ pna => λ npa => and_intro npa.right (pna npa.left)
  have h18 : (P → ¬A) → ¬(P ∧ A) := λ pna => λ npa => h3 ((h17 pna) npa)
  exact h18 h

-- Conjunction Implication
example (A P : Prop) (h: ¬(P ∧ A)) : P → ¬A := by
  sorry


example (C S : Prop) (s: S) : S ∨ C := by
  sorry


-- TODO more problems incompleted
