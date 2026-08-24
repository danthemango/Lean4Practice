theorem and_intro : P -> Q -> P ∧ Q := by
    intro h1
    intro h2
    constructor
    assumption
    assumption
