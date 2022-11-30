
variables A B C D : Prop

example : A ∧ (A → B) → B :=
assume h: A ∧ (A -> B),
show B, from (and.right h) (and.left h)

example : A → ¬(¬A ∧ B) :=
assume h1: A,
assume h2: ¬A ∧B,
show false, from (and.left h2) h1

example : ¬(A ∧ B) → (A → ¬B) :=
assume h: ¬ (A ∧ B),
assume h₁ : A,
assume h₂ : B,
show false, from h (and.intro h₁ h₂)


example (h₁ : A ∨ B) (h₂ : A → C) (h₃ : B → D) : C ∨ D := /- lots of haves/shows -/

show C ∨ D, from or.elim h₁

(assume optionOne: A, show C ∨ D, from or.inl(h₂ optionOne) )
(assume optionTwo: B, show C ∨ D, from or.inr (h₃ optionTwo) )

example (h : ¬A ∧ ¬B) : ¬(A ∨ B) := /-demorgan's Law-/
assume h2 : A∨B,

 show false, from or.elim h2
(assume optionOne: A, show false, from (and.left h) optionOne)
(assume optionTwo: B, show false, from (and.right h) optionTwo)



example : ¬(A ↔ ¬A) :=
assume h: A ↔ ¬A,
show false, from (assume h1: A,((iff.mp h h1)h1))(iff.mpr h (assume h1: A, ((iff.mp h h1)h1)))
