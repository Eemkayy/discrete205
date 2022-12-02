
import data.set
open set

-- 1. Replace "sorry" in these examples.
section
  variable {U : Type}
  variables A B C : set U

  example : ∀ x, x ∈ A ∩ C → x ∈ A ∪ B :=
  assume x,
  assume h: x ∈ A ∩ C,
  show x ∈ A ∪ B, from or.inl h.left  

  example : ∀ x, x ∈ -(A ∪ B) → x ∈ -A :=
  assume x, 
  assume : x ∈ -(A ∪ B),
  have ¬ x ∈ (A ∪ B), from this,
  assume : x ∈ A, 
  show false, from ‹¬ x ∈ (A ∪ B)› (or.inl this)
end

-- 2. Replace "sorry" in the last example.
section
  variable {U : Type}

  /- defining "disjoint" -/
  def disj (A B : set U) : Prop := ∀ ⦃x⦄, x ∈ A → x ∈ B → false

  example (A B : set U) (h : ∀ x, ¬ (x ∈ A ∧ x ∈ B)) : disj A B :=
  assume x,
  assume h1 : x ∈ A,
  assume h2 : x ∈ B,
  have h3 : x ∈ A ∧ x ∈ B, from and.intro h1 h2,
  show false, from h x h3

  -- notice that we do not have to mention x when applying
  --   h : disj A B
  example (A B : set U) (h1 : disj A B) (x : U) (h2 : x ∈ A) (h3 : x ∈ B) : false :=
  h1 h2 h3

  -- the same is true of ⊆
  example (A B : set U) (x : U) (h : A ⊆ B) (h1 : x ∈ A) : x ∈ B :=
  h h1

  example (A B C D : set U) (h1 : disj A B) (h2 : C ⊆ A) (h3 : D ⊆ B) : disj C D :=
    assume x,   
    assume g1: x ∈ C,
    assume g2: x ∈ D,
    have g3: x ∈ A, from h2 g1,
    have g4: x ∈ B, from h3 g2, 
    show false, from h1 g3 g4
end

-- 3. Prove the following facts about indexed unions and
-- intersections, using the theorems Inter.intro, Inter.elim,
-- Union.intro, and Union.elim listed above.
section
  variables {I U : Type}
  variables (A : I → set U) (B : I → set U) (C : set U)

  def Union (A : I → set U) : set U := { x | ∃ i : I, x ∈ A i }
  def Inter (A : I → set U) : set U := { x | ∀ i : I, x ∈ A i }

    notation `⋃` binders `, ` r:(scoped f, Union f) := r
    notation `⋂` binders `, ` r:(scoped f, Inter f) := r

    theorem Inter.intro {x : U} (h : ∀ i, x ∈ A i) : x ∈ ⋂ i, A i :=
        by simp; assumption

    
    theorem Inter.elim {x : U} (h : x ∈ ⋂ i, A i) (i : I) : x ∈ A i :=
        by simp at h; apply h

    theorem Union.intro {x : U} (i : I) (h : x ∈ A i) :
    x ∈ ⋃ i, A i :=
        by {simp, existsi i, exact h}

    theorem Union.elim {b : Prop} {x : U}
    (h₁ : x ∈ ⋃ i, A i) (h₂ : ∀ (i : I), x ∈ A i → b) : b :=
        by {simp at h₁, cases h₁ with i h, exact h₂ i h}

  example : (⋂ i, A i) ∩ (⋂ i, B i) ⊆ (⋂ i, A i ∩ B i) :=
  assume x,
        assume h: x ∈ (⋂ i, A i) ∩ (⋂ i, B i), 
        show x ∈ (⋂ i, A i ∩ B i), from 
            Inter.intro 
            (assume i: I,
            have h1: x ∈ A i, from Inter.elim h.left i,
            have h2: x ∈ B i, from Inter.elim h.right i,
            show x ∈ A i ∩ B i, from and.intro h1 h2)

  example : C ∩ (⋃i, A i) ⊆ ⋃i, C ∩ A i :=
  assume x : U,
        assume h : x ∈ C ∩ (⋃i, A i),
        show x ∈ ⋃ i, C ∩ A i, from
            Union.elim h.right 
            (assume i : I,
            assume h1: x ∈ A i,
            show  x ∈ ⋃ i, C ∩ A i, from 
                Union.intro i (and.intro h.left h1))
end

-- 4. Prove the following fact about power sets. You can use the
-- theorems subset.trans and subset.refl
section
  variable  {U : Type}
  variables A B C : set U

    @[refl] theorem subset.refl (a : set U) : a ⊆ a := assume x, id 

    @[trans] theorem subset.trans {a b c : set U} (ab : a ⊆ b) (bc : b ⊆ c) : a ⊆ c :=
        assume x h, bc (ab h)
  -- For this exercise these two facts are useful
  example (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C :=
  subset.trans h1 h2

  example : A ⊆ A :=
  subset.refl A

  example (h : A ⊆ B) : powerset A ⊆ powerset B :=
   assume X : set U,
        assume h1 : X ∈ powerset A,
        show X ∈ powerset B, from subset.trans h1 h

  example (h : powerset A ⊆ powerset B) : A ⊆ B :=
  assume x: U,
        assume h1 : x ∈ A,
        have h2: {y|x = y} ∈ powerset A, from 
            assume z,
            assume : z ∈ {y| x = y},
            have x = z, from this,
            show z ∈ A, from eq.subst this h1, 
        have h3: {y| x = y} ∈ powerset B, from h h2, 
        have h4: x ∈ {y| x = y}, from eq.refl x, 
        show x ∈ B, from h3 h4
end

-- 5. Replace the sorry commands in the following proofs to show that
-- we can create a partial order R'​ out of a strict partial order R.
section
  parameters {A : Type} {R : A → A → Prop}
  parameter (irreflR : irreflexive R)
  parameter (transR : transitive R)

  local infix < := R
  variables a b c : A

  def R' (a b : A) : Prop := R a b ∨ a = b
  local infix ≤ := R'

  theorem reflR' (a : A) : a ≤ a :=
  begin
        have h1: a = a, from eq.refl a,
        apply or.inr h1
    end

  theorem transR' {a b c : A} (h1 : a ≤ b) (h2 : b ≤ c): a ≤ c :=
    or.elim h1
        (assume h3: a < b, or.elim h2 
                (assume h4: b < c, or.inl (transR h3 h4))
                (assume h4: b = c, eq.subst h4 h1))
        (assume h3: a = b, eq.subst (eq.symm h3) h2) 

  theorem antisymmR' {a b : A} (h1 : a ≤ b) (h2 : b ≤ a) : a = b :=
  or.elim h1 
        (assume h: a < b, or.elim h2
            (assume h3: b < a, false.elim ((irreflR b) (transR h3 h))) 
            (assume h3: b = a, eq.symm h3))
        (assume h: a = b, h)
end

-- 6
section
  parameters {A : Type} {R : A → A → Prop}
  parameter (reflR : reflexive R)
  parameter (transR : transitive R)

  def S (a b : A) : Prop := R a b ∧ R b a

  example : transitive S :=
  assume x y z,
        assume h1 h2,
        and.intro (transR h1.left h2.left) (transR h2.right h1.right)
end

-- 7. Only one of the following two theorems is provable. Figure out
-- which one is true, and replace the sorry command with a complete
-- proof.
section
  parameters {A : Type} {a b c : A} {R : A → A → Prop}
  parameter (Rab : R a b)
  parameter (Rbc : R b c)
  parameter (nRac : ¬ R a c)


  theorem R_is_not_strict_partial_order : ¬(irreflexive R ∧ transitive R) :=
  assume h: irreflexive R ∧ transitive R, 
  show false, from nRac (h.right Rab Rbc)
end

-- 8
section
  open nat

  example : 1 ≤ 4 :=
  have h1: 1 <  1 + 1, from lt_succ_self 1, 
have h2: (1 + 1) < (1 + 1) + 1, from lt_succ_self (1 + 1),
have h3: (1 + 1 + 1) < (1 + 1 + 1) + 1, from lt_succ_self (1 + 1 + 1),
have h4: 4 = 1 + 1 + 1 + 1, by simp,
have h5: 1 ≤ (1 + 1 + 1) + 1, from le_of_lt (lt_trans h1 (lt_trans h2 h3)),
eq.subst h4 h5 
end