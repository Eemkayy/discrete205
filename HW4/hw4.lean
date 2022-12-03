import data.set
import data.int.basic
import data.nat.basic
open function int set nat

section
  def f (x : ℤ) : ℤ := x + 3
  def g (x : ℤ) : ℤ := -x
  def h (x : ℤ) : ℤ := 2 * x + 3

  -- 1
  example : injective h :=
  begin
  assume x1 x2, assume h2 : 2 * x1 + 3 = 2 * x2 + 3,
  show x1=x2, from 
    have h1 : 2 ≠ (0 : ℤ), from dec_trivial,  show x1 = x2, from mul_left_cancel₀ h1 (add_right_cancel h2)
  end

  -- 2
  example : surjective g :=
  assume y1, have h3 : g ( -y1 ) = y1, from calc 
        g ( -y1 ) = - (-y1) : rfl
        ... = y1           : by rw neg_neg y1, show ∃ x, g x = y1, from  exists.intro (-y1) h3

  -- 3
  example (A B : Type) (u : A → B) (v1 : B → A) (v2 : B → A)
    (h1 : left_inverse v1 u) (h2 : right_inverse v2 u) : v1 = v2 :=
  funext
    (assume x,
      calc
        v1 x = v1 (u (v2 x)) : by rw h2
         ... = v2 x          : by rw h1)
end

-- 4
section
  variables {X Y : Type}
  variable f : X → Y
  variables A B : set X

  example : f '' (A ∩ B) ⊆ f '' A ∩ f '' B :=
  assume y,
  assume h1 : y ∈ f '' (A ∩ B),
  show y ∈ f '' A ∩ f '' B, from 
  exists.elim h1 $
      assume x5 : X,
      assume h4 : x5 ∈ A ∩ B ∧ f x5 = y,
      have ha: f x5 = y, from and.right h4,
      have hb : x5 ∈ A ∩ B, from and.left h4,
      have hc : x5 ∈ A, from and.left hb,
      have hd : y ∈ f '' A, from exists.intro x5 $ ⟨hc, ha⟩,
      have he : x5 ∈ B, from and.right hb,
      have hf :y ∈ f '' B, from exists.intro x5 $ ⟨he, ha⟩,
      ⟨hd, hf⟩ 
end


-- 5
example : ∀ m n k : nat, m * (n + k) = m * n + m * k :=
assume m n k, 
nat.rec_on k
    (show m*(n + 0) = m*n + m*0, from calc
    m*(n + 0) = m*n : by rw add_zero 
          ... = m*n + 0 : by rw add_zero
          ... = m*n + m*0 : by rw mul_zero
    )
    (assume k, 
    assume ih: m*(n + k) = m*n + m*k, 
    show m*(n + succ k) = m*n + m*(succ k), from calc
    m*(n + succ k) = m*(succ(n + k)) : by rw add_succ
               ... = m*(n + k) + m : by rw mul_succ
               ... = m*n + m*k + m : by rw ih 
               ... = m*n + (m*k + m) : by rw add_assoc
               ... = m*n + m*(succ k) : by rw mul_succ         
    )

-- 6
example : ∀ n : nat, 0 * n = 0 :=
begin
  intro n,
  induction n with i2 h2,
  show 0 * 0 = 0, from mul_zero 0, 
  rw mul_succ,
  rw h2,
end

-- 7
example : ∀ n : nat, 1 * n = n :=
begin
intro n,
  induction n with i3 h3,
  show 1 * 0 = 0, from mul_zero 1,
  rw mul_succ,
  rw h3,
end

-- 8
example : ∀ m n k : nat, (m * n) * k = m * (n * k) :=
begin
  intros m n k,
  induction k with i4 h4,
  show (m * n) * 0 = m * (n * 0), from calc
        (m * n) * 0 = 0           : by rw mul_zero
                ... = m * 0       : by rw mul_zero
                ... = m * (n * 0) : by rw mul_zero n,
  rw mul_succ,
  rw mul_succ,
  rw mul_add,
  rw h4,

end

-- 9
example : ∀ m n : nat, m * n = n * m :=
begin
  intros m n,
  induction n with i5 h5,
  show m * 0 = 0 * m, from calc
        m * 0 = 0     : by rw mul_zero
          ... = 0 * m : by rw zero_mul,
  rw mul_succ,
  rw succ_mul,
  rw h5,

end
