-- Pruebas del principio del tercio excluso
-- ========================================

-- Demostrar que
--    A ∨ ¬A

import tactic

variable (A : Prop)

-- open classical

-- 1ª demostración
example : A ∨ ¬A :=
by_contradiction 
  ( assume h1 : ¬(A ∨ ¬A),
    have h2 : ¬A, from
      assume h3 : A,
      have h4 : A ∨ ¬A, from or.inl h3,
      show false, from h1 h4,
    have h5 : A ∨ ¬A, from or.inr h2,
    show false, from h1 h5 )

-- 2ª demostración
example : A ∨ ¬A :=
by_contradiction
  ( assume h1 : ¬(A ∨ ¬A),
    have h2 : ¬A, from
      assume h3 : A,
      have h4 : A ∨ ¬A, from or.inl h3,
      show false, from h1 h4,
    have h5 : A ∨ ¬A, from or.inr h2,
    h1 h5 )

-- 3ª demostración
example : A ∨ ¬A :=
by_contradiction
  ( assume h1 : ¬(A ∨ ¬A),
    have h2 : ¬A, from
      assume h3 : A,
      have h4 : A ∨ ¬A, from or.inl h3,
      show false, from h1 h4,
    h1 (or.inr h2) )

-- 4ª demostración
example : A ∨ ¬A :=
by_contradiction
  ( assume h1 : ¬(A ∨ ¬A),
    have h2 : ¬A, from
      assume h3 : A,
      have h4 : A ∨ ¬A, from or.inl h3,
      h1 h4,
    h1 (or.inr h2) )

-- 5ª demostración
example : A ∨ ¬A :=
by_contradiction
  ( assume h1 : ¬(A ∨ ¬A),
    have h2 : ¬A, from
      assume h3 : A,
      h1 (or.inl h3),
    h1 (or.inr h2) )


-- 6ª demostración
example : A ∨ ¬A :=
by_contradiction
  ( assume h1 : ¬(A ∨ ¬A),
    have h2 : ¬A, from
      λ h3, h1 (or.inl h3),
    h1 (or.inr h2) )

-- 7ª demostración
example : A ∨ ¬A :=
by_contradiction
  ( assume h1 : ¬(A ∨ ¬A),
    h1 (or.inr (λ h3, h1 (or.inl h3))) )

-- 8ª demostración
example : A ∨ ¬A :=
by_contradiction
  ( λ h1, h1 (or.inr (λ h3, h1 (or.inl h3))) )

-- 9ª demostración
example : A ∨ ¬A :=
em A

-- 10ª demostración
open_locale classical

example : A ∨ ¬A :=
begin
  by_contra h1,
  apply h1,
  apply or.inr,
  intro h2,
  apply h1,
  exact or.inl h2,
end

-- 11ª demostración
example : A ∨ ¬A :=
begin
  by_contra h1,
  apply h1,
  apply or.inr,
  intro h2,
  exact h1 (or.inl h2),
end

-- 12ª demostración
example : A ∨ ¬A :=
begin
  by_contra h1,
  apply h1,
  apply or.inr,
  exact λ h2, h1 (or.inl h2),
end

-- 13ª demostración
example : A ∨ ¬A :=
begin
  by_contra h1,
  apply h1,
  exact or.inr (λ h2, h1 (or.inl h2)),
end

-- 14ª demostración
example : A ∨ ¬A :=
begin
  by_contra h1,
  exact h1 (or.inr (λ h2, h1 (or.inl h2))),
end

-- 15ª demostración
example : A ∨ ¬A :=
by_contra (λh1, h1 (or.inr (λh2, h1 (or.inl h2))))

-- 16ª demostración
example : A ∨ ¬A :=
by tauto

-- 17ª demostración
example : A ∨ ¬A :=
by finish
