-- Pruebas del principio del tercio excluso
-- ========================================

-- Demostrar que
--    F ∨ ¬F

import tactic

variable (F : Prop)

-- open classical

-- 1ª demostración
example : F ∨ ¬F :=
by_contradiction 
  ( assume h1 : ¬(F ∨ ¬F),
    have h2 : ¬F, from
      assume h3 : F,
      have h4 : F ∨ ¬F, from or.inl h3,
      show false, from h1 h4,
    have h5 : F ∨ ¬F, from or.inr h2,
    show false, from h1 h5 )

-- 2ª demostración
example : F ∨ ¬F :=
by_contradiction
  ( assume h1 : ¬(F ∨ ¬F),
    have h2 : ¬F, from
      assume h3 : F,
      have h4 : F ∨ ¬F, from or.inl h3,
      show false, from h1 h4,
    have h5 : F ∨ ¬F, from or.inr h2,
    h1 h5 )

-- 3ª demostración
example : F ∨ ¬F :=
by_contradiction
  ( assume h1 : ¬(F ∨ ¬F),
    have h2 : ¬F, from
      assume h3 : F,
      have h4 : F ∨ ¬F, from or.inl h3,
      show false, from h1 h4,
    h1 (or.inr h2) )

-- 4ª demostración
example : F ∨ ¬F :=
by_contradiction
  ( assume h1 : ¬(F ∨ ¬F),
    have h2 : ¬F, from
      assume h3 : F,
      have h4 : F ∨ ¬F, from or.inl h3,
      h1 h4,
    h1 (or.inr h2) )

-- 5ª demostración
example : F ∨ ¬F :=
by_contradiction
  ( assume h1 : ¬(F ∨ ¬F),
    have h2 : ¬F, from
      assume h3 : F,
      h1 (or.inl h3),
    h1 (or.inr h2) )


-- 6ª demostración
example : F ∨ ¬F :=
by_contradiction
  ( assume h1 : ¬(F ∨ ¬F),
    have h2 : ¬F, from
      λ h3, h1 (or.inl h3),
    h1 (or.inr h2) )

-- 7ª demostración
example : F ∨ ¬F :=
by_contradiction
  ( assume h1 : ¬(F ∨ ¬F),
    h1 (or.inr (λ h3, h1 (or.inl h3))) )

-- 8ª demostración
example : F ∨ ¬F :=
by_contradiction
  ( λ h1, h1 (or.inr (λ h3, h1 (or.inl h3))) )

-- 9ª demostración
example : F ∨ ¬F :=
em F

#print axioms em

-- 10ª demostración
open_locale classical

example : F ∨ ¬F :=
begin
  by_contra h1,
  apply h1,
  apply or.inr,
  intro h2,
  apply h1,
  exact or.inl h2,
end

-- 11ª demostración
example : F ∨ ¬F :=
begin
  by_contra h1,
  apply h1,
  apply or.inr,
  intro h2,
  exact h1 (or.inl h2),
end

-- 12ª demostración
example : F ∨ ¬F :=
begin
  by_contra h1,
  apply h1,
  apply or.inr,
  exact λ h2, h1 (or.inl h2),
end

-- 13ª demostración
example : F ∨ ¬F :=
begin
  by_contra h1,
  apply h1,
  exact or.inr (λ h2, h1 (or.inl h2)),
end

-- 14ª demostración
example : F ∨ ¬F :=
begin
  by_contra h1,
  exact h1 (or.inr (λ h2, h1 (or.inl h2))),
end

-- 15ª demostración
example : F ∨ ¬F :=
by_contra (λh1, h1 (or.inr (λh2, h1 (or.inl h2))))

-- 16ª demostración
example : F ∨ ¬F :=
by tauto

-- 17ª demostración
example : F ∨ ¬F :=
by finish
