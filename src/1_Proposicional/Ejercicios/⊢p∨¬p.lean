-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    ⊢ p ∨ ¬p
-- ----------------------------------------------------

import tactic
variable (p : Prop)

open_locale classical

-- 1ª demostración
example : p ∨ ¬p :=
by_contradiction
  ( assume h1 : ¬(p ∨ ¬p),
    have h2 : ¬p, from
      assume h3 : p,
      have h4 : p ∨ ¬p, from or.inl h3,
      show false, from h1 h4,
    have h5 : p ∨ ¬p, from or.inr h2,
    show false, from h1 h5 )

-- 2ª demostración
example : p ∨ ¬p :=
by_contradiction
  ( assume h1 : ¬(p ∨ ¬p),
    have h2 : ¬p, from
      assume h3 : p,
      have h4 : p ∨ ¬p, from or.inl h3,
      show false, from h1 h4,
    have h5 : p ∨ ¬p, from or.inr h2,
    h1 h5 )

-- 3ª demostración
example : p ∨ ¬p :=
by_contradiction
  ( assume h1 : ¬(p ∨ ¬p),
    have h2 : ¬p, from
      assume h3 : p,
      have h4 : p ∨ ¬p, from or.inl h3,
      show false, from h1 h4,
    h1 (or.inr h2) )

-- 4ª demostración
example : p ∨ ¬p :=
by_contradiction
  ( assume h1 : ¬(p ∨ ¬p),
    have h2 : ¬p, from
      assume h3 : p,
      have h4 : p ∨ ¬p, from or.inl h3,
      h1 h4,
    h1 (or.inr h2) )

-- 5ª demostración
example : p ∨ ¬p :=
by_contradiction
  ( assume h1 : ¬(p ∨ ¬p),
    have h2 : ¬p, from
      assume h3 : p,
      h1 (or.inl h3),
    h1 (or.inr h2) )

-- 6ª demostración
example : p ∨ ¬p :=
by_contradiction
  ( assume h1 : ¬(p ∨ ¬p),
    have h2 : ¬p, from
      λ h3, h1 (or.inl h3),
    h1 (or.inr h2) )

-- 7ª demostración
example : p ∨ ¬p :=
by_contradiction
  ( assume h1 : ¬(p ∨ ¬p),
    h1 (or.inr (λ h3, h1 (or.inl h3))) )

-- 8ª demostración
example : p ∨ ¬p :=
by_contradiction
  ( λ h1, h1 (or.inr (λ h3, h1 (or.inl h3))) )

-- 9ª demostración
example : p ∨ ¬p :=
-- by library_search
em p

-- #print axioms em

-- 10ª demostración
example : p ∨ ¬p :=
begin
  by_contra h1,
  apply h1,
  apply or.inr,
  intro h2,
  apply h1,
  exact or.inl h2,
end

-- 11ª demostración
example : p ∨ ¬p :=
begin
  by_contra h1,
  apply h1,
  apply or.inr,
  intro h2,
  exact h1 (or.inl h2),
end

-- 12ª demostración
example : p ∨ ¬p :=
begin
  by_contra h1,
  apply h1,
  apply or.inr,
  exact λ h2, h1 (or.inl h2),
end

-- 13ª demostración
example : p ∨ ¬p :=
begin
  by_contra h1,
  apply h1,
  exact or.inr (λ h2, h1 (or.inl h2)),
end

-- 14ª demostración
example : p ∨ ¬p :=
begin
  by_contra h1,
  exact h1 (or.inr (λ h2, h1 (or.inl h2))),
end

-- 15ª demostración
example : p ∨ ¬p :=
by_contra (λ h1, h1 (or.inr (λh2, h1 (or.inl h2))))

-- 16ª demostración
example : p ∨ ¬p :=
begin
  by_contra h1,
  apply h1,
  right,
  intro h2,
  apply h1,
  left,
  exact h2,
end

-- 17ª demostración
example : p ∨ ¬p :=
-- by hint
by tauto

-- 18ª demostración
example : p ∨ ¬p :=
by finish
