-- Pruebas de P → Q ⊢ ¬P ∨ Q
-- =========================

-- ----------------------------------------------------
-- Ej. 1. (p. 24) Demostrar
--    P → Q ⊢ ¬P ∨ Q
-- ----------------------------------------------------

import tactic

variables (P Q : Prop)

open_locale classical

-- 1ª demostración
example
  (h1 : P → Q)
  : ¬P ∨ Q :=
have h2 : P ∨ ¬P,
  from em P,
or.elim h2
  ( assume h3 : P,
    have h4 : Q,
      from h1 h3,
    show ¬P ∨ Q,
      from or.inr h4)
  ( assume h5 : ¬P,
    show ¬P ∨ Q,
      from or.inl h5)

-- 2ª demostración
example
  (h1 : P → Q)
  : ¬P ∨ Q :=
have h2 : P ∨ ¬P,
  from em P,
or.elim h2
  ( assume h3 : P,
    have h4 : Q,
      from h1 h3,
    show ¬P ∨ Q,
      from or.inr h4)
  ( assume h5 : ¬P,
    or.inl h5)

-- 3ª demostración
example
  (h1 : P → Q)
  : ¬P ∨ Q :=
have h2 : P ∨ ¬P,
  from em P,
or.elim h2
  ( assume h3 : P,
    have h4 : Q,
      from h1 h3,
    show ¬P ∨ Q,
      from or.inr h4)
  ( λ h5, or.inl h5)

-- 4ª demostración
example
  (h1 : P → Q)
  : ¬P ∨ Q :=
have h2 : P ∨ ¬P,
  from em P,
or.elim h2
  ( assume h3 : P,
    have h4 : Q,
      from h1 h3,
    or.inr h4)
  ( λ h5, or.inl h5)

-- 5ª demostración
example
  (h1 : P → Q)
  : ¬P ∨ Q :=
have h2 : P ∨ ¬P,
  from em P,
or.elim h2
  ( assume h3 : P,
    or.inr (h1 h3))
  ( λ h5, or.inl h5)

-- 6ª demostración
example
  (h1 : P → Q)
  : ¬P ∨ Q :=
have h2 : P ∨ ¬P,
  from em P,
or.elim h2
  ( λ h3, or.inr (h1 h3))
  ( λ h5, or.inl h5)

-- 7ª demostración
example
  (h1 : P → Q)
  : ¬P ∨ Q :=
or.elim (em P)
  ( λ h3, or.inr (h1 h3))
  ( λ h5, or.inl h5)

example
  (h1 : P → Q)
  : ¬P ∨ Q :=
(em P).elim
  ( λ h3, or.inr (h1 h3))
  ( λ h5, or.inl h5)

-- 8ª demostración
example
  (h1 : P → Q)
  : ¬P ∨ Q :=
-- by library_search
not_or_of_imp h1

-- 9ª demostración
example
  (h1 : P → Q)
  : ¬P ∨ Q :=
if h3 : P then or.inr (h1 h3) else or.inl h3

-- 10ª demostración
example
  (h1 : P → Q)
  : ¬P ∨ Q :=
begin
  by_cases h2 : P,
  { apply or.inr,
    exact h1 h2, },
  { exact or.inl h2, },
end

-- 11ª demostración
example
  (h1 : P → Q)
  : ¬P ∨ Q :=
begin
  by_cases h2 : P,
  { exact or.inr (h1 h2), },
  { exact or.inl h2, },
end

-- 12ª demostración
example
  (h1 : P → Q)
  : ¬P ∨ Q :=
begin
  by_cases h2 : P,
  { right,
    exact h1 h2, },
  { left,
    exact h2, },
end

-- 13ª demostración
example
  (h1 : P → Q)
  : ¬P ∨ Q :=
-- by hint
by tauto

-- 14ª demostración
example
  (h1 : P → Q)
  : ¬P ∨ Q :=
-- by hint
by finish
