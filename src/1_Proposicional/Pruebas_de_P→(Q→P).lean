-- Pruebas de P → (Q → P)
-- ======================

-- ----------------------------------------------------
-- Ej. 1. (p. 13) Demostrar
--    P → (Q → P)
-- ----------------------------------------------------

import tactic

variables (P Q : Prop)

-- 1ª demostración
example : P → (Q → P) :=
assume (h1 : P),
show Q → P, from
  ( assume h2 : Q,
    show P, from h1)

-- 2ª demostración
example : P → (Q → P) :=
assume (h1 : P),
show Q → P, from
  ( assume h2 : Q, h1)

-- 3ª demostración
example : P → (Q → P) :=
assume (h1 : P),
show Q → P, from
  ( λ h2, h1)

-- 4ª demostración
example : P → (Q → P) :=
assume (h1 : P), (λ h2, h1)

-- 5ª demostración
example : P → (Q → P) :=
λ h1, λ h2, h1

-- 6ª demostración
example : P → (Q → P) :=
λ h1 h2, h1

-- 7ª demostración
example : P → (Q → P) :=
λ h _, h

-- 8ª demostración
example : P → (Q → P) :=
-- by library_search
imp_intro

-- 9ª demostración
example : P → (Q → P) :=
begin
  intro h1,
  intro h2,
  exact h1,
end

-- 10ª demostración
example : P → (Q → P) :=
begin
  intros h1 h2,
  exact h1,
end

-- 6ª demostración
example : P → (Q → P) :=
λ h1 h2, h1

-- 11ª demostración
example : P → (Q → P) :=
-- by hint
by tauto

-- 12ª demostración
example : P → (Q → P) :=
by finish
