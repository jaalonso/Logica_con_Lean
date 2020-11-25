-- Regla de eliminación de la disyunción
-- =====================================

import tactic

variables (P Q R : Prop)

-- ----------------------------------------------------
-- Ej. 1. (p. 11) Demostrar
--    P ∨ Q, P → R, Q → R ⊢ R
-- ----------------------------------------------------

-- 1ª demostración
example
  (h1 : P ∨ Q)
  (h2 : P → R)
  (h3 : Q → R)
  : R :=
or.elim h1 h2 h3

-- 2ª demostración
example
  (h1 : P ∨ Q)
  (h2 : P → R)
  (h3 : Q → R)
  : R :=
h1.elim h2 h3

-- 3ª demostración
example
  (h1 : P ∨ Q)
  (h2 : P → R)
  (h3 : Q → R)
  : R :=
-- by library_search
or.rec h2 h3 h1

-- 4ª demostración
example
  (h1 : P ∨ Q)
  (h2 : P → R)
  (h3 : Q → R)
  : R :=
begin
  cases h1 with hP hQ,
  { exact h2 hP, },
  { exact h3 hQ, },
end

-- 5ª demostración
example
  (h1 : P ∨ Q)
  (h2 : P → R)
  (h3 : Q → R)
  : R :=
-- by hint
by tauto

-- 6ª demostración
example
  (h1 : P ∨ Q)
  (h2 : P → R)
  (h3 : Q → R)
  : R :=
by finish
