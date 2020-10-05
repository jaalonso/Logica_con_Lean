-- Regla de eliminación de la disyunción
-- =====================================

import tactic

variables (P Q R : Prop)

-- Ej. 1. Demostrar
--    P ∨ Q, P → R, Q → R ⊢ R

-- 1ª demostración
example
  (h1 : P ∨ Q)
  (h2 : P → R) 
  (h3 : Q → R)
  : R :=
or.elim h1 h2 h3

example
  (h1 : P ∨ Q)
  (h2 : P → R) 
  (h3 : Q → R)
  : R :=
h1.elim h2 h3

-- 2ª demostración
example
  (h1 : P ∨ Q)
  (h2 : P → R) 
  (h3 : Q → R)
  : R :=
or.rec h2 h3 h1

-- 3ª demostración
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

-- 4ª demostración
example
  (h1 : P ∨ Q)
  (h2 : P → R) 
  (h3 : Q → R)
  : R :=
by tauto

-- 5ª demostración
example
  (h1 : P ∨ Q)
  (h2 : P → R) 
  (h3 : Q → R)
  : R :=
by finish
