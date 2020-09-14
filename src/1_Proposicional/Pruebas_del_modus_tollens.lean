-- Pruebas del modus tollens
-- =========================

-- Ej. 1. Demostrar
--    P → Q, ¬Q ⊢ ¬P

import tactic

variables (P Q : Prop)

-- 1ª demostración
example 
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
assume h3 : P,
have h4 : Q,
  from h1 h3,
show false, 
  from h2 h4

-- 2ª demostración
example 
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
assume h3 : P,
have h4 : Q := h1 h3,
show false, 
  from h2 h4

-- 3ª demostración
example 
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
assume h3 : P,
show false, 
  from h2 (h1 h3)

-- 4ª demostración
example 
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
assume h3 : P, h2 (h1 h3)

-- 5ª demostración
example 
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
λ h3, h2 (h1 h3)

-- 6ª demostración
example 
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
h2 ∘ h1

-- 7ª demostración
example 
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
mt h1 h2

-- 8ª demostración
example 
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
by tauto

-- 9ª demostración
example 
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
by finish

