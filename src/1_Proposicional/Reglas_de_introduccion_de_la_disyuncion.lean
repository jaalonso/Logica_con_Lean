-- Reglas de introducción de la disyunción
-- =======================================

import tactic

variables (P Q R : Prop)

-- Ej. 1. Demostrar
--    P ⊢ P ∨ Q

-- 1ª demostración 
example 
  (h : P)
  : P ∨ Q :=
or.intro_left Q h

-- 2ª demostración 
example 
  (h : P)
  : P ∨ Q :=
or.inl h

-- 3ª demostración 
example 
  (h : P)
  : P ∨ Q :=
by tauto

-- 4ª demostración 
example 
  (h : P)
  : P ∨ Q :=
by finish

-- Ej. 2. Demostrar
--    P ∧ Q ⊢ P ∨ R

-- 1ª demostración
example 
  (h1 : P ∧ Q)
  : P ∨ R :=
have h2 : P,
  from and.elim_left h1,
show P ∨ R,
  from or.inl h2

-- 2ª demostración
example 
  (h1 : P ∧ Q)
  : P ∨ R :=
have h2 : P,
  from h1.1,
show P ∨ R,
  from or.inl h2

-- 3ª demostración
example 
  (h1 : P ∧ Q)
  : P ∨ R :=
have h2 : P := h1.1,
show P ∨ R,
  from or.inl h2

-- 4ª demostración
example 
  (h1 : P ∧ Q)
  : P ∨ R :=
show P ∨ R,
  from or.inl h1.1

-- 5ª demostración
example 
  (h1 : P ∧ Q)
  : P ∨ R :=
or.inl h1.1

-- 6ª demostración
example 
  (h1 : P ∧ Q)
  : P ∨ R :=
by tauto

-- 7ª demostración
example 
  (h1 : P ∧ Q)
  : P ∨ R :=
by finish

-- Ej. 3. Demostrar
--    Q ⊢ P ∨ Q

-- 1ª demostración 
example 
  (h : Q)
  : P ∨ Q :=
or.intro_right P h

-- 2ª demostración 
example 
  (h : Q)
  : P ∨ Q :=
or.inr h

-- 3ª demostración 
example 
  (h : Q)
  : P ∨ Q :=
by tauto

-- 4ª demostración 
example 
  (h : Q)
  : P ∨ Q :=
by finish

-- Ej. 4. Demostrar
--    P ∧ Q ⊢ P ∨ R

-- 1ª demostración
example 
  (h1 : P ∧ Q)
  : R ∨ Q :=
have h2 : Q,
  from and.elim_right h1,
show R ∨ Q,
  from or.inr h2

-- 2ª demostración
example 
  (h1 : P ∧ Q)
  : R ∨ Q :=
have h2 : Q,
  from h1.2,
show R ∨ Q,
  from or.inr h2

-- 3ª demostración
example 
  (h1 : P ∧ Q)
  : R ∨ Q :=
have h2 : Q := h1.2,
show R ∨ Q,
  from or.inr h2

-- 4ª demostración
example 
  (h1 : P ∧ Q)
  : R ∨ Q :=
show R ∨ Q,
  from or.inr h1.2

-- 5ª demostración
example 
  (h1 : P ∧ Q)
  : R ∨ Q :=
or.inr h1.2

-- 6ª demostración
example 
  (h1 : P ∧ Q)
  : R ∨ Q :=
by tauto

-- 7ª demostración
example 
  (h1 : P ∧ Q)
  : R ∨ Q :=
by finish

