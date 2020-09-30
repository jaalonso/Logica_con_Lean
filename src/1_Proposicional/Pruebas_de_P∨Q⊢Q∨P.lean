-- Pruebas de P ∨ Q ⊢ Q ∨ P
-- ========================

import tactic

variables (P Q R : Prop)

-- Ej. 1. Demostrar
--    P ∨ Q ⊢ Q ∨ P

-- 1ª demostración
example
  (h1 : P ∨ Q)
  : Q ∨ P :=
or.elim h1 
  ( assume h2 : P,
    show Q ∨ P,
      from or.inr h2 )
  ( assume h3 : Q,
    show Q ∨ P,
      from or.inl h3 )

-- 2ª demostración
example
  (h1 : P ∨ Q)
  : Q ∨ P :=
or.elim h1 
  ( λ h, or.inr h )
  ( λ h, or.inl h )

-- 3ª demostración
example
  (h1 : P ∨ Q)
  : Q ∨ P :=
or.elim h1 or.inr or.inl

-- 4ª demostración
example
  (h1 : P ∨ Q)
  : Q ∨ P :=
or.rec or.inr or.inl h1

-- 5ª demostración
example
  (h1 : P ∨ Q)
  : Q ∨ P :=
or.swap h1

-- 6ª demostración
example
  (h1 : P ∨ Q)
  : Q ∨ P :=
begin
  cases h1 with h2 h3,
  { exact or.inr h2, },
  { exact or.inl h3, },
end 

-- 7ª demostración
example
  (P ∨ Q)
  : Q ∨ P :=
begin
  cases ‹P ∨ Q›, 
  { exact or.inr ‹P›, },
  { exact or.inl ‹Q›, },
end 

-- 8ª demostración
example
  (h1 : P ∨ Q)
  : Q ∨ P :=
begin
  cases h1 with h2 h3,
  { right, 
    exact h2, },
  { left, 
    exact h3, },
end 

-- 9ª demostración
example
  (h1 : P ∨ Q)
  : Q ∨ P :=
by tauto

-- 10ª demostración
example
  (h1 : P ∨ Q)
  : Q ∨ P :=
by finish
