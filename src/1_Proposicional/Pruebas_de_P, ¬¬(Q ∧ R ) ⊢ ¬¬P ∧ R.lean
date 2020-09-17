-- Pruebas de P, ¬¬(Q ∧ R) ⊢ ¬¬P ∧ R
-- =================================

-- Ej. 1. Demostrar
--    P, ¬¬(Q ∧ R) ⊢ ¬¬P ∧ R

import tactic

variables (P Q R : Prop)

example
  (h1 : P)
  (h2 : ¬¬(Q ∧ R)
  : ¬¬P ∧ R :=
have h3 : ¬¬P,
  from not_not_intro h1,
sorry   

