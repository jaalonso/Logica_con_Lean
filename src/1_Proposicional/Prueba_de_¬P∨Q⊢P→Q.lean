-- Prueba de ¬P ∨ Q ⊢ P → Q
-- ========================

-- Ej. 1. Demostrar
--    ¬P ∨ Q ⊢ P → Q

import tactic

variables (P Q : Prop)

-- 1ª demostración
example 
  (h1 : ¬P ∨ Q)
  : P → Q :=
sorry