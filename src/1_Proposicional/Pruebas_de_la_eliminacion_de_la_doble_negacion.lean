-- Pruebas de la eliminación de la doble negación
-- ==============================================

-- Ej. 1. Demostrar
--     ¬¬P ⊢ P

import tactic

variable (P : Prop)

open_locale classical

-- 1ª demostración
example
  (h1 : ¬¬P)
  : P :=
by_contra 
  ( assume h2 : ¬P,
    show false, 
      from h1 h2)

-- 2ª demostración
example
  (h1 : ¬¬P)
  : P :=
by_contra 
  ( assume h2 : ¬P,
    h1 h2)

-- 3ª demostración
example
  (h1 : ¬¬P)
  : P :=
by_contra (λ h2, h1 h2)

-- 4ª demostración
example
  (h1 : ¬¬P)
  : P :=
not_not.mp h1

-- 6ª demostración
example
  (h1 : ¬¬P)
  : P :=
begin
  by_contra h2,
  exact h1 h2,
end

-- 7ª demostración
example
  (h1 : ¬¬P)
  : P :=
by tauto

-- 8ª demostración
example
  (h1 : ¬¬P)
  : P :=
by finish
