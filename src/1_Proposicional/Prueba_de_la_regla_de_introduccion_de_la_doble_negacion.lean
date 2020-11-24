-- Regla de introducción de la doble negación
-- ==========================================

-- ----------------------------------------------------
-- Ej. 1. (p. 21) Demostrar
--    P ⊢ ¬¬P
-- ----------------------------------------------------

import tactic
variable (P : Prop)

-- 1ª demostración
example
  (h1 : P)
  : ¬¬P :=
not.intro
  ( assume h2: ¬P,
    show false,
      from h2 h1)

-- 2ª demostración
example
  (h1 : P)
  : ¬¬P :=
assume h2: ¬P,
show false,
  from h2 h1

-- 3ª demostración
example
  (h1 : P)
  : ¬¬P :=
assume h2: ¬P, h2 h1

-- 4ª demostración
example
  (h1 : P)
  : ¬¬P :=
λ h2, h2 h1

-- 5ª demostración
example
  (h1 : P)
  : ¬¬P :=
not_not.mpr h1

-- 6ª demostración
example
  (h1 : P)
  : ¬¬P :=
not_not_intro h1

-- 7ª demostración
example
  (h1 : P)
  : ¬¬P :=
begin
  intro h2,
  exact h2 h1,
end

-- 8ª demostración
example
  (h1 : P)
  : ¬¬P :=
by tauto

-- 9ª demostración
example
  (h1 : P)
  : ¬¬P :=
by finish
