-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    p ⊢ p ∨ p
-- ----------------------------------------------------

import tactic
variables (p : Prop)

-- 1ª demostración
example
  (H : p)
  : p ∨ p :=
-- by library_search
or.inl H

-- 2ª demostración
example
  (H : p)
  : p ∨ p :=
-- by hint
by tauto

-- 3ª demostración
example
  (H : p)
  : p ∨ p :=
by finish
