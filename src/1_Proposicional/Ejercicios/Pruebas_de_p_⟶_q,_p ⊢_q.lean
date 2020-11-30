-- ----------------------------------------------------
-- Ejercicio. Demostrar
--      p ⟶ q, p ⊢ q
-- ----------------------------------------------------

import tactic
variables (p q : Prop)

-- 1ª demostración
example
  (Hpq : p → q)
  (Hp  : p)
  : q :=
Hpq Hp

-- 2ª demostración
example
  (Hpq : p → q)
  (Hp  : p)
  : q :=
by tauto
