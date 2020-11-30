-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    q ⊢ p ∨ q
-- ----------------------------------------------------

import tactic
variables (p q : Prop)

-- 1ª demostración
example
  (H : q)
  : p ∨ q :=
begin
  right,
  exact H,
end

-- 2ª demostración
example
  (H : q)
  : p ∨ q :=
or.intro_right p H

-- 3ª demostración
example
  (H : q)
  : p ∨ q :=
-- by library_search
or.inr H

-- 4ª demostración
example
  (H : q)
  : p ∨ q :=
-- by hint
by tauto

-- 5ª demostración
example
  (H : q)
  : p ∨ q :=
by finish
