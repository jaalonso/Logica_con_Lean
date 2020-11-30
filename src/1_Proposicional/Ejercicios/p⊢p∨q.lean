-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    p ⊢ p ∨ q
-- ----------------------------------------------------

import tactic
variables (p q : Prop)

-- 1ª demostración
example
  (H : p)
  : p ∨ q :=
begin
  left,
  exact H,
end

-- 2ª demostración
example
  (H : p)
  : p ∨ q :=
or.intro_left q H

-- 3ª demostración
example
  (H : p)
  : p ∨ q :=
-- by library_search
or.inl H

-- 4ª demostración
example
  (H : p)
  : p ∨ q :=
-- by hint
by tauto

-- 5ª demostración
example
  (H : p)
  : p ∨ q :=
by finish
