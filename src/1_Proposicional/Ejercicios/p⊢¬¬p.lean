-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    p ⊢ ¬¬p
-- ----------------------------------------------------

import tactic
variable (p : Prop)

-- 1ª demostración
example
  (H : p)
  : ¬¬p :=
begin
  intro H1,
  apply H1 H,
end

-- 2ª demostración
example
  (H : p)
  : ¬¬p :=
λ H1, H1 H

-- 3ª demostración
example
  (H : p)
  : ¬¬p :=
-- by library_search
not_not.mpr H

-- 4ª demostración
example
  (H : p)
  : ¬¬p :=
assume H1 : ¬p,
show false,
  from H1 H

-- 5ª demostración
example
  (H : p)
  : ¬¬p :=
-- by hint
by tauto

-- 6ª demostración
example
  (H : p)
  : ¬¬p :=
by finish
