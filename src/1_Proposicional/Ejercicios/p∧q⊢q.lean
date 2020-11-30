-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    p ∧ q ⊢ q
-- ----------------------------------------------------

import tactic
variables (p q : Prop)

-- 1ª demostración
example
  (H : p ∧ q)
  : q :=
begin
  cases H with Hp Hq,
  exact Hq,
end

-- 2ª demostración
example
  (H : p ∧ q)
  : q :=
and.elim_right H

-- 3ª demostración
example
  (H : p ∧ q)
  : q :=
and.right H

-- 4ª demostración
example
  (H : p ∧ q)
  : q :=
H.right

-- 5ª demostración
example
  (H : p ∧ q)
  : q :=
H.2

-- 6ª demostración
example
  (H : p ∧ q)
  : q :=
-- by library_search
H.right

-- 7ª demostración
example
  (H : p ∧ q)
  : q :=
-- by hint
by tauto

-- 8ª demostración
example
  (H : p ∧ q)
  : q :=
by finish
