-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    p ∧ q ⊢ p
-- ----------------------------------------------------

import tactic
variables (p q : Prop)

-- 1ª demostración
example
  (H : p ∧ q)
  : p :=
begin
  cases H with Hp Hq,
  exact Hp,
end

-- 2ª demostración
example
  (H : p ∧ q)
  : p :=
and.elim_left H

-- 3ª demostración
example
  (H : p ∧ q)
  : p :=
and.left H

-- 4ª demostración
example
  (H : p ∧ q)
  : p :=
H.left

-- 5ª demostración
example
  (H : p ∧ q)
  : p :=
H.1

-- 6ª demostración
example
  (H : p ∧ q)
  : p :=
-- by library_search
H.left

-- 7ª demostración
example
  (H : p ∧ q)
  : p :=
-- by hint
by tauto

-- 8ª demostración
example
  (H : p ∧ q)
  : p :=
by finish
