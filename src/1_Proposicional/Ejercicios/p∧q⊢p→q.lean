-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    p ∧ q ⊢ p → q
-- ----------------------------------------------------

import tactic
variables (p q : Prop)

-- 1ª demostración
example
  (Hpq : p ∧ q)
  : p → q :=
begin
  intro p,
  exact Hpq.right,
end

-- 2ª demostración
example
  (Hpq : p ∧ q)
  : p → q :=
λ _, Hpq.2

-- 3ª demostración
example
  (Hpq : p ∧ q)
  : p → q :=
assume Hp : p,
show q,
  from and.right Hpq

-- 4ª demostración
example
  (Hpq : p ∧ q)
  : p → q :=
-- by hint
by tauto

-- 5ª demostración
example
  (Hpq : p ∧ q)
  : p → q :=
by finish
