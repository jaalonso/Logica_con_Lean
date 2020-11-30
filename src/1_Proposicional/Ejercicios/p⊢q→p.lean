-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    p ⊢ q → p
-- ----------------------------------------------------

import tactic
variables (p q : Prop)

-- 1ª demostración
example
  (Hp : p)
  : q → p :=
begin
  intro Hq,
  exact Hp,
end

-- 2ª demostración
example
  (H : p)
  : q → p :=
λ _, H

-- 3ª demostración
example
  (Hp : p)
  : q → p :=
assume Hq : q,
show p,
  from Hp

-- 4ª demostración
example
  (Hp : p)
  : q → p :=
-- by library_search
imp_intro Hp

-- 5ª demostración
example
  (Hp : p)
  : q → p :=
-- by hint
by tauto

-- 6ª demostración
example
  (Hp : p)
  : q → p :=
by finish
