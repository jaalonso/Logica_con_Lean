-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    ⊢ p → (q → p)
-- ----------------------------------------------------

import tactic
variables (p q : Prop)

-- 1ª demostración
example :
  p → (q → p) :=
begin
  intros Hp Hq,
  exact Hp,
end

-- 2ª demostración
example :
  p → (q → p) :=
λ Hp _, Hp

-- 3ª demostración
example :
  p → (q → p) :=
assume Hp : p,
assume Hq : q,
show p,
  from Hp

-- 4ª demostración
example :
  p → (q → p) :=
-- by library_search
imp_intro

-- 5ª demostración
example :
  p → (q → p) :=
-- by hint
by tauto

-- 6ª demostración
example :
  p → (q → p) :=
by finish
