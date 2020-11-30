-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    p, q ⊢  p ∧ q
-- ----------------------------------------------------

import tactic
variables (p q : Prop)

-- 1ª demostración
example
  (Hp : p)
  (Hq : q)
  : p ∧ q :=
begin
  split,
  { exact Hp, },
  { exact Hq, },
end

-- 2ª demostración
example
  (Hp : p)
  (Hq : q)
  : p ∧ q :=
and.intro Hp Hq

-- 3ª demostración
example
  (Hp : p)
  (Hq : q)
  : p ∧ q :=
-- by library_search
⟨Hp, Hq⟩

-- 4ª demostración
example
  (Hp : p)
  (Hq : q)
  : p ∧ q :=
-- by hint
by tauto

-- 5ª demostración
example
  (Hp : p)
  (Hq : q)
  : p ∧ q :=
by finish
