-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    ¬p ⊢ p → q
-- ----------------------------------------------------

import tactic
variables (p q : Prop)

-- 1ª demostración
example
  (H : ¬p)
  : p → q :=
begin
  intro Hp,
  exfalso,
  apply H,
  exact Hp,
end

-- 2ª demostración
example
  (H : ¬p)
  : p → q :=
begin
  intro Hp,
  exfalso,
  exact H Hp,
end

-- 3ª demostración
example
  (H : ¬p)
  : p → q :=
begin
  intro Hp,
  exact absurd Hp H,
end

-- 4ª demostración
example
  (H : ¬p)
  : p → q :=
λ Hp, absurd Hp H

-- 5ª demostración
example
  (H : ¬p)
  : p → q :=
-- by library_search
not.elim H

-- 6ª demostración
example
  (H : ¬p)
  : p → q :=
assume Hp : p,
show q,
  from absurd Hp H
