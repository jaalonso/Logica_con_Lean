-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    ¬q → ¬p ⊢ p → q
-- ----------------------------------------------------

import tactic
variables (p q : Prop)

open_locale classical

-- 1ª demostración
example
  (H : ¬q → ¬p)
  : p → q :=
begin
  intro Hp,
  by_contra Hnq,
  apply not.elim _ Hp,
  exact H Hnq,
end

-- 2ª demostración
example
  (H : ¬q → ¬p)
  : p → q :=
-- by library_search
not_imp_not.mp H

-- 3ª demostración
example
  (H : ¬q → ¬p)
  : p → q :=
assume Hp : p,
show q, from
  by_contradiction
    ( assume Hnq : ¬q,
      have Hnp : ¬p,
        from H Hnq,
      show false,
        from Hnp Hp )

-- 4ª demostración
example
  (H : ¬q → ¬p)
  : p → q :=
-- by hint
by tauto

-- 5ª demostración
example
  (H : ¬q → ¬p)
  : p → q :=
by finish
