-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    p ∨ q, ¬p ⊢ q
-- ----------------------------------------------------

import tactic
variables (p q : Prop)

-- 1ª demostración
example
  (Hpq : p ∨ q)
  (Hnp: ¬p)
  : q :=
begin
  cases Hpq with Hp Hq,
  { exact absurd Hp Hnp, },
  { exact Hq, },
end

-- 2ª demostración
example
  (Hpq : p ∨ q)
  (Hnp: ¬p)
  : q :=
or.elim Hpq (λ Hp, absurd Hp Hnp) id

-- 3ª demostración
example
  (Hpq : p ∨ q)
  (Hnp: ¬p)
  : q :=
-- by library_search
or.resolve_left Hpq Hnp

-- 4ª demostración
example
  (Hpq : p ∨ q)
  (Hnp: ¬p)
  : q :=
or.elim Hpq
  ( assume Hp : p,
    show q,
      from absurd Hp Hnp)
  ( assume Hq : q,
    show q,
      from Hq)

-- 5ª demostración
example
  (Hpq : p ∨ q)
  (Hnp: ¬p)
  : q :=
-- by hint
by tauto

-- 6ª demostración
example
  (Hpq : p ∨ q)
  (Hnp: ¬p)
  : q :=
by finish
