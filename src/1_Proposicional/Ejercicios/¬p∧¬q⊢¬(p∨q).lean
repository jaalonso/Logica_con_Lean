-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    ¬p ∧ ¬q ⊢ ¬(p ∨ q)
-- ----------------------------------------------------

import tactic
variables (p q : Prop)

-- 1ª demostración
example
  (H : ¬p ∧ ¬q)
  : ¬(p ∨ q) :=
begin
  intro H1,
  cases H1 with H2 H3,
  { exact absurd H2 H.1, },
  { exact absurd H3 H.2, },
end

-- 2ª demostración
example
  (H : ¬p ∧ ¬q)
  : ¬(p ∨ q) :=
λ H1, or.elim H1 (λ H2, absurd H2 H.1) (λ H3, absurd H3 H.2)

-- 3ª demostración
example
  (H : ¬p ∧ ¬q)
  : ¬(p ∨ q) :=
-- by library_search
not_or_distrib.mpr H

-- 4ª demostración
example
  (H : ¬p ∧ ¬q)
  : ¬(p ∨ q) :=
assume Hpq : p ∨ q,
or.elim Hpq
  ( assume Hp : p,
    show false,
      from absurd Hp H.left)
  ( assume Hq : q,
    show false,
      from absurd Hq H.right)

-- 5ª demostración
example
  (H : ¬p ∧ ¬q)
  : ¬(p ∨ q) :=
-- by hint
by tauto

-- 6ª demostración
example
  (H : ¬p ∧ ¬q)
  : ¬(p ∨ q) :=
by finish
