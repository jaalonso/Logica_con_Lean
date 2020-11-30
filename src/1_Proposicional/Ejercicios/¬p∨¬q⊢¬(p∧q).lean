-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    ¬p ∨ ¬q ⊢ ¬(p ∧ q)
-- ----------------------------------------------------

import tactic
variables (p q : Prop)

-- 1ª demostración
example
  (H : ¬p ∨ ¬q)
  : ¬(p ∧ q) :=
begin
  intro Hpq,
  cases H with Hnp Hnq,
  { apply Hnp,
    exact Hpq.left, },
  { apply Hnq,
    exact Hpq.right, },
end

-- 2ª demostración
example
  (H : ¬p ∨ ¬q)
  : ¬(p ∧ q) :=
begin
  intro Hpq,
  cases H with Hnp Hnq,
  { exact Hnp Hpq.1, },
  { exact Hnq Hpq.2, },
end

-- 3ª demostración
example
  (H : ¬p ∨ ¬q)
  : ¬(p ∧ q) :=
begin
  intro Hpq,
  exact or.elim H (λ Hnp, Hnp Hpq.1) (λ Hnq, Hnq Hpq.2),
end

-- 4ª demostración
example
  (H : ¬p ∨ ¬q)
  : ¬(p ∧ q) :=
λ Hpq, or.elim H (λ Hnp, Hnp Hpq.1) (λ Hnq, Hnq Hpq.2)

-- 5ª demostración
example
  (H : ¬p ∨ ¬q)
  : ¬(p ∧ q) :=
-- by library_search
not_and_distrib.mpr H

-- 6ª demostración
example
  (H : ¬p ∨ ¬q)
  : ¬(p ∧ q) :=
assume Hpq : p ∧ q,
or.elim H
  ( assume Hnp : ¬p,
    show false,
      from Hnp (and.left Hpq))
  ( assume Hnq : ¬q,
    show false,
      from Hnq (and.right Hpq))

-- 7ª demostración
example
  (H : ¬p ∨ ¬q)
  : ¬(p ∧ q) :=
-- by hint
by tauto

-- 8ª demostración
example
  (H : ¬p ∨ ¬q)
  : ¬(p ∧ q) :=
by finish
