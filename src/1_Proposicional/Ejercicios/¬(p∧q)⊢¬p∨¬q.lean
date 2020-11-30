-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    ¬(p ∧ q) ⊢ ¬p ∨ ¬q
-- ----------------------------------------------------

import tactic
variables (p q r : Prop)

open_locale classical

-- 1ª demostración
example
  (H : ¬(p ∧ q))
  : ¬p ∨ ¬q :=
begin
  by_cases Hp : p,
  { by_cases Hq : q,
    { exfalso,
      apply H,
      exact ⟨Hp, Hq⟩, },
    { exact or.inr Hq, }},
  { exact or.inl Hp, },
end

-- 2ª demostración
example
  (H : ¬(p ∧ q))
  : ¬p ∨ ¬q :=
if Hp : p
then if Hq : q
     then not.elim H ⟨Hp, Hq⟩
     else or.inr Hq
else or.inl Hp

-- 3ª demostración
example
  (H : ¬(p ∧ q))
  : ¬p ∨ ¬q :=
-- by library_search
not_and_distrib.mp H

-- 4ª demostración
example
  (H : ¬(p ∧ q))
  : ¬p ∨ ¬q :=
or.elim (em p)
  ( assume Hp : p,
    or.elim (em q)
      ( assume Hq : q,
        show ¬p ∨ ¬q,
          from not.elim H ⟨Hp, Hq⟩)
      ( assume Hnq : ¬q,
        show ¬p ∨ ¬q,
          from or.inr Hnq))
  ( assume Hnp : ¬p,
    show ¬p ∨ ¬q,
      from or.inl Hnp)

-- 5ª demostración
example
  (H : ¬(p ∧ q))
  : ¬p ∨ ¬q :=
or.elim (em p)
  (λ Hp, or.elim (em q)
           (λ Hq, not.elim H ⟨Hp, Hq⟩)
           or.inr)
  or.inl

-- 6ª demostración
example
  (H : ¬(p ∧ q))
  : ¬p ∨ ¬q :=
-- by hint
by tauto

-- 7ª demostración
example
  (H : ¬(p ∧ q))
  : ¬p ∨ ¬q :=
by finish
