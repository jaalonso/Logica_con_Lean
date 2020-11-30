-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    ¬(¬p ∧ ¬q) ⊢ p ∨ q
-- ----------------------------------------------------

import tactic
variables (p q r : Prop)

open_locale classical

-- 1ª demostración
example
  (H : ¬(¬p ∧ ¬q))
  : p ∨ q :=
begin
  by_cases Hp : p,
  { exact or.inl Hp, },
  { by_cases Hq : q,
    { exact or.inr Hq, },
    { exfalso,
      apply H,
      exact and.intro Hp Hq, }},
end

-- 2ª demostración
example
  (H : ¬(¬p ∧ ¬q))
  : p ∨ q :=
-- by library_search
or_iff_not_and_not.mpr H

-- 3ª demostración
example
  (H : ¬(¬p ∧ ¬q))
  : p ∨ q :=
or.elim (em p)
  ( assume Hp : p,
    show p ∨ q ,
      from or.inl Hp)
  ( assume Hnp : ¬p,
    show p ∨ q, from
      or.elim (em q)
        ( assume Hq : q,
          show p ∨ q,
            from or.inr Hq)
        ( assume Hnq : ¬q,
          have H' : ¬p ∧ ¬q,
            from and.intro Hnp Hnq,
          show p ∨ q,
            from not.elim H H'))

-- 4ª demostración
example
  (H : ¬(¬p ∧ ¬q))
  : p ∨ q :=
or.elim (em p)
  or.inl
  (λ Hnp, or.elim (em q)
            or.inr
            (λ Hnq, not.elim H (and.intro Hnp Hnq)))

-- 5ª demostración
example
  (H : ¬(¬p ∧ ¬q))
  : p ∨ q :=
-- by hint
by tauto

-- 6ª demostración
example
  (H : ¬(¬p ∧ ¬q))
  : p ∨ q :=
by finish
