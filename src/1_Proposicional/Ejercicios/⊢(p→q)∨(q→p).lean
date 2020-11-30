-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    ⊢ (p → q) ∨ (q → p)
-- ----------------------------------------------------

import tactic
variables (p q : Prop)

open_locale classical

-- 1ª demostración
example :
  (p → q) ∨ (q → p) :=
begin
  by_cases H1 : p,
  { right,
    intro,
    exact H1, },
  { left,
    intro H2,
    exfalso,
    exact H1 H2, },
end

-- 2ª demostración
example :
  (p → q) ∨ (q → p) :=
begin
  cases (em p) with Hp Hnp,
  { exact or.inr (λ Hq, Hp), },
  { exact or.inl (λ Hp, not.elim Hnp Hp), },
end

-- 3ª demostración
example :
  (p → q) ∨ (q → p) :=
or.elim (em p)
  (λ Hp, or.inr (λ Hq, Hp))
  (λ Hnp, or.inl (λ Hp, not.elim Hnp Hp))

-- 4ª demostración
example :
  (p → q) ∨ (q → p) :=
if Hp : p
   then or.inr (λ _, Hp)
   else or.inl (λ H, not.elim Hp H)

-- 5ª demostración
example :
  (p → q) ∨ (q → p) :=
-- by hint
by tauto

-- 6ª demostración
example :
  (p → q) ∨ (q → p) :=
by finish
