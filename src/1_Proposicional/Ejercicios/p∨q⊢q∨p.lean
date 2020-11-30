-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    p ∨ q ⊢ q ∨ p
-- ----------------------------------------------------

import tactic
variables (p q : Prop)

-- 1ª demostración
example
  (H : p ∨ q)
  : q ∨ p :=
begin
  cases H with Hp Hq,
  { right,
    exact Hp, },
  { left,
    exact Hq, },
end

-- 2ª demostración
example
  (H : p ∨ q)
  : q ∨ p :=
begin
  cases H with Hp Hq,
  { exact or.inr Hp, },
  { exact or.inl Hq, },
end

-- 3ª demostración
example
  (H : p ∨ q)
  : q ∨ p :=
or.elim H
  ( assume Hp : p,
    show q ∨ p,
      from or.inr Hp)
  ( assume Hq : q,
    show q ∨ p,
      from or.inl Hq)

-- 4ª demostración
example
  (H : p ∨ q)
  : q ∨ p :=
or.elim H
  ( assume Hp : p,
    or.inr Hp)
  ( assume Hq : q,
    or.inl Hq)

-- 5ª demostración
example
  (H : p ∨ q)
  : q ∨ p :=
or.elim H
  ( λ Hp, or.inr Hp)
  ( λ Hq, or.inl Hq)

-- 6ª demostración
example
  (H : p ∨ q)
  : q ∨ p :=
or.elim H or.inr or.inl

-- 7ª demostración
example
  (H : p ∨ q)
  : q ∨ p :=
-- by library_search
or.swap H

-- 8ª demostración
example
  (H : p ∨ q)
  : q ∨ p :=
-- by hint
by tauto

-- 9ª demostración
example
  (H : p ∨ q)
  : q ∨ p :=
by finish
