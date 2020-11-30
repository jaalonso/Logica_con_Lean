-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    q → r ⊢ p ∨ q → p ∨ r
-- ----------------------------------------------------

import tactic
variables (p q r : Prop)

-- 1ª demostración
example
  (H : q → r)
  : p ∨ q → p ∨ r :=
begin
  intro H1,
  cases H1 with Hp Hq,
  { left,
    exact Hp, },
  { right,
    apply H,
    exact Hq, },
end

-- 2ª demostración
example
  (H : q → r)
  : p ∨ q → p ∨ r :=
begin
  rintro (Hp | Hq),
  { left,
    exact Hp, },
  { right,
    exact H Hq, },
end

-- 3ª demostración
example
  (H : q → r)
  : p ∨ q → p ∨ r :=
begin
  rintro (Hp | Hq),
  { exact or.inl Hp, },
  { exact or.inr (H Hq), },
end

-- 4ª demostración
example
  (H : q → r)
  : p ∨ q → p ∨ r :=
assume H1 : p ∨ q,
or.elim H1
  ( assume Hp : p,
    show p ∨ r,
      from or.inl Hp)
  ( assume Hq : q,
    have Hr : r,
      from H Hq,
    show p ∨ r,
      from or.inr Hr)

-- 5ª demostración
example
  (H : q → r)
  : p ∨ q → p ∨ r :=
assume H1 : p ∨ q,
or.elim H1
  ( assume Hp : p,
    or.inl Hp)
  ( assume Hq : q,
    have Hr : r,
      from H Hq,
    or.inr Hr)

-- 6ª demostración
example
  (H : q → r)
  : p ∨ q → p ∨ r :=
assume H1 : p ∨ q,
or.elim H1
  ( assume Hp : p,
    or.inl Hp)
  ( assume Hq : q,
    or.inr (H Hq))

-- 7ª demostración
example
  (H : q → r)
  : p ∨ q → p ∨ r :=
assume H1 : p ∨ q,
or.elim H1
  ( λ Hp, or.inl Hp)
  ( λ Hq, or.inr (H Hq))

-- 8ª demostración
example
  (H : q → r)
  : p ∨ q → p ∨ r :=
assume H1 : p ∨ q,
or.elim H1
  or.inl
  ( λ Hq, or.inr (H Hq))

-- 9ª demostración
example
  (H : q → r)
  : p ∨ q → p ∨ r :=
λ H1, or.elim H1 or.inl (λ Hq, or.inr (H Hq))

-- 10ª demostración
example
  (H : q → r)
  : p ∨ q → p ∨ r :=
-- by library_search
or.imp_right H
