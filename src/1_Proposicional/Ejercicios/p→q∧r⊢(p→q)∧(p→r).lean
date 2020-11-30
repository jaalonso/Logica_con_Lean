-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    p → q ∧ r ⊢ (p → q) ∧ (p → r)
-- ----------------------------------------------------

import tactic
variables (p q r : Prop)

-- 1ª demostración
example
  (H : p → q ∧ r)
  : (p → q) ∧ (p → r) :=
begin
  split,
  { intro Hp,
    have Hqr : q ∧ r,
      from H Hp,
    exact Hqr.left, },
  { intro Hp,
    have Hqr : q ∧ r,
      from H Hp,
    exact Hqr.right, },
end

-- 2ª demostración
example
  (H : p → q ∧ r)
  : (p → q) ∧ (p → r) :=
begin
  split,
  { intro Hp,
    exact (H Hp).left, },
  { intro Hp,
    exact (H Hp).right, },
end

-- 3ª demostración
example
  (H : p → q ∧ r)
  : (p → q) ∧ (p → r) :=
⟨λ Hp, (H Hp).left,
 λ Hp, (H Hp).right⟩

-- 4ª demostración
example
  (H : p → q ∧ r)
  : (p → q) ∧ (p → r) :=
have Hpq : p → q, from
  assume Hp : p,
  have Hqr : q ∧ r,
    from H Hp,
  show q,
    from and.left Hqr,
have Hpr : p → r, from
  assume Hp : p,
  have Hqr : q ∧ r,
    from H Hp,
  show r,
    from and.right Hqr,
show (p → q) ∧ (p → r),
  from and.intro Hpq Hpr

-- 5ª demostración
example
  (H : p → q ∧ r)
  : (p → q) ∧ (p → r) :=
and.intro
  ( assume Hp : p,
    have Hqr : q ∧ r,
      from H Hp,
    show q,
      from and.left Hqr)
  ( assume Hp : p,
    have Hqr : q ∧ r,
      from H Hp,
    show r,
      from and.right Hqr)

-- 6ª demostración
example
  (H : p → q ∧ r)
  : (p → q) ∧ (p → r) :=
-- by library_search
imp_and_distrib.mp H

-- 7ª demostración
example
  (H : p → q ∧ r)
  : (p → q) ∧ (p → r) :=
-- by hint
by finish
