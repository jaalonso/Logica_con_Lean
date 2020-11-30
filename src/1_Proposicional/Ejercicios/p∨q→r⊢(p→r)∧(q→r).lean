-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    p ∨ q → r ⊢ (p → r) ∧ (q → r)
-- ----------------------------------------------------

import tactic
variables (p q r : Prop)

-- 1ª demostración
example
  (H : p ∨ q → r)
  : (p → r) ∧ (q → r) :=
begin
  split,
  { intro Hp,
    apply H,
    left,
    exact Hp, },
  { intro Hq,
    apply H,
    right,
    exact Hq, },
end

-- 2ª demostración
example
  (H : p ∨ q → r)
  : (p → r) ∧ (q → r) :=
begin
  split,
  { intro Hp,
    apply H,
    exact or.inl Hp, },
  { intro Hq,
    apply H,
    exact or.inr Hq, },
end

-- 3ª demostración
example
  (H : p ∨ q → r)
  : (p → r) ∧ (q → r) :=
begin
  split,
  { intro Hp,
    exact H (or.inl Hp), },
  { intro Hq,
    exact H (or.inr Hq), },
end

-- 4ª demostración
example
  (H : p ∨ q → r)
  : (p → r) ∧ (q → r) :=
⟨λ Hp, H (or.inl Hp),
 λ Hq, H (or.inr Hq)⟩

-- 5ª demostración
example
  (H : p ∨ q → r)
  : (p → r) ∧ (q → r) :=
-- by library_search
or_imp_distrib.mp H

-- 6ª demostración
example
  (H : p ∨ q → r)
  : (p → r) ∧ (q → r) :=
and.intro
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    show r,
      from H Hpq)
  ( assume Hq : q,
    have Hpq : p ∨ q,
      from or.inr Hq,
    show r,
      from H Hpq)

-- 7ª demostración
example
  (H : p ∨ q → r)
  : (p → r) ∧ (q → r) :=
and.intro
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    H Hpq)
  ( assume Hq : q,
    have Hpq : p ∨ q,
      from or.inr Hq,
    H Hpq)

-- 8ª demostración
example
  (H : p ∨ q → r)
  : (p → r) ∧ (q → r) :=
and.intro
  ( assume Hp : p,
    H (or.inl Hp))
  ( assume Hq : q,
    H (or.inr Hq))

-- 9ª demostración
example
  (H : p ∨ q → r)
  : (p → r) ∧ (q → r) :=
and.intro
  (λ Hp, H (or.inl Hp))
  (λ Hq, H (or.inr Hq))

-- 10ª demostración
example
  (H : p ∨ q → r)
  : (p → r) ∧ (q → r) :=
⟨λ Hp, H (or.inl Hp),
 λ Hq, H (or.inr Hq)⟩
