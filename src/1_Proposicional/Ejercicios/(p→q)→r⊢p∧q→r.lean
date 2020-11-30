-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    (p → q) → r ⊢ p ∧ q → r
-- ----------------------------------------------------

import tactic
variables (p q r : Prop)

-- 1ª demostración
example
  (H : (p → q) → r)
  : p ∧ q → r :=
begin
  intro Hpq,
  apply H,
  intro Hp,
  exact Hpq.right,
end

-- 2ª demostración
example
  (H : (p → q) → r)
  : p ∧ q → r :=
begin
  intro Hpq,
  apply H,
  exact (λ Hp, Hpq.right),
end

-- 3ª demostración
example
  (H : (p → q) → r)
  : p ∧ q → r :=
begin
  intro Hpq,
  exact H (λ Hp, Hpq.right),
end

-- 4ª demostración
example
  (H : (p → q) → r)
  : p ∧ q → r :=
λ Hpq, H (λ _, Hpq.right)

-- 5ª demostración
example
  (H : (p → q) → r)
  : p ∧ q → r :=
assume Hpq : p ∧ q,
have H1 : p → q, from
  assume Hp : p,
  show q,
    from and.right Hpq,
show r,
  from H H1

-- 6ª demostración
example
  (H : (p → q) → r)
  : p ∧ q → r :=
-- by hint
by finish
