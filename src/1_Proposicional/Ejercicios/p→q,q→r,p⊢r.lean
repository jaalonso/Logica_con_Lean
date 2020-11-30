-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    p → q, q → r, p ⊢ r
-- ----------------------------------------------------

import tactic
variables (p q r : Prop)

-- 1ª demostracióm
example
  (Hpq : p → q)
  (Hqr : q → r)
  (Hp : p)
  : r :=
begin
  apply Hqr,
  apply Hpq,
  exact Hp,
end

-- 2ª demostracióm
example
  (Hpq : p → q)
  (Hqr : q → r)
  (Hp : p)
  : r :=
begin
  apply Hqr,
  exact Hpq Hp,
end

-- 3ª demostracióm
example
  (Hpq : p → q)
  (Hqr : q → r)
  (Hp : p)
  : r :=
begin
  exact Hqr (Hpq Hp),
end

-- 3ª demostracióm
example
  (Hpq : p → q)
  (Hqr : q → r)
  (Hp : p)
  : r :=
Hqr (Hpq Hp)

-- 4ª demostracióm
example
  (Hpq : p → q)
  (Hqr : q → r)
  (Hp : p)
  : r :=
by tauto

-- 5ª demostracióm
example
  (Hpq : p → q)
  (Hqr : q → r)
  (Hp : p)
  : r :=
have Hq : q,
  from Hpq Hp,
show r,
  from Hqr Hq
