-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    p → q, q → r ⊢ p → r
-- ----------------------------------------------------

import tactic
variables (p q r : Prop)

-- 1ª demostración
example
  (Hpq : p → q)
  (Hqr : q → r)
  : p → r :=
begin
  intro Hp,
  apply Hqr,
  apply Hpq,
  exact Hp,
end

-- 2ª demostración
example
  (Hpq : p → q)
  (Hqr : q → r)
  : p → r :=
begin
  intro Hp,
  apply Hqr,
  exact Hpq Hp,
end

-- 3ª demostración
example
  (Hpq : p → q)
  (Hqr : q → r)
  : p → r :=
begin
  intro Hp,
  exact Hqr (Hpq Hp),
end

-- 4ª demostración
example
  (Hpq : p → q)
  (Hqr : q → r)
  : p → r :=
λ Hp, Hqr (Hpq Hp)

-- 5ª demostración
example
  (Hpq : p → q)
  (Hqr : q → r)
  : p → r :=
assume Hp : p,
have Hq : q,
  from Hpq Hp,
show r,
  from Hqr Hq

-- 6ª demostración
example
  (Hpq : p → q)
  (Hqr : q → r)
  : p → r :=
assume Hp : p,
have Hq : q,
  from Hpq Hp,
Hqr Hq

-- 7ª demostración
example
  (Hpq : p → q)
  (Hqr : q → r)
  : p → r :=
assume Hp : p,
Hqr (Hpq Hp)

-- 8ª demostración
example
  (Hpq : p → q)
  (Hqr : q → r)
  : p → r :=
λ Hp, Hqr (Hpq Hp)

-- 9ª demostración
example
  (Hpq : p → q)
  (Hqr : q → r)
  : p → r :=
-- by hint
by tauto

-- 10ª demostración
example
  (Hpq : p → q)
  (Hqr : q → r)
  : p → r :=
by finish
