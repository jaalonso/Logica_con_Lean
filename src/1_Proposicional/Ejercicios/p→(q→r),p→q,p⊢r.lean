-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    p → (q → r), p → q, p ⊢ r
-- ----------------------------------------------------

import tactic
variables (p q r : Prop)

-- 1ª demostración
example
  (Hpqr : p → (q → r))
  (Hpq  : p → q)
  (Hp   : p)
  : r :=
begin
  have Hqr : q → r, from Hpqr Hp,
  apply Hqr,
  apply Hpq,
  exact Hp,
end

-- 2ª demostración
example
  (Hpqr : p → (q → r))
  (Hpq  : p → q)
  (Hp   : p)
  : r :=
begin
  have Hqr : q → r, from Hpqr Hp,
  apply Hqr,
  exact Hpq Hp,
end

-- 3ª demostración
example
  (Hpqr : p → (q → r))
  (Hpq  : p → q)
  (Hp   : p)
  : r :=
begin
  have Hqr : q → r, from Hpqr Hp,
  exact Hqr (Hpq Hp),
end

-- 4ª demostración
example
  (Hpqr : p → (q → r))
  (Hpq  : p → q)
  (Hp   : p)
  : r :=
(Hpqr Hp) (Hpq Hp)

-- 5ª demostración
example
  (Hpqr : p → (q → r))
  (Hpq  : p → q)
  (Hp   : p)
  : r :=
-- by hint
by finish
