-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    ⊢ (p → (q → r)) → ((p → q) → (p → r))
-- ----------------------------------------------------

import tactic
variables (p q r : Prop)

-- 1ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
begin
  intros Hpq Hp,
  apply Hpqr,
  { exact Hp, },
  { apply Hpq,
    exact Hp, },
end

-- 2ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
begin
  intros Hpq Hp,
  apply Hpqr,
  { exact Hp, },
  { exact Hpq Hp, },
end

-- 3ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
begin
  intros Hpq Hp,
  exact Hpqr Hp (Hpq Hp),
end

-- 4ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
λ Hpq Hp, Hpqr Hp (Hpq Hp)

-- 5ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
assume Hpq : p → q,
assume Hp : p,
have Hq : q,
  from Hpq Hp,
have Hqr : q → r,
  from Hpqr Hp,
show r,
  from Hqr Hq

-- 6ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
assume Hpq : p → q,
assume Hp : p,
have Hq : q,
  from Hpq Hp,
have Hqr : q → r,
  from Hpqr Hp,
Hqr Hq

-- 7ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
assume Hpq : p → q,
assume Hp : p,
have Hq : q,
  from Hpq Hp,
(Hpqr Hp) Hq

-- 8ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
assume Hpq : p → q,
assume Hp : p,
(Hpqr Hp) (Hpq Hp)

-- 9ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
λ Hpq Hp, (Hpqr Hp) (Hpq Hp)

-- 10ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
-- by hint
by finish
