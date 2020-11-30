-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    p → (q → r) ⊢ (p → q) → (p → r)
-- ----------------------------------------------------

import tactic
variables (p q r : Prop)

-- 1ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
begin
  intros Hpq Hp,
  have Hqr : q → r,
    from Hpqr Hp,
  apply Hqr,
  apply Hpq,
  exact Hp,
end

-- 2ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
begin
  intros Hpq Hp,
  have Hqr : q → r,
    from Hpqr Hp,
  apply Hqr,
  exact Hpq Hp,
end

-- 3ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
begin
  intros Hpq Hp,
  have Hqr : q → r,
    from Hpqr Hp,
  exact Hqr (Hpq Hp),
end

-- 4ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
begin
  intros Hpq Hp,
  exact (Hpqr Hp) (Hpq Hp),
end

-- 5ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
λ Hpq Hp, (Hpqr Hp) (Hpq Hp)

-- 6ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
assume Hpq : p → q,
assume Hp : p,
have Hqr : q → r,
  from Hpqr Hp,
have Hq : q,
  from Hpq Hp,
show r,
  from Hqr Hq

-- 7ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
assume Hpq : p → q,
assume Hp : p,
have Hqr : q → r,
  from Hpqr Hp,
have Hq : q,
  from Hpq Hp,
Hqr Hq

-- 8ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
assume Hpq : p → q,
assume Hp : p,
have Hqr : q → r,
  from Hpqr Hp,
Hqr (Hpq Hp)

-- 9ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
assume Hpq : p → q,
assume Hp : p,
(Hpqr Hp) (Hpq Hp)

-- 10ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
λ Hpq Hp, (Hpqr Hp) (Hpq Hp)

-- 11ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
-- by hint
by finish
