-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    p → (q → r) ⊢ q → (p → r)
-- ----------------------------------------------------

import tactic
variables (p q r : Prop)

-- 1ª demostración
example
  (Hpqr : p → (q → r))
  : q → (p → r) :=
begin
  intro Hq,
  intro Hp,
  have Hqr : q → r,
    from Hpqr Hp,
  apply Hqr,
  exact Hq,
end

-- 2ª demostración
example
  (Hpqr : p → (q → r))
  : q → (p → r) :=
begin
  intro Hq,
  intro Hp,
  have Hqr : q → r,
    from Hpqr Hp,
  exact Hqr Hq,
end

-- 3ª demostración
example
  (Hpqr : p → (q → r))
  : q → (p → r) :=
begin
  intro Hq,
  intro Hp,
  exact (Hpqr Hp) Hq,
end

-- 4ª demostración
example
  (Hpqr : p → (q → r))
  : q → (p → r) :=
begin
  intros Hq Hp,
  exact (Hpqr Hp) Hq,
end

-- 5ª demostración
example
  (Hpqr : p → (q → r))
  : q → (p → r) :=
λ Hq Hp, (Hpqr Hp) Hq

-- 6ª demostración
example
  (Hpqr : p → (q → r))
  : q → (p → r) :=
begin
  intros Hq Hp,
  apply Hpqr,
  { exact Hp, },
  { exact Hq, },
end

-- 7ª demostración
example
  (Hpqr : p → (q → r))
  : q → (p → r) :=
assume Hq : q,
assume Hp : p,
have Hqr : q → r,
  from Hpqr Hp,
show r,
  from Hqr Hq

-- 8ª demostración
example
  (Hpqr : p → (q → r))
  : q → (p → r) :=
assume Hq : q,
assume Hp : p,
have Hqr : q → r,
  from Hpqr Hp,
Hqr Hq

-- 9ª demostración
example
  (Hpqr : p → (q → r))
  : q → (p → r) :=
assume Hq : q,
assume Hp : p,
(Hpqr Hp) Hq

-- 10ª demostración
example
  (Hpqr : p → (q → r))
  : q → (p → r) :=
λ Hq Hp, (Hpqr Hp) Hq

-- 11ª demostración
example
  (Hpqr : p → (q → r))
  : q → (p → r) :=
-- by hint
by tauto

-- 12ª demostración
example
  (Hpqr : p → (q → r))
  : q → (p → r) :=
by finish
