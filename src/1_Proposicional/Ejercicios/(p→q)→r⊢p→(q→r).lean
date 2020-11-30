-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    (p → q) → r ⊢ p → (q → r)
-- ----------------------------------------------------

import tactic
variables (p q r : Prop)

-- 1ª demostración
example
  (Hpqr : (p → q) → r)
  : p → (q → r) :=
begin
  intros Hp Hq,
  apply Hpqr,
  intro Hp,
  exact Hq,
end

-- 2ª demostración
example
  (Hpqr : (p → q) → r)
  : p → (q → r) :=
begin
  intros Hp Hq,
  apply Hpqr,
  exact (λ Hp, Hq),
end

-- 3ª demostración
example
  (Hpqr : (p → q) → r)
  : p → (q → r) :=
begin
  intros Hp Hq,
  exact Hpqr (λ Hp, Hq),
end

-- 4ª demostración
example
  (Hpqr : (p → q) → r)
  : p → (q → r) :=
λ Hp Hq, Hpqr (λ Hp, Hq)

-- 5ª demostración
example
  (Hpqr : (p → q) → r)
  : p → (q → r) :=
assume Hp : p,
assume Hq : q,
have Hpq : p → q,
  { assume p,
    show q,
      from Hq },
show r,
  from Hpqr Hpq

-- 6ª demostración
example
  (Hpqr : (p → q) → r)
  : p → (q → r) :=
assume Hp : p,
assume Hq : q,
have Hpq : p → q,
  { assume p,
    show q,
      from Hq },
Hpqr Hpq

-- 7ª demostración
example
  (Hpqr : (p → q) → r)
  : p → (q → r) :=
assume Hp : p,
assume Hq : q,
have Hpq : p → q,
  from (λ p, Hq),
Hpqr Hpq

-- 8ª demostración
example
  (Hpqr : (p → q) → r)
  : p → (q → r) :=
assume Hp : p,
assume Hq : q,
Hpqr (λ p, Hq)

-- 9ª demostración
example
  (Hpqr : (p → q) → r)
  : p → (q → r) :=
λ Hp Hq, Hpqr (λ p, Hq)

-- 10ª demostración
example
  (Hpqr : (p → q) → r)
  : p → (q → r) :=
-- by hint
by finish
