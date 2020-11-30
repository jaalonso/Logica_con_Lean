-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    p ∧ (q → r) ⊢ (p → q) → r
-- ----------------------------------------------------

import tactic
variables (p q r : Prop)

-- 1ª demostración
example
  (H : p ∧ (q → r))
  : (p → q) → r :=
begin
  intro Hpq,
  cases H with Hp Hqr,
  apply Hqr,
  apply Hpq,
  exact Hp,
end

-- 2ª demostración
example
  (H : p ∧ (q → r))
  : (p → q) → r :=
begin
  intro Hpq,
  cases H with Hp Hqr,
  apply Hqr,
  exact Hpq Hp,
end

-- 3ª demostración
example
  (H : p ∧ (q → r))
  : (p → q) → r :=
begin
  intro Hpq,
  cases H with Hp Hqr,
  exact Hqr (Hpq Hp),
end

-- 4ª demostración
example
  (H : p ∧ (q → r))
  : (p → q) → r :=
begin
  intro Hpq,
  exact H.2 (Hpq H.1),
end

-- 5ª demostración
example
  (H : p ∧ (q → r))
  : (p → q) → r :=
λ Hpq, H.2 (Hpq H.1)

-- 6ª demostración
example
  (H : p ∧ (q → r))
  : (p → q) → r :=
assume Hpq : p → q,
have Hp : p,
  from and.left H,
have Hq : q,
  from Hpq Hp,
have Hqr : q → r,
  from H.right,
show r,
  from Hqr Hq

-- 7ª demostració
example
  (H : p ∧ (q → r))
  : (p → q) → r :=
-- by hint
by tauto

-- 8ª demostració
example
  (H : p ∧ (q → r))
  : (p → q) → r :=
-- by hint
by finish
