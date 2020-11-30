-- ----------------------------------------------------
-- Ejercicio Demostrar
--    p → (q → r) ⊢ p ∧ q → r
-- ----------------------------------------------------

import tactic
variables (p q r : Prop)

-- 1ª demostración
example
  (H : p → (q → r))
  : p ∧ q → r :=
begin
  intro Hpq,
  apply H,
  { exact Hpq.left, },
  { exact Hpq.right, },
end

-- 2ª demostración
example
  (H : p → (q → r))
  : p ∧ q → r :=
begin
  intro Hpq,
  exact (H Hpq.left) Hpq.right,
end

-- 3ª demostración
example
  (H : p → (q → r))
  : p ∧ q → r :=
λ Hpq, (H Hpq.left) Hpq.right

-- 4ª demostración
example
  (H : p → (q → r))
  : p ∧ q → r :=
λ Hpq, H Hpq.1 Hpq.2

-- 5ª demostración
example
  (H : p → (q → r))
  : p ∧ q → r :=
assume Hpq : p ∧ q,
have Hp : p,
  from and.left Hpq,
have Hq : q,
  from and.right Hpq,
have Hqr : q → r,
  from H Hp,
show r,
  from Hqr Hq

-- 6ª demostración
example
  (H : p → (q → r))
  : p ∧ q → r :=
-- by library_search
and_imp.mpr H

-- 7ª demostración
example
  (H : p → (q → r))
  : p ∧ q → r :=
-- by hint
by tauto

-- 8ª demostración
example
  (H : p → (q → r))
  : p ∧ q → r :=
by finish
