-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    (p → r) ∧ (q → r) ⊢ p ∨ q → r
-- ----------------------------------------------------

import tactic
variables (p q r : Prop)

-- 1ª demostración
example
  (H : (p → r) ∧ (q → r))
  : p ∨ q → r :=
begin
  cases H with Hpr Hqr,
  intro Hpq,
  cases Hpq with Hp Hq,
  { apply Hpr,
    exact Hp, },
  { apply Hqr,
    exact Hq, },
end

-- 2ª demostración
example
  (H : (p → r) ∧ (q → r))
  : p ∨ q → r :=
begin
  cases H with Hpr Hqr,
  intro Hpq,
  cases Hpq with Hp Hq,
  { exact Hpr Hp, },
  { exact Hqr Hq, },
end

-- 3ª demostración
example
  (H : (p → r) ∧ (q → r))
  : p ∨ q → r :=
begin
  intro Hpq,
  cases Hpq with Hp Hq,
  { exact H.left  Hp, },
  { exact H.right Hq, },
end

-- 4ª demostración
example
  (H : (p → r) ∧ (q → r))
  : p ∨ q → r :=
-- by library_search
or_imp_distrib.mpr H

-- 5ª demostración
example
  (H : (p → r) ∧ (q → r))
  : p ∨ q → r :=
assume Hpq : p ∨ q,
or.elim Hpq
  ( assume Hp : p,
    have Hpr: p → r,
      from and.left H,
    show r,
      from Hpr Hp )
  ( assume Hq : q,
    have Hqr : q → r,
      from and.right H,
    show r,
      from Hqr Hq)

-- 6ª demostración
example
  (H : (p → r) ∧ (q → r))
  : p ∨ q → r :=
assume Hpq : p ∨ q,
or.elim Hpq
  ( assume Hp : p,
    have Hpr: p → r,
      from and.left H,
    Hpr Hp )
  ( assume Hq : q,
    have Hqr : q → r,
      from and.right H,
    Hqr Hq)

-- 7ª demostración
example
  (H : (p → r) ∧ (q → r))
  : p ∨ q → r :=
assume Hpq : p ∨ q,
or.elim Hpq
  ( assume Hp : p,
    H.1 Hp )
  ( assume Hq : q,
    H.2 Hq)

-- 8ª demostración
example
  (H : (p → r) ∧ (q → r))
  : p ∨ q → r :=
assume Hpq : p ∨ q,
or.elim Hpq
  (λ Hp, H.1 Hp)
  (λ Hq, H.2 Hq)

-- 9ª demostración
example
  (H : (p → r) ∧ (q → r))
  : p ∨ q → r :=
assume Hpq : p ∨ q,
or.elim Hpq H.1 H.2

-- 10ª demostración
example
  (H : (p → r) ∧ (q → r))
  : p ∨ q → r :=
λ Hpq, or.elim Hpq H.1 H.2

-- 11ª demostración
example
  (H : (p → r) ∧ (q → r))
  : p ∨ q → r :=
-- by hint
by tauto

-- 12ª demostración
example
  (H : (p → r) ∧ (q → r))
  : p ∨ q → r :=
by finish
