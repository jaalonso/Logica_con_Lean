-- Pruebas del silogismo hipotético
-- --------------------------------

import tactic

variables (P Q R : Prop)

-- ----------------------------------------------------
-- Ej. 1. Demostrar que
--    P → Q, Q → R ⊢ P → R
-- ----------------------------------------------------

-- 1º demostración
example
  (h1 : P → Q)
  (h2 : Q → R)
  : P → R :=
assume h : P,
have h3 : Q,
  from h1 h,
show R,
  from h2 h3

variable (h1 : P → Q)
variable (h2 : Q → R)
variable (h : P)
#check h1 h
#check h2 (h1 h)

-- 2º demostración
example
  (h1 : P → Q)
  (h2 : Q → R)
  : P → R :=
assume h : P,
have h3 : Q,
  from h1 h,
h2 h3

-- 3º demostración
example
  (h1 : P → Q)
  (h2 : Q → R)
  : P → R :=
assume h : P,
h2 (h1 h)

-- 4º demostración
example
  (h1 : P → Q)
  (h2 : Q → R)
  : P → R :=
λ h, h2 (h1 h)

-- 5º demostración
example
  (h1 : P → Q)
  (h2 : Q → R)
  : P → R :=
h2 ∘ h1

-- 6º demostración
example
  (h1 : P → Q)
  (h2 : Q → R)
  : P → R :=
begin
  intro h,
  apply h2,
  apply h1,
  exact h,
end

-- 7º demostración
example
  (h1 : P → Q)
  (h2 : Q → R)
  : P → R :=
begin
  intro h,
  apply h2,
  exact h1 h,
end

-- 8º demostración
example
  (h1 : P → Q)
  (h2 : Q → R)
  : P → R :=
begin
  intro h,
  exact h2 (h1 h),
end

-- 9º demostración
example
  (h1 : P → Q)
  (h2 : Q → R)
  : P → R :=
λ h, h2 (h1 h)

-- 10º demostración
example
  (h1 : P → Q)
  (h2 : Q → R)
  : P → R :=
-- by library_search
h2 ∘ h1

-- 11º demostración
example
  (h1 : P → Q)
  (h2 : Q → R)
  : P → R :=
-- by hint
by tauto

-- 12º demostración
example
  (h1 : P → Q)
  (h2 : Q → R)
  : P → R :=
by finish
