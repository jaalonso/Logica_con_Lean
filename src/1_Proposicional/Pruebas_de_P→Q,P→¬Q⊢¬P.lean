-- Pruebas de P → Q, P → ¬Q ⊢ ¬P
-- =============================

import tactic

variables (P Q : Prop)

-- ----------------------------------------------------
-- Ej. 1. (p. 16) Demostrar
--    P → Q, P → ¬Q ⊢ ¬P
-- ----------------------------------------------------

-- 1ª demostración
example
  (h1 : P → Q)
  (h2 : P → ¬Q)
  : ¬P :=
assume h3 : P,
have h4 : Q,
  from h1 h3,
have h5 : ¬Q,
  from h2 h3,
show false,
  from h5 h4

-- 2ª demostración
example
  (h1 : P → Q)
  (h2 : P → ¬Q)
  : ¬P :=
assume h3 : P,
have h4 : Q  := h1 h3,
have h5 : ¬Q := h2 h3,
show false,
  from h5 h4

-- 3ª demostración
example
  (h1 : P → Q)
  (h2 : P → ¬Q)
  : ¬P :=
assume h3 : P,
show false,
  from (h2 h3) (h1 h3)

-- 4ª demostración
example
  (h1 : P → Q)
  (h2 : P → ¬Q)
  : ¬P :=
assume h3 : P, (h2 h3) (h1 h3)

-- 5ª demostración
example
  (h1 : P → Q)
  (h2 : P → ¬Q)
  : ¬P :=
λ h, (h2 h) (h1 h)

-- 6ª demostración
example
  (h1 : P → Q)
  (h2 : P → ¬Q)
  : ¬P :=
begin
  intro h,
  have h3 : ¬Q := h2 h,
  apply h3,
  apply h1,
  exact h,
end

-- 7ª demostración
example
  (h1 : P → Q)
  (h2 : P → ¬Q)
  : ¬P :=
begin
  intro h,
  have h3 : ¬Q := h2 h,
  apply h3,
  exact h1 h,
end

-- 8ª demostración
example
  (h1 : P → Q)
  (h2 : P → ¬Q)
  : ¬P :=
begin
  intro h,
  have h3 : ¬Q := h2 h,
  exact h3 (h1 h),
end

-- 9ª demostración
example
  (h1 : P → Q)
  (h2 : P → ¬Q)
  : ¬P :=
begin
  intro h,
  exact (h2 h) (h1 h),
end

-- 10ª demostración
example
  (h1 : P → Q)
  (h2 : P → ¬Q)
  : ¬P :=
λ h, (h2 h) (h1 h)

-- 11ª demostración
example
  (h1 : P → Q)
  (h2 : P → ¬Q)
  : ¬P :=
-- by hint
by finish

-- 12ª demostración
example
  (h1 : P → Q)
  (h2 : P → ¬Q)
  : ¬P :=
by tauto!
