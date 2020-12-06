-- Pruebas del modus tollens
-- =========================

-- ----------------------------------------------------
-- Ej. 1. (p. 20) Demostrar
--    P → Q, ¬Q ⊢ ¬P
-- ----------------------------------------------------

import tactic

variables (P Q : Prop)

-- 1ª demostración
example
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
assume h3 : P,
have h4 : Q,
  from h1 h3,
show false,
  from h2 h4

-- 2ª demostración
example
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
assume h3 : P,
have h4 : Q := h1 h3,
show false,
  from h2 h4

-- 3ª demostración
example
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
assume h3 : P,
show false,
  from h2 (h1 h3)

-- 4ª demostración
example
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
assume h3 : P, h2 (h1 h3)

-- 5ª demostración
example
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
λ h3, h2 (h1 h3)

-- 6ª demostración
example
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
h2 ∘ h1

-- 7ª demostración
example
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
-- by library_search
mt h1 h2

-- 8ª demostración
example
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
begin
  intro h,
  apply h2,
  apply h1,
  exact h,
end

-- 9ª demostración
example
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
begin
  intro h,
  exact h2 (h1 h),
end

-- 10ª demostración
example
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
λ h, h2 (h1 h)

-- 11ª demostración
example
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
-- by hint
by tauto

-- 12ª demostración
example
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
by finish
