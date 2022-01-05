-- Pruebas de P, P → Q, P → (Q → R) ⊢ R
-- ====================================

-- ----------------------------------------------------
-- Ej 1. (p. 6) Demostrar que
--    P, P → Q, P → (Q → R) ⊢ R
-- ----------------------------------------------------

import tactic

variables (P Q R : Prop)

-- 1ª demostración
example
  (h1 : P)
  (h2 : P → Q)
  (h3 : P → (Q → R))
  : R :=
have h4 : Q,
  from h2 h1,
have h5 : Q → R,
  from h3 h1,
show R,
  from h5 h4

-- 2ª demostración
example
  (h1 : P)
  (h2 : P → Q)
  (h3 : P → (Q → R))
  : R :=
have h4 : Q     := h2 h1,
have h5 : Q → R := h3 h1,
show R, from h5 h4

-- 3ª demostración
example
  (h1 : P)
  (h2 : P → Q)
  (h3 : P → (Q → R))
  : R :=
show R, from (h3 h1) (h2 h1)

-- 4ª demostración
example
  (h1 : P)
  (h2 : P → Q)
  (h3 : P → (Q → R))
  : R :=
(h3 h1) (h2 h1)

-- 5ª demostración
example
  (h1 : P)
  (h2 : P → Q)
  (h3 : P → (Q → R))
  : R :=
-- by hint
by finish

-- 6ª demostración
example
  (h1 : P)
  (h2 : P → Q)
  (h3 : P → (Q → R))
  : R :=
begin
  apply h3,
  { exact h1, },
  { apply h2,
    exact h1, },
end

-- 7ª demostración
example
  (h1 : P)
  (h2 : P → Q)
  (h3 : P → (Q → R))
  : R :=
begin
  apply h3,
  { exact h1, },
  { exact h2 h1, },
end

-- 7ª demostración
example
  (h1 : P)
  (h2 : P → Q)
  (h3 : P → (Q → R))
  : R :=
begin
  { exact (h3 h1) (h2 h1), },
end

-- 8ª demostración
example
  (h1 : P)
  (h2 : P → Q)
  (h3 : P → (Q → R))
  : R :=
by exact (h3 h1) (h2 h1)

-- 9ª demostración
example
  (h1 : P)
  (h2 : P → Q)
  (h3 : P → (Q → R))
  : R :=
(h3 h1) (h2 h1)
