-- Pruebas de P → (Q → R), P, ¬R ⊢ ¬Q
-- ==================================

-- ----------------------------------------------------
-- Ej. 1. Demostrar
--    Pruebas de P → (Q → R), P, ¬R ⊢ ¬Q
-- ----------------------------------------------------

import tactic

variables (P Q R : Prop)

-- 1ª demostración
example
  (h1 : P → (Q → R))
  (h2 : P)
  (h3 : ¬R)
  : ¬Q :=
have h4 : Q → R,
  from h1 h2,
show ¬Q,
  from mt h4 h3

-- 2ª demostración
example
  (h1 : P → (Q → R))
  (h2 : P)
  (h3 : ¬R)
  : ¬Q :=
have h4 : Q → R := h1 h2,
show ¬Q,
  from mt h4 h3

-- 3ª demostración
example
  (h1 : P → (Q → R))
  (h2 : P)
  (h3 : ¬R)
  : ¬Q :=
show ¬Q,
  from mt (h1 h2) h3

-- 4ª demostración
example
  (h1 : P → (Q → R))
  (h2 : P)
  (h3 : ¬R)
  : ¬Q :=
-- by library_search
mt (h1 h2) h3

-- 5ª demostración
example
  (h1 : P → (Q → R))
  (h2 : P)
  (h3 : ¬R)
  : ¬Q :=
begin
  intro h4,
  apply h3,
  apply (h1 h2),
  exact h4,
end

-- 6ª demostración
example
  (h1 : P → (Q → R))
  (h2 : P)
  (h3 : ¬R)
  : ¬Q :=
begin
  intro h4,
  apply h3,
  exact (h1 h2) h4,
end

-- 7ª demostración
example
  (h1 : P → (Q → R))
  (h2 : P)
  (h3 : ¬R)
  : ¬Q :=
begin
  intro h4,
  exact h3 ((h1 h2) h4),
end

-- 8ª demostración
example
  (h1 : P → (Q → R))
  (h2 : P)
  (h3 : ¬R)
  : ¬Q :=
λ h4, h3 ((h1 h2) h4)

-- 9ª demostración
example
  (h1 : P → (Q → R))
  (h2 : P)
  (h3 : ¬R)
  : ¬Q :=
-- by hint
by finish
