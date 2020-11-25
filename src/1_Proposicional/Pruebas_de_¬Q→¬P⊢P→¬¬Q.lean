-- Pruebas de ¬Q → ¬P ⊢ P → ¬¬Q
-- ============================

-- ----------------------------------------------------
-- Ej. 1. (p. 9) Demostrar
--    ¬Q → ¬P ⊢ P → ¬¬Q
-- ----------------------------------------------------

import tactic

variables (P Q : Prop)

-- 1ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
assume h2 : P,
have h3 : ¬¬P,
  from not_not_intro h2,
show ¬¬Q,
  from mt h1 h3

-- 2ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
assume h2 : P,
have h3 : ¬¬P := not_not_intro h2,
show ¬¬Q,
  from mt h1 h3

-- 3ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
assume h2 : P,
show ¬¬Q,
  from mt h1 (not_not_intro h2)

-- 4ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
assume h2 : P, mt h1 (not_not_intro h2)

-- 5ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
λ h2, mt h1 (not_not_intro h2)

-- 6ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
-- by library_search
imp_not_comm.mp h1

-- 7ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
begin
  intro h2,
  apply mt h1,
  apply not_not_intro,
  exact h2,
end

-- 8ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
begin
  intro h2,
  apply mt h1,
  exact not_not_intro h2,
end

-- 9ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
begin
  intro h2,
  exact mt h1 (not_not_intro h2),
end

-- 10ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
λ h2, mt h1 (not_not_intro h2)

-- 11ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
begin
  intro h2,
  intro h3,
  have h4 : ¬P := h1 h3,
  exact h4 h2,
end

-- 12ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
begin
  intros h2 h3,
  exact (h1 h3) h2,
end

-- 13ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
λ h2 h3, (h1 h3) h2

-- 14ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
-- by hint
by tauto

-- 15ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
by finish
