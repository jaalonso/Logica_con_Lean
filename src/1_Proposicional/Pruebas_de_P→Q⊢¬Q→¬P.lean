-- Pruebas de P → Q ⊢ ¬Q → ¬P
-- ==========================

-- Ej. 1. Demostrar
--    P → Q ⊢ ¬Q → ¬P

import tactic

variables (P Q : Prop)

-- 1ª demostración
example
  (h1 : P → Q)
  : ¬Q → ¬P :=
assume h2 : ¬Q,
show ¬P,
  from mt h1 h2

example
  (h1 : P → Q)
  : ¬Q → ¬P :=
assume h2 : ¬Q, mt h1 h2

example
  (h1 : P → Q)
  : ¬Q → ¬P :=
λ h2, mt h1 h2

example
  (h1 : P → Q)
  : ¬Q → ¬P :=
mt h1

example
  (h1 : P → Q)
  : ¬Q → ¬P :=
begin
  intro h2,
  exact mt h1 h2,
end

example
  (h1 : P → Q)
  : ¬Q → ¬P :=
begin
  intro h2,
  intro h3,
  apply h2,
  apply h1,
  exact h3,
end

example
  (h1 : P → Q)
  : ¬Q → ¬P :=
begin
  intro h2,
  intro h3,
  apply h2,
  exact h1 h3,
end

example
  (h1 : P → Q)
  : ¬Q → ¬P :=
begin
  intro h2,
  intro h3,
  exact h2 (h1 h3),
end

example
  (h1 : P → Q)
  : ¬Q → ¬P :=
begin
  intros h2 h3,
  exact h2 (h1 h3),
end

example
  (h1 : P → Q)
  : ¬Q → ¬P :=
λ h2 h3, h2 (h1 h3)

example
  (h1 : P → Q)
  : ¬Q → ¬P :=
by tauto

example
  (h1 : P → Q)
  : ¬Q → ¬P :=
by finish
