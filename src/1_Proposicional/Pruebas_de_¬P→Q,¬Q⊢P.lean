-- Pruebas de ¬P → Q, ¬Q ⊢ P
-- =========================

-- ----------------------------------------------------
-- Ej. 1. (p. 7) Demostrar
--    ¬P → Q, ¬Q ⊢ P
-- ----------------------------------------------------

import tactic

variables (P Q : Prop)

open_locale classical

-- 1ª demostración
example
  (h1 : ¬P → Q)
  (h2 : ¬Q)
  : P :=
have h3 : ¬¬P, from mt h1 h2,
show P,        from not_not.mp h3

-- 2ª demostración
example
  (h1 : ¬P → Q)
  (h2 : ¬Q)
  : P :=
not_not.mp (mt h1 h2)

-- 3ª demostración
example
  (h1 : ¬P → Q)
  (h2 : ¬Q)
  : P :=
begin
  by_contra h3,
  apply h2,
  exact h1 h3,
end

-- 4ª demostración
example
  (h1 : ¬P → Q)
  (h2 : ¬Q)
  : P :=
begin
  by_contra h3,
  exact h2 (h1 h3),
end

-- 5ª demostración
example
  (h1 : ¬P → Q)
  (h2 : ¬Q)
  : P :=
by_contra (λ h3, h2 (h1 h3))

-- 6ª demostración
example
  (h1 : ¬P → Q)
  (h2 : ¬Q)
  : P :=
by_contra (λ h3, (h2 ∘ h1) h3)

-- 7ª demostración
example
  (h1 : ¬P → Q)
  (h2 : ¬Q)
  : P :=
by_contra (h2 ∘ h1)

-- 8ª demostración
example
  (h1 : ¬P → Q)
  (h2 : ¬Q)
  : P :=
-- by library_search
not_not.mp (mt h1 h2)

-- 9ª demostración
example
  (h1 : ¬P → Q)
  (h2 : ¬Q)
  : P :=
-- by hint
by tauto

-- 10ª demostración
lemma aux
  (h1 : ¬P → Q)
  (h2 : ¬Q)
  : P :=
-- by hint
by finish

#print axioms aux
