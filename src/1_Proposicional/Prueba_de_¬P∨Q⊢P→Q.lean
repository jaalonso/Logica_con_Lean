-- Prueba de ¬P ∨ Q ⊢ P → Q
-- ========================

-- ----------------------------------------------------
-- Ej. 1. (p. 15) Demostrar
--    ¬P ∨ Q ⊢ P → Q
-- ----------------------------------------------------

import tactic

variables (P Q : Prop)

-- 1ª demostración
example
  (h1 : ¬P ∨ Q)
  : P → Q :=
assume h2 : P,
or.elim h1
  ( assume h3 : ¬P,
    have h4 : false,
      from h3 h2,
    show Q,
      from false.elim h4)
  ( assume h5 : Q,
    show Q, from h5)

-- 2ª demostración
example
  (h1 : ¬P ∨ Q)
  : P → Q :=
assume h2 : P,
or.elim h1
  ( assume h3 : ¬P,
    have h4 : false,
      from h3 h2,
    show Q,
      from false.elim h4)
  ( assume h5 : Q, h5)

-- 3ª demostración
example
  (h1 : ¬P ∨ Q)
  : P → Q :=
assume h2 : P,
or.elim h1
  ( assume h3 : ¬P,
    have h4 : false,
      from h3 h2,
    show Q,
      from false.elim h4)
  ( λ h5, h5)

-- 4ª demostración
example
  (h1 : ¬P ∨ Q)
  : P → Q :=
assume h2 : P,
or.elim h1
  ( assume h3 : ¬P,
    have h4 : false,
      from h3 h2,
    show Q,
      from false.elim h4)
  id

-- 5ª demostración
example
  (h1 : ¬P ∨ Q)
  : P → Q :=
assume h2 : P,
or.elim h1
  ( assume h3 : ¬P,
    show Q,
      from false.elim (h3 h2))
  id

-- 6ª demostración
example
  (h1 : ¬P ∨ Q)
  : P → Q :=
assume h2 : P,
or.elim h1
  ( assume h3 : ¬P, false.elim (h3 h2))
  id

-- 7ª demostración
example
  (h1 : ¬P ∨ Q)
  : P → Q :=
assume h2 : P,
or.elim h1
  ( λ h3, false.elim (h3 h2))
  id

-- 8ª demostración
example
  (h1 : ¬P ∨ Q)
  : P → Q :=
λ h2, or.elim h1 (λ h3, false.elim (h3 h2)) id

example
  (h1 : ¬P ∨ Q)
  : P → Q :=
λ h2, h1.elim (λ h3, false.elim (h3 h2)) id

example
  (h1 : ¬P ∨ Q)
  : P → Q :=
λ h2, h1.elim (λ h3, (h3 h2).elim) id

-- 9ª demostración
example
  (h1 : ¬P ∨ Q)
  : P → Q :=
imp_iff_not_or.mpr h1

-- 10ª demostración
example
  (h1 : ¬P ∨ Q)
  : P → Q :=
begin
  intro h2,
  cases h1 with h3 h4,
  { apply false.rec,
    exact h3 h2, },
  { exact h4, },
end

-- 11ª demostración
example
  (h1 : ¬P ∨ Q)
  : P → Q :=
begin
  intro h2,
  cases h1 with h3 h4,
  { exact false.elim (h3 h2), },
  { exact h4, },
end

-- 12ª demostración
example
  (h1 : ¬P ∨ Q)
  : P → Q :=
begin
  intro h2,
  cases h1 with h3 h4,
  { exfalso,
    exact h3 h2, },
  { exact h4, },
end

-- 13ª demostración
example
  (h1 : ¬P ∨ Q)
  : P → Q :=
by tauto

-- 14ª demostración
example
  (h1 : ¬P ∨ Q)
  : P → Q :=
by finish
