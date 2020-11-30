-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    p ∧ q ⊢ ¬(¬p ∨ ¬q)
-- ----------------------------------------------------

import tactic
variables (p q : Prop)

-- 1ª demostración
example
  (H : p ∧ q)
  : ¬(¬p ∨ ¬q) :=
begin
  intro H1,
  cases H1 with H2 H3,
  { apply H2,
    exact H.left, },
  { apply H3,
    exact H.right, },
end

-- 2ª demostración
example
  (H : p ∧ q)
  : ¬(¬p ∨ ¬q) :=
begin
  intro H1,
  cases H1 with H2 H3,
  { exact H2 H.left, },
  { exact H3 H.right, },
end

-- 3ª demostración
example
  (H : p ∧ q)
  : ¬(¬p ∨ ¬q) :=
λ H1, or.elim H1 (λ H2, H2 H.1) (λ H3, H3 H.2)

-- 4ª demostración
example
  (H : p ∧ q)
  : ¬(¬p ∨ ¬q) :=
begin
  rintro (H2 | H3),
  { exact H2 H.left, },
  { exact H3 H.right, },
end

-- 5ª demostración
example
  (H : p ∧ q)
  : ¬(¬p ∨ ¬q) :=
-- by library_search
and_iff_not_or_not.mp H

-- 6ª demostración
example
  (H : p ∧ q)
  : ¬(¬p ∨ ¬q) :=
-- by hint
by tauto

-- 7ª demostración
example
  (H : p ∧ q)
  : ¬(¬p ∨ ¬q) :=
by finish
