-- Prueba de la regla de reducción al absurdo
-- ==========================================

import tactic

variable (P : Prop)

-- ----------------------------------------------------
-- Ej. 1 (p. 22) Demostrar que
--    ¬P → false ⊢ P
-- ----------------------------------------------------

-- 1ª demostración
example
  (h1 : ¬P → false)
  : P :=
have h2 : ¬¬P, from
  assume h3 : ¬P,
  show false, from h1 h3,
show P, from not_not.mp h2

-- 2ª demostración
example
  (h1 : ¬P → false)
  : P :=
begin
  apply not_not.mp,
  intro h2,
  exact h1 h2,
end

-- 3ª demostración
example
  (h1 : ¬P → false)
  : P :=
begin
  apply not_not.mp,
  exact λ h2, h1 h2,
end

-- 4ª demostración
example
  (h1 : ¬P → false)
  : P :=
not_not.mp (λ h2, h1 h2)

-- #print axioms not_not

-- 5ª demostración
example
  (h1 : ¬P → false)
  : P :=
-- by library_search
by_contra h1

-- #print axioms by_contra

-- 6ª demostración
lemma RAA
  (h1 : ¬P → false)
  : P :=
-- by hint
by finish

-- #print axioms RAA
