-- Pruebas de la eliminación de la doble negación
-- ==============================================

-- Ej. 1. Demostrar
--     ¬¬P ⊢ P

import tactic

variable (P : Prop)

-- 1ª demostración
example
  (h1 : ¬¬P)
  : P :=
have h2 : P ∨ ¬P, from em P,
or.elim h2 
  id
  ( assume h3 : ¬P,
    have h4 : false, from h1 h3,
    show P, from false.elim h4)

-- 2ª demostración
example
  (h1 : ¬¬P)
  : P :=
have h2 : P ∨ ¬P, from em P,
or.elim h2 
  id
  ( assume h3 : ¬P,
    have h4 : false, from h1 h3,
    false.elim h4)

-- 3ª demostración
example
  (h1 : ¬¬P)
  : P :=
have h2 : P ∨ ¬P, from em P,
or.elim h2 
  id
  ( assume h3 : ¬P,
    false.elim (h1 h3))

-- 4ª demostración
example
  (h1 : ¬¬P)
  : P :=
have h2 : P ∨ ¬P, from em P,
or.elim h2 
  id
  (λ h3, false.elim (h1 h3))

-- 5ª demostración
example
  (h1 : ¬¬P)
  : P :=
or.elim (em P) id (λ h3, false.elim (h1 h3))

#print axioms em

-- 5ª demostración
example
  (h1 : ¬¬P)
  : P :=
not_not.mp h1

#print axioms not_not 

-- 6ª demostración
example
  (h1 : ¬¬P)
  : P :=
begin
  by_cases P, 
  { assumption, },
  { exfalso,
    exact h1 ‹¬P›, },
end

-- 7ª demostración
example
  (h1 : ¬¬P)
  : P :=
by finish


