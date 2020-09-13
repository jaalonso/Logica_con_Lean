-- Reglas de la negación
-- =====================

import tactic

variable (P : Prop)

-- Eliminación del falso
-- ---------------------

-- Ej. 1. Demostrar que
--    ⊥ ⊢ P

-- 1ª demostración
example 
  (h : false)
  : P :=
false.elim h

-- 2ª demostración
example 
  (h : false)
  : P :=
false.rec P h

-- 3ª demostración
example 
  (h : false)
  : P :=
by tauto

-- 4ª demostración
example 
  (h : false)
  : P :=
by cases h

-- 5ª demostración
example 
  (h : false)
  : P :=
by finish

-- 6ª demostración
example 
  (h : false)
  : P :=
by solve_by_elim

-- Definición de la negación
-- -------------------------

-- ¬P ≡ (P → false)  

-- Eliminación de la negación
-- --------------------------

-- Ej. 2. Demostrar que
--    P, ¬P ⊢ ⊥

-- 1ª demostración
example
  (h1: P)
  (h2: ¬P)
  : false :=
not.elim h2 h1

-- 2ª demostración
example
  (h1: P)
  (h2: ¬P)
  : false :=
h2 h1

-- Introducción de la negación
-- ---------------------------

-- Ej. 3. Demostrar 
--    ¬(P ∧ ¬P)

-- 1ª demostración
example : ¬(P ∧ ¬P) :=
not.intro 
  ( assume h : P ∧ ¬P,
    have h1 : P  := h.1,
    have h2 : ¬P := h.2,
    show false, from h2 h1 )
  
-- 2ª demostración
example : ¬(P ∧ ¬P) :=
not.intro 
  ( assume h : P ∧ ¬P,
    show false, from h.2 h.1 )
  
-- 3ª demostración
example : ¬(P ∧ ¬P) :=
not.intro 
  ( assume h : P ∧ ¬P, h.2 h.1 )
  
-- 4ª demostración
example : ¬(P ∧ ¬P) :=
not.intro (λ h, h.2 h.1)
  
-- 5ª demostración
example : ¬(P ∧ ¬P) :=
begin
  intro h,
  cases h with h1 h2,
  apply h2,
  exact h1,
end  

-- 6ª demostración
example : ¬(P ∧ ¬P) :=
begin
  rintro ⟨h1, h2⟩,
  exact h2 h1,
end  

-- 7ª demostración
example : ¬(P ∧ ¬P) :=
λ ⟨h1, h2⟩, h2 h1

-- 8ª demostración
example : ¬(P ∧ ¬P) :=
(and_not_self P).mp

-- 9ª demostración
example : ¬(P ∧ ¬P) :=
by tauto

-- 10ª demostración
example : ¬(P ∧ ¬P) :=
by finish

-- 11ª demostración
example : ¬(P ∧ ¬P) :=
by simp 
