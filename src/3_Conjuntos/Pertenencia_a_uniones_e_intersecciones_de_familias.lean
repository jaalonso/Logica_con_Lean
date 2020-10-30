-- Pertenencia a uniones e intersecciones de familias
-- ==================================================

import data.set

open set

variables {I U : Type}
variables {A : I → set U}
variable  {x : U}

-- ----------------------------------------------------
-- Ej. 1. Demostrar que
--    (x ∈ ⋃ i, A i) ↔ (∃ i, x ∈ A i) 
-- ----------------------------------------------------

-- 1ª demostración
example :
  (x ∈ ⋃ i, A i) ↔ (∃ i, x ∈ A i) :=
-- by library_search
mem_Union

-- 2ª demostración
example :
  (x ∈ ⋃ i, A i) ↔ (∃ i, x ∈ A i) :=
by simp 

-- ----------------------------------------------------
-- Ej. 2. Demostrar que
--    (x ∈ ⋂ i, A i) ↔ (∀ i, x ∈ A i)
-- ----------------------------------------------------

-- 1ª demostración
example :
  (x ∈ ⋂ i, A i) ↔ (∀ i, x ∈ A i) :=
-- by library_search
mem_Inter

-- 2ª demostración
example :
  (x ∈ ⋂ i, A i) ↔ (∀ i, x ∈ A i) :=
by simp

