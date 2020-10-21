-- Prueba de la reflexividad de la inclusión de conjuntos
-- ======================================================

-- ----------------------------------------------------
-- Ej. 1. Demostrar
--    A ⊆ A
-- ----------------------------------------------------

import data.set

variable  {U : Type}
variables A : set U
variable  x : U

-- 1ª demostración
example 
  : A ⊆ A :=
begin
  intros x h,
  exact h,
end

-- 2ª demostración
example 
  : A ⊆ A :=
assume x, 
assume h : x ∈ A,
show x ∈ A, from h

-- 3ª demostración
example 
  : A ⊆ A :=
assume x, 
assume h : x ∈ A,
h

-- 4ª demostración
example 
  : A ⊆ A :=
assume x, 
λ h : x ∈ A, h

-- 5ª demostración
example 
  : A ⊆ A :=
assume x, 
id

-- 6ª demostración
example 
  : A ⊆ A :=
λ x, id

-- 7ª demostración
example 
  : A ⊆ A :=
-- by library_search
set.subset.rfl

open set

-- 8ª demostración
example 
  : A ⊆ A :=
-- by library_search
subset.rfl

-- 9ª demostración
example 
  : A ⊆ A :=
-- by hint
by tauto

-- 10ª demostración
example 
  : A ⊆ A :=
by finish

-- 11ª demostración
example 
  : A ⊆ A :=
by refl 


