-- Pruebas de la antisimetría de la inclusión de conjuntos
-- =======================================================

-- ----------------------------------------------------
-- Ej. 1. Demostrar
--    A ⊆ B, B ⊆ A ⊢ A = B 
-- ----------------------------------------------------

import data.set

variable  U : Type
variables A B : set U

open set

-- 1ª demostración
example 
  (h1 : A ⊆ B)
  (h2 : B ⊆ A)
  : A = B :=
begin
  ext,
  split,
  { intro h,
    exact h1 h, },
  { intro h,
    exact h2 h, },
end

-- 2ª demostración
example 
  (h1 : A ⊆ B)
  (h2 : B ⊆ A)
  : A = B :=
ext 
( assume x, 
  iff.intro
  ( assume h : x ∈ A,
    show x ∈ B, from h1 h)
  ( assume h : x ∈ B,
    show x ∈ A, from h2 h))

-- 3ª demostración
example 
  (h1 : A ⊆ B)
  (h2 : B ⊆ A)
  : A = B :=
ext 
(λ x, 
 iff.intro
 (λ h, h1 h)
 (λ h, h2 h))

-- 4ª demostración
example 
  (h1 : A ⊆ B)
  (h2 : B ⊆ A)
  : A = B :=
eq_of_subset_of_subset
  ( assume x,
    assume h : x ∈ A,
    show x ∈ B, from h1 h)
  ( assume x,
    assume h : x ∈ B,
    show x ∈ A, from h2 h)

-- 5ª demostración
example 
  (h1 : A ⊆ B)
  (h2 : B ⊆ A)
  : A = B :=
eq_of_subset_of_subset h1 h2

-- 6ª demostración
example 
  (h1 : A ⊆ B)
  (h2 : B ⊆ A)
  : A = B :=
-- by library_search
subset.antisymm h1 h2



