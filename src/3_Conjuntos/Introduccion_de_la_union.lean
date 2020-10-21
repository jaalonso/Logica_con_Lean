-- Introducción de la unión
-- ========================

-- ----------------------------------------------------
-- Ej. 1. Demostrar
--    A ⊆ A ∪ B
-- ----------------------------------------------------

import data.set

variable  {U : Type}
variables A B : set U
variable  x : U

open set

-- #reduce x ∈ A ∪ B

-- 1ª demostración
example : A ⊆ A ∪ B :=
begin
  intros x h,
  simp,
  left,
  exact h,
end

-- 2ª demostración
example : A ⊆ A ∪ B :=
begin
  intros x h,
  left,
  exact h,
end

-- 3ª demostración
example : A ⊆ A ∪ B :=
assume x,
assume h : x ∈ A,
show x ∈ A ∪ B, from or.inl h

-- 4ª demostración
example : A ⊆ A ∪ B :=
assume x,
assume h : x ∈ A,
or.inl h

-- 5ª demostración
example : A ⊆ A ∪ B :=
assume x,
λ h : x ∈ A, or.inl h

-- 6ª demostración
example : A ⊆ A ∪ B :=
assume x, or.inl 

-- 7ª demostración
example : A ⊆ A ∪ B :=
λ x, or.inl 

-- 8ª demostración
example : A ⊆ A ∪ B :=
-- by library_search
subset_union_left A B

-- 9ª demostración
example : A ⊆ A ∪ B :=
λ x, mem_union_left B

-- 10ª demostración
example : A ⊆ A ∪ B :=
-- by hint
by finish

-- 11ª demostración
example : A ⊆ A ∪ B :=
by simp

