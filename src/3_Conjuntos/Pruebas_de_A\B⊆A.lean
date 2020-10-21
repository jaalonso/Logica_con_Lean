-- Pruebas de A \ B ⊆ A
-- ====================

-- ----------------------------------------------------
-- Ej. 1. Demostrar
--    A \ B ⊆ A
-- ----------------------------------------------------

import data.set

variable  {U : Type}
variables A B : set U
variable  x : U

open set

-- #reduce x ∈ A \ B

-- 1ª demostración
example : A \ B ⊆ A :=
begin
  intros x h,
  simp at h,
  exact h.left,
end

-- 2ª demostración
example : A \ B ⊆ A :=
begin
  intros x h,
  exact h.left,
end

-- 3ª demostración
example : A \ B ⊆ A :=
assume x,
assume h : x ∈ A \ B,
show x ∈ A, from and.left h

-- 4ª demostración
example : A \ B ⊆ A :=
assume x,
assume h : x ∈ A \ B,
and.left h

-- 5ª demostración
example : A \ B ⊆ A :=
assume x,
λ h, and.left h

-- 6ª demostración
example : A \ B ⊆ A :=
λ x, λ h, and.left h

-- 7ª demostración
example : A \ B ⊆ A :=
λ x h, and.left h

-- 8ª demostración
example : A \ B ⊆ A :=
-- by library_search
diff_subset A B

-- 9ª demostración
example : A \ B ⊆ A :=
assume x,
assume h : x ∈ A \ B,
show x ∈ A, from mem_of_mem_diff h

-- 10ª demostración
example : A \ B ⊆ A :=
λ x h, mem_of_mem_diff h

