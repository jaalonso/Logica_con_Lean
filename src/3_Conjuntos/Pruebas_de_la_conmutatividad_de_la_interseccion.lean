-- Pruebas de la conmutatividad de la intersección
-- ===============================================

-- ----------------------------------------------------
-- Ej. 1. Demostrar
--    A ∩ B ⊆ B ∩ A
-- ----------------------------------------------------

import data.set

variable  {U : Type}
variables A B : set U
variable  x : U

open set

-- 1ª demostración
example : A ∩ B ⊆ B ∩ A :=
begin
  intros x h,
  simp at *,
  split,
  { exact h.right, },
  { exact h.left,  },
end

-- 2ª demostración
example : A ∩ B ⊆ B ∩ A :=
begin
  intros x h,
  split,
  { exact h.right, },
  { exact h.left,  },
end

-- 3ª demostración
example : A ∩ B ⊆ B ∩ A :=
begin
  rintros x ⟨h1, h2⟩,
  split,
  { exact h2, },
  { exact h1, },
end

-- 4ª demostración
example : A ∩ B ⊆ B ∩ A :=
begin
  rintros x ⟨h1, h2⟩,
  exact ⟨h2, h1⟩,
end

-- 5ª demostración
example : A ∩ B ⊆ B ∩ A :=
assume x,
assume h : x ∈ A ∩ B,
have h1 : x ∈ A, from and.left h,
have h2 : x ∈ B, from and.right h,
show x ∈ B ∩ A,  from and.intro h2 h1

-- 6ª demostración
example : A ∩ B ⊆ B ∩ A :=
assume x,
assume h : x ∈ A ∩ B,
have h1 : x ∈ A ∧ x ∈ B, from h,
have h2 : x ∈ B ∧ x ∈ A, from and.comm.mp h1,
show x ∈ B ∩ A,          from h2 

-- 7ª demostración
example : A ∩ B ⊆ B ∩ A :=
assume x,
assume h : x ∈ A ∩ B,
show x ∈ B ∩ A, from and.comm.mp h

-- 8ª demostración
example : A ∩ B ⊆ B ∩ A :=
assume x,
assume h : x ∈ A ∩ B,
and.comm.mp h

-- 9ª demostración
example : A ∩ B ⊆ B ∩ A :=
assume x,
λ h, and.comm.mp h

-- 10ª demostración
example : A ∩ B ⊆ B ∩ A :=
assume x,
and.comm.mp 

-- 10ª demostración
example : A ∩ B ⊆ B ∩ A :=
λ _, and.comm.mp 

-- 11ª demostración
example : A ∩ B ⊆ B ∩ A :=
-- by hint
by finish

-- 12ª demostración
lemma aux : A ∩ B ⊆ B ∩ A :=
by simp

-- ----------------------------------------------------
-- Ej. 2. Demostrar
--    A ∩ B = B ∩ A
-- ----------------------------------------------------

-- 1ª demostración
example : A ∩ B = B ∩ A :=
begin
  apply eq_of_subset_of_subset,
  { exact aux A B, },
  { exact aux B A, },
end

-- 2ª demostración
example : A ∩ B = B ∩ A :=
eq_of_subset_of_subset (aux A B) (aux B A)

-- 3ª demostración
example : A ∩ B = B ∩ A :=
-- by library_search
inter_comm A B

-- 4ª demostración
example : A ∩ B = B ∩ A :=
-- by hint
by finish
