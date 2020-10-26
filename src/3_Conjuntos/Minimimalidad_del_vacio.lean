-- Regla del conjunto vacío
-- ========================

-- ----------------------------------------------------
-- Ej. 1. Demostrar
--    ∅ ⊆ A
-- ----------------------------------------------------

import data.set

variable  U : Type
variables A : set U
variable  x : U

open set

-- #reduce (∅ : set U)
-- #reduce x ∈ (∅ : set U) 

-- 1ª demostración
example : ∅ ⊆ A :=
begin
  intros x h,
  simp at h,
  exfalso,
  exact h,
end

-- 2ª demostración
example : ∅ ⊆ A :=
begin
  intros x h,
  exfalso,
  exact h,
end

-- 3ª demostración
example : ∅ ⊆ A :=
assume x,
assume h : x ∈ (∅ : set U),
show x ∈ A, from false.elim h

-- 4ª demostración
example : ∅ ⊆ A :=
λ x, λ h, false.elim h

-- 5ª demostración
example : ∅ ⊆ A :=
λ _, false.elim 

-- 6ª demostración
example : ∅ ⊆ A :=
-- by library_search
empty_subset A

-- 7ª demostración
example : ∅ ⊆ A :=
assume x,
assume h : x ∈ (∅ : set U),
show x ∈ A, from absurd h (not_mem_empty x)

-- 8ª demostración
example : ∅ ⊆ A :=
λ x h, absurd h (not_mem_empty x)

-- 9ª demostración
example : ∅ ⊆ A :=
-- by hint
by tauto

-- 10ª demostración
example : ∅ ⊆ A :=
by finish

-- 11ª demostración
example : ∅ ⊆ A :=
by simp 

