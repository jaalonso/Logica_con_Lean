-- Pruebas de A \ B ⊆ Bᶜ
-- =====================

-- ----------------------------------------------------
-- Ej. 1. Demostrar
--    A \ B ⊆ Bᶜ
-- ----------------------------------------------------

import data.set

variable  {U : Type}
variables A B : set U
variable  x : U

open set

-- #reduce x ∈ Bᶜ

-- 1ª demostración
example : A \ B ⊆ Bᶜ :=
begin
  intros x h,
  simp at *,
  exact h.right,
end

-- 2ª demostración
example : A \ B ⊆ Bᶜ :=
begin
  intros x h,
  exact h.right,
end

-- 3ª demostración
example : A \ B ⊆ Bᶜ :=
assume x,
assume h1 : x ∈ A \ B,
have h2 : x ∉ B, from and.right h1,
show x ∈ Bᶜ,     from h2

-- 4ª demostración
example : A \ B ⊆ Bᶜ :=
assume x,
assume h1 : x ∈ A \ B,
have h2 : x ∉ B, from and.right h1,
show x ∈ Bᶜ,     from h2

-- 5ª demostración
example : A \ B ⊆ Bᶜ :=
assume x,
assume h1 : x ∈ A \ B,
show x ∈ Bᶜ, from and.right h1

-- 6ª demostración
example : A \ B ⊆ Bᶜ :=
λ x h, and.right h

-- 7ª demostración
example : A \ B ⊆ Bᶜ :=
λ x h, not_mem_of_mem_diff h

