-- La identidad es biyectiva
-- =========================

import tactic

open function

variables {X Y Z : Type}

-- ----------------------------------------------------
-- Ej. 1. Demostrar que la identidad es inyectiva.
-- ----------------------------------------------------

-- 1ª demostración
example : injective (@id X) :=
begin
  intros x₁ x₂ h,
  exact h,
end

-- 2ª demostración
example : injective (@id X) :=
λ x₁ x₂ h, h

-- 3ª demostración
example : injective (@id X) :=
λ x₁ x₂, id

-- 4ª demostración
example : injective (@id X) :=
assume x₁ x₂,
assume h : id x₁ = id x₂,
show x₁ = x₂, from h

-- 5ª demostración
example : injective (@id X) :=
-- by library_search
injective_id

-- 6ª demostración
example : injective (@id X) :=
-- by hint
by tauto

-- 7ª demostración
example : injective (@id X) :=
-- by hint
by finish

-- ----------------------------------------------------
-- Ej. 2. Demostrar que la identidad es suprayectiva.
-- ----------------------------------------------------

-- 1ª demostración
example : surjective (@id X) :=
begin
  intro x,
  use x,
  exact rfl,
end

-- 2ª demostración
example : surjective (@id X) :=
begin
  intro x,
  exact ⟨x, rfl⟩,
end

-- 3ª demostración
example : surjective (@id X) :=
λ x, ⟨x, rfl⟩

-- 4ª demostración
example : surjective (@id X) :=
assume y,
show ∃ x, id x = y, from exists.intro y rfl

-- 5ª demostración
example : surjective (@id X) :=
-- by library_search
surjective_id

-- 6ª demostración
example : surjective (@id X) :=
-- by hint
by tauto

-- ----------------------------------------------------
-- Ej. 3. Demostrar que la identidad es biyectiva.
-- ----------------------------------------------------

-- 1ª demostración
example : bijective (@id X) :=
and.intro injective_id surjective_id

-- 2ª demostración
example : bijective (@id X) :=
⟨injective_id, surjective_id⟩

-- 3ª demostración
example : bijective (@id X) :=
-- by library_search
bijective_id

