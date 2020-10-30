-- Monotonía del conjunto potencia: 𝒫 A ⊆ 𝒫 B ↔ A ⊆ B
-- ===================================================

import data.set
open set

variable  {U : Type}
variables {A B C : set U}

-- ----------------------------------------------------
-- Ej. 1. Demostrar
--    𝒫 A ⊆ 𝒫 B → A ⊆ B 
-- ----------------------------------------------------

-- 1ª demostración
example : 𝒫 A ⊆ 𝒫 B → A ⊆ B :=
begin
  intro h,
  apply subset_of_mem_powerset,
  apply h,
  apply mem_powerset,
  exact subset.rfl,
end

-- 2ª demostración
example : 𝒫 A ⊆ 𝒫 B → A ⊆ B :=
begin
  intro h,
  apply h,
  exact subset.rfl,
end

-- 3ª demostración
example : 𝒫 A ⊆ 𝒫 B → A ⊆ B :=
begin
  intro h,
  exact (h subset.rfl),
end

-- 4ª demostración
example : 𝒫 A ⊆ 𝒫 B → A ⊆ B :=
λ h, h subset.rfl

-- 5ª demostración
example : 𝒫 A ⊆ 𝒫 B → A ⊆ B :=
assume h1 : 𝒫 A ⊆ 𝒫 B,
have h2 : A ⊆ A, from subset.rfl,
have h3 : A ∈ 𝒫 A, from h2,
have h4 : A ∈ 𝒫 B, from h1 h3,
show A ⊆ B, from h4

-- 6ª demostración
example : 𝒫 A ⊆ 𝒫 B → A ⊆ B :=
assume h1 : 𝒫 A ⊆ 𝒫 B,
have h2 : A ⊆ A, from subset.rfl,
have h3 : A ∈ 𝒫 A, from h2,
h1 h3

-- 7ª demostración
example : 𝒫 A ⊆ 𝒫 B → A ⊆ B :=
assume h1 : 𝒫 A ⊆ 𝒫 B,
have h2 : A ⊆ A, from subset.rfl,
h1 h2

-- 8ª demostración
example : 𝒫 A ⊆ 𝒫 B → A ⊆ B :=
assume h1 : 𝒫 A ⊆ 𝒫 B,
h1 subset.rfl

-- 9ª demostración
lemma aux1 : 𝒫 A ⊆ 𝒫 B → A ⊆ B :=
λ h, h subset.rfl

-- 10ª demostración
example : 𝒫 A ⊆ 𝒫 B → A ⊆ B :=
powerset_mono.mp

-- ----------------------------------------------------
-- Ej. 2. Demostrar
--    A ⊆ B → 𝒫 A ⊆ 𝒫 B 
-- ----------------------------------------------------

-- 1ª demostración
example : A ⊆ B → 𝒫 A ⊆ 𝒫 B :=
begin
  intro h,
  intros C hCA,
  apply mem_powerset,
  apply subset.trans hCA h,
end

-- 2ª demostración
example : A ⊆ B → 𝒫 A ⊆ 𝒫 B :=
begin
  intros h C hCA,
  apply subset.trans hCA h,
end

-- 3ª demostración
lemma aux2 : A ⊆ B → 𝒫 A ⊆ 𝒫 B :=
λ h C hCA, subset.trans hCA h

-- 4ª demostración
example : A ⊆ B → 𝒫 A ⊆ 𝒫 B :=
powerset_mono.mpr

-- ----------------------------------------------------
-- Ej. 3. Demostrar
--    𝒫 A ⊆ 𝒫 B ↔ A ⊆ B
-- ----------------------------------------------------

-- 1ª demostración
example : 𝒫 A ⊆ 𝒫 B ↔ A ⊆ B :=
iff.intro aux1 aux2

-- 2ª demostración
example : 𝒫 A ⊆ 𝒫 B ↔ A ⊆ B :=
-- by library_search
powerset_mono

