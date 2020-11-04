-- La composición de funciones inyectivas es inyectiva
-- ===================================================

-- ----------------------------------------------------
-- Ej. 1. Demostrar que la composición de dos funciones
-- inyectivas es una función inyectiva.
-- ----------------------------------------------------

import tactic

open function

variables {X Y Z : Type}
variable  {f : X → Y}
variable  {g : Y → Z} 

-- 1ª demostración
example 
  (Hf : injective f) 
  (Hg : injective g) 
  : injective (g ∘ f) :=
begin
  intros x y h,
  apply Hf,
  apply Hg,
  exact h,
end

-- 2ª demostración
example 
  (Hf : injective f) 
  (Hg : injective g) 
  : injective (g ∘ f) :=
begin
  intros x y h,
  apply Hf,
  exact Hg h,
end

-- 3ª demostración
example 
  (Hf : injective f) 
  (Hg : injective g) 
  : injective (g ∘ f) :=
begin
  intros x y h,
  exact Hf (Hg h),
end

-- 4ª demostración
example 
  (Hf : injective f) 
  (Hg : injective g) 
  : injective (g ∘ f) :=
λ x y h, Hf (Hg h)

-- 5ª demostración
example 
  (Hf : injective f) 
  (Hg : injective g) 
  : injective (g ∘ f) :=
assume x y,
assume h1 : (g ∘ f) x = (g ∘ f) y,
have h2 : f x = f y, from Hg h1,
show x = y, from Hf h2

-- 6ª demostración
example 
  (Hf : injective f) 
  (Hg : injective g) 
  : injective (g ∘ f) :=
assume x y,
assume h1 : (g ∘ f) x = (g ∘ f) y,
show x = y, from Hf (Hg h1)

-- 7ª demostración
example 
  (Hf : injective f) 
  (Hg : injective g) 
  : injective (g ∘ f) :=
assume x y,
assume h1 : (g ∘ f) x = (g ∘ f) y,
Hf (Hg h1)

-- 8ª demostración
example 
  (Hf : injective f) 
  (Hg : injective g) 
  : injective (g ∘ f) :=
λ x y h1, Hf (Hg h1)

-- 9ª demostración
example 
  (Hg : injective g) 
  (Hf : injective f) 
  : injective (g ∘ f) :=
-- by library_search
injective.comp Hg Hf

-- 10ª demostración
example 
  (Hg : injective g) 
  (Hf : injective f) 
  : injective (g ∘ f) :=
-- by hint
by tauto
