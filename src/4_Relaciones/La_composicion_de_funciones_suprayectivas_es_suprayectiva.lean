-- La composición de funciones suprayectivas es suprayectiva
-- =========================================================

-- ----------------------------------------------------
-- Ej. 1. Demostrar que la composición de dos funciones
-- suprayectivas es una función suprayectiva.
-- ----------------------------------------------------

import tactic

open function

variables {X Y Z : Type}
variable  {f : X → Y}
variable  {g : Y → Z} 

-- 1ª demostración
example 
  (hf : surjective f) 
  (hg : surjective g) 
  : surjective (g ∘ f) :=
begin
  intro z,
  cases hg z with y hy,
  cases hf y with x hx,
  use x,
  simp,
  rw hx,
  exact hy,
end

-- 2ª demostración
example 
  (hf : surjective f) 
  (hg : surjective g) 
  : surjective (g ∘ f) :=
begin
  intro z,
  cases hg z with y hy,
  cases hf y with x hx,
  use x,
  calc (g ∘ f) x = g (f x) : by rw comp_app
             ... = g y     : congr_arg g hx
             ... = z       : hy,
end

-- 3ª demostración
example 
  (hf : surjective f) 
  (hg : surjective g) 
  : surjective (g ∘ f) :=
assume z,
exists.elim (hg z) 
  ( assume y (hy : g y = z),
    exists.elim (hf y) 
    ( assume x (hx : f x = y),
      have g (f x) = z, from eq.subst (eq.symm hx) hy,
      show ∃ x, g (f x) = z, from exists.intro x this))

-- 4ª demostración
example 
  (hf : surjective f) 
  (hg : surjective g) 
  : surjective (g ∘ f) :=
-- by library_search
surjective.comp hg hf

-- 5ª demostración
example 
  (hf : surjective f) 
  (hg : surjective g) 
  : surjective (g ∘ f) :=
λ z, exists.elim (hg z) 
  (λ y hy, exists.elim (hf y) 
     (λ x hx, exists.intro x 
        (show g (f x) = z, 
           from (eq.trans (congr_arg g hx) hy))))


