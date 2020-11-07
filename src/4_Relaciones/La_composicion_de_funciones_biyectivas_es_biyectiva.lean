-- La composición de funciones biyectivas es biyectiva
-- ===================================================

-- ----------------------------------------------------
-- Ej. 1. Demostrar que la composición de dos funciones
-- biyectivas es una función biyectiva.
-- ----------------------------------------------------

import tactic

open function

variables {X Y Z : Type}
variable  {f : X → Y}
variable  {g : Y → Z} 

-- 1ª demostración
example 
  (hf : bijective f) 
  (hg : bijective g) 
  : bijective (g ∘ f) :=
begin
  split,
  { apply injective.comp, 
    { exact hg.left, },
    { exact hf.left, }},
  { apply surjective.comp, 
    { exact hg.right, },
    { exact hf.right, }},
end

-- 2ª demostración
example 
  (hf : bijective f) 
  (hg : bijective g) 
  : bijective (g ∘ f) :=
begin
  split,
  { exact injective.comp hg.1 hf.1, },
  { exact surjective.comp hg.2 hf.2, },
end

-- 3ª demostración
example 
  (hf : bijective f) 
  (hg : bijective g) 
  : bijective (g ∘ f) :=
⟨injective.comp  hg.1 hf.1,
 surjective.comp hg.2 hf.2⟩

-- 4ª demostración
example 
  (hf : bijective f) 
  (hg : bijective g) 
  : bijective (g ∘ f) :=
have giny : injective g, from hg.left,
have gsupr : surjective g, from hg.right,
have finy : injective f, from hf.left,
have fsupr : surjective f, from hf.right,
show bijective (g ∘ f),
  from and.intro (injective.comp giny finy)
                 (surjective.comp gsupr fsupr)

-- 5ª demostración
example 
  (hf : bijective f) 
  (hg : bijective g) 
  : bijective (g ∘ f) :=
-- by library_search
bijective.comp hg hf

-- 6ª demostración
example :
  bijective f → bijective g → bijective (g ∘ f) :=
begin
  rintros ⟨f_iny,f_supr⟩ ⟨g_iny,g_supr⟩,
  exact ⟨injective.comp  g_iny f_iny, 
         surjective.comp g_supr f_supr⟩,
end

-- 7ª demostración
example :
  bijective f → bijective g → bijective (g ∘ f) :=
begin
  rintros ⟨f_iny,f_supr⟩ ⟨g_iny,g_supr⟩,
  exact ⟨g_iny.comp f_iny, 
         g_supr.comp f_supr⟩,
end

-- 8ª demostración
example :
  bijective f → bijective g → bijective (g ∘ f) 
| ⟨f_iny,f_supr⟩ ⟨g_iny,g_supr⟩ := 
  ⟨g_iny.comp f_iny, g_supr.comp f_supr⟩

-- 9ª demostración
example :
  bijective f → bijective g → bijective (g ∘ f) :=
λ ⟨f_iny,f_supr⟩ ⟨g_iny,g_supr⟩,
  ⟨g_iny.comp f_iny, g_supr.comp f_supr⟩

