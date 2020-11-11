-- La imagen de la unión es la unión de las imágenes
-- =================================================

import data.set
open set function

variables {X Y : Type}
variable  (f : X → Y)
variables (A₁ A₂ : set X)

-- #reduce image f A₁
-- #reduce f '' A₁

-- 1ª demostración
example :
  f '' (A₁ ∪ A₂) = f '' A₁ ∪ f '' A₂ :=
begin
  ext y,
  split,
  { intro h,
    cases h with x hx,
    cases hx with xA₁A₂ fxy,
    cases xA₁A₂ with xA₁ xA₂,
    { left,
      use x,
      exact ⟨xA₁, fxy⟩, },
    { right,
      use x,
      exact ⟨xA₂, fxy⟩, }},
  { intro h,
    cases h with yifA₁ yifA₂,
    { cases yifA₁ with  x h1,
      cases h1 with xA₁ fxy,
      use x,
      split,
      { left,
        exact xA₁, },
      { exact fxy, }},
    { cases yifA₂ with x h1,
      cases h1 with xA₂ fxy,
      use x,
      split,
      { right,
        exact xA₂, },
      { exact fxy, }}},
end

-- 2ª demostración
example :
  f '' (A₁ ∪ A₂) = f '' A₁ ∪ f '' A₂ :=
begin
  ext y,
  split,
  { rintro ⟨x, (xA₁ | xA₂), fxy⟩,
    { exact or.inl ⟨x, xA₁, fxy⟩, },
    { exact or.inr ⟨x, xA₂, fxy⟩, }},
  { rintro (⟨x, xA₁, fxy⟩ | ⟨x, xA₂, fxy⟩),
    { exact ⟨x, or.inl xA₁, fxy⟩, },
    { exact ⟨x, or.inr xA₂, fxy⟩, }},
end

-- 3ª demostración
example :
  f '' (A₁ ∪ A₂) = f '' A₁ ∪ f '' A₂ :=
ext (assume y, iff.intro
  ( assume h : y ∈ f '' (A₁ ∪ A₂),
    exists.elim h
      ( assume x h1,
        have xA₁A₂ : x ∈ A₁ ∪ A₂, from h1.left,
        have fxy : f x = y, from h1.right,
        or.elim xA₁A₂
          ( assume xA₁, or.inl ⟨x, xA₁, fxy⟩)
          ( assume xA₂, or.inr ⟨x, xA₂, fxy⟩)))
  ( assume h : y ∈ f '' A₁ ∪ f '' A₂,
    or.elim h
      ( assume yifA₁ : y ∈ f '' A₁,
        exists.elim yifA₁
          ( assume x h1,
            have xA₁ : x ∈ A₁, from h1.left,
            have fxy : f x = y, from h1.right,
            ⟨x, or.inl xA₁, fxy⟩))
      ( assume yifA₂ : y ∈ f '' A₂,
        exists.elim yifA₂
          ( assume x h1,
            have xA₂ : x ∈ A₂, from h1.left,
            have fxy : f x = y, from h1.right,
            ⟨x, (or.inr xA₂), fxy⟩))))

-- 4ª demostración
example :
  f '' (A₁ ∪ A₂) = f '' A₁ ∪ f '' A₂ :=
-- by library_search
image_union f A₁ A₂

-- 5ª demostración
example :
  f '' (A₁ ∪ A₂) = f '' A₁ ∪ f '' A₂ :=
by finish [ext_iff, iff_def]
