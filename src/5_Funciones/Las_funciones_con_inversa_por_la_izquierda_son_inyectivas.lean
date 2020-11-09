-- Las funciones con inversa por la izquierda son inyectivas
-- =========================================================

import tactic

open function

variables {X Y : Type}
variable  {f : X → Y}
variable  {g : Y → X}

-- ----------------------------------------------------
-- Ej. 1. Demostrar que si f tiene inversa por la
-- izquierda, entonces f es inyectiva.
-- ----------------------------------------------------

-- 1ª demostración
example
  (h : left_inverse g f)
  : injective f :=
begin
  intros x₁ x₂ h1,
  rw ←(h x₁),
  rw ←(h x₂),
  rw h1,
end

-- 2ª demostración
example
  (h : left_inverse g f)
  : injective f :=
begin
  intros x₁ x₂ h1,
  calc x₁ = g (f x₁) : (h x₁).symm
      ... = g (f x₂) : congr_arg g h1
      ... = x₂       : h x₂,
end

-- 3ª demostración
example
  (h : left_inverse g f)
  : injective f :=
begin
  intros x₁ x₂ h1,
  calc x₁ = g (f x₁) : by rw h
      ... = g (f x₂) : by rw h1
      ... = x₂       : by rw h
end

-- 4ª demostración
example
  (h : left_inverse g f)
  : injective f :=
assume x₁ x₂,
assume h1 : f x₁ = f x₂,
show x₁ = x₂, from
  calc x₁ = g (f x₁) : by rw h
      ... = g (f x₂) : by rw h1
      ... = x₂       : by rw h

-- 5ª demostración
example
  (h : left_inverse g f)
  : injective f :=
-- by library_search
left_inverse.injective h

-- 6ª demostración
example
  (h : left_inverse g f)
  : injective f :=
assume x₁ x₂,
assume h1 : f x₁ = f x₂,
show x₁ = x₂, from
  calc x₁ = g (f x₁) : (h x₁).symm
      ... = g (f x₂) : congr_arg g h1
      ... = x₂       : h x₂

-- 7ª demostración
example
  (h : left_inverse g f)
  : injective f :=
λ x₁ x₂ h1, (trans (h x₁).symm
                   (trans (congr_arg g h1)
                          (h x₂)))
