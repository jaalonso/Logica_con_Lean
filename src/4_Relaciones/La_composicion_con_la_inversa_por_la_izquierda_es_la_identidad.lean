-- La composición con la inversa por la izquierda es la identidad
-- ==============================================================

import tactic

open function

variables {X Y Z : Type}
variable  {f : X → Y}
variable  {g : Y → X} 

-- #reduce left_inverse g f

-- 1ª demostración
example 
  (h : left_inverse g f)
  : g ∘ f = id :=
begin
  apply funext,
  intro x,
  rw comp_app,
  rw id.def,
  rw h,
end

-- 2ª demostración
example 
  (h : left_inverse g f)
  : g ∘ f = id :=
begin
  apply funext,
  intro x,
  calc (g ∘ f) x 
           = g (f x) : by rw comp_app
       ... = x       : by rw h
       ... = id x    : by rw id.def,
end

-- 3ª demostración
example 
  (h : left_inverse g f)
  : g ∘ f = id :=
begin
  funext,
  dsimp,
  rw h,
end

-- 4ª demostración
example 
  (h : left_inverse g f)
  : g ∘ f = id :=
funext h

-- 5ª demostración
example 
  (h : left_inverse g f)
  : g ∘ f = id :=
-- by library_search
left_inverse.id h

