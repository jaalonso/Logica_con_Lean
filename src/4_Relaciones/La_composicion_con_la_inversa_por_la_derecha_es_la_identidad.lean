-- La composición con la inversa por la derecha es la identidad
-- ==============================================================

import tactic

open function

variables {X Y Z : Type}
variable  {f : X → Y}
variable  {g : Y → X}

-- #reduce right_inverse g f

-- 1ª demostración
example
  (h : right_inverse g f)
  : f ∘ g = id :=
begin
  apply funext,
  intro x,
  rw comp_app,
  rw id.def,
  rw h,
end

-- 2ª demostración
example
  (h : right_inverse g f)
  : f ∘ g = id :=
begin
  apply funext,
  intro x,
  calc (f ∘ g) x
           = f (g x) : by rw comp_app
       ... = x       : by rw h
       ... = id x    : by rw id.def,
end

-- 3ª demostración
example
  (h : right_inverse g f)
  : f ∘ g = id :=
begin
  funext,
  dsimp,
  rw h,
end

-- 4ª demostración
example
  (h : right_inverse g f)
  : f ∘ g = id :=
funext h

-- 5ª demostración
example
  (h : right_inverse g f)
  : f ∘ g = id :=
-- by library_search
right_inverse.id h
