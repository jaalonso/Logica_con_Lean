-- Las funciones con inversa por la derecha son suprayectivas
-- ==========================================================

import tactic

open function

variables {X Y : Type}
variable  {f : X → Y}
variable  {g : Y → X}

-- ----------------------------------------------------
-- Ej. 1. Demostrar que si f tiene inversa por la
-- derecha, entonces f es suprayectiva
-- ----------------------------------------------------

-- 1ª demostración
example
  (h : right_inverse g f)
  : surjective f :=
begin
  intro y,
  use g y,
  exact h y,
end

-- 2ª demostración
example
  (h : right_inverse g f)
  : surjective f :=
λ y, ⟨g y, h y⟩

-- 3ª demostración
example
  (h : right_inverse g f)
  : surjective f :=
assume y,
show ∃ x, f x = y,
  from exists.intro (g y) (h y)

-- 4ª demostración
example
  (h : right_inverse g f)
  : surjective f :=
-- by library_search
right_inverse.surjective h
