-- Las funciones inyectivas tienen inversa por la izquierda
-- ========================================================

import tactic

open classical function

local attribute [instance] prop_decidable

variables {X Y : Type}

-- ----------------------------------------------------
-- Ej. 1. Definir la función
--    inversa :: (X → Y) → X → (Y → X)
-- tal que (inversa f d) es la función que a cada
-- y ∈ Y le asigna
-- + alguno de los elementos x tales que f(x) = y, si
--   existen dichos elementos y
-- + d, en caso contrario.
-- ----------------------------------------------------

noncomputable def inversa (f : X → Y) (d : X) : Y → X :=
λ y, if h : ∃ x, f x = y then some h else d

-- Notación:
variable (f : X → Y)
variable (d : X)
variable (y : Y)

-- ----------------------------------------------------
-- Ej. 2. Demostrar que si
--    ∃ x, f x = y
-- entonces,
--    f ((inversa f d) y) = y
-- ----------------------------------------------------

-- 1ª demostración
example
  (h : ∃ x, f x = y)
  : f ((inversa f d) y) = y :=
calc f ((inversa f d) y)
         = f (some h)  : congr rfl (dif_pos h)
     ... = y           : some_spec h

-- 2ª demostración
lemma inversa_cuando_existe
  (h : ∃ x, f x = y)
  : f ((inversa f d) y) = y :=
have h1 : (inversa f d) y = some h,
  from dif_pos h,
have h2 : f (some h) = y,
  from some_spec h,
show f (inversa f d y) = y,
  from eq.subst (eq.symm h1) h2

-- ----------------------------------------------------
-- Ej. 3. Demostrar que si f es inyectiva, entonces
-- (inversa f d) es inversa de f por la izquierda.
-- ----------------------------------------------------

-- 1ª demostración
example
  (h : injective f)
  : left_inverse (inversa f d) f :=
begin
  intro x,
  apply h,
  rw inversa_cuando_existe f d,
  use x,
end

-- 2ª demostración
lemma inversa_es_inversa_por_la_izquierda
  (h : injective f)
  : left_inverse (inversa f d) f :=
let g := (inversa f d) in
assume x,
have h1 : ∃ x', f x' = f x,
  from exists.intro x rfl,
have h2 : f (g (f x)) = f x,
  from inversa_cuando_existe f d (f x) h1,
show g (f x) = x,
  from h h2

-- ----------------------------------------------------
-- Ej. 4. Demostrar que si f es inyectiva, entonces
-- f tiene inversa por la izquierda.
-- ----------------------------------------------------

-- 1ª demostración
example
  (d : X)
  (h : injective f)
  : has_left_inverse f :=
begin
  unfold has_left_inverse,
  use (inversa f d),
  exact (inversa_es_inversa_por_la_izquierda f d h),
end

-- 2ª demostración
example
  (d : X)
  (h : injective f)
  : has_left_inverse f :=
have h1 : left_inverse (inversa f d) f,
  from inversa_es_inversa_por_la_izquierda f d h,
have h2 : ∃ g, left_inverse g f,
  from exists.intro (inversa f d) h1,
show has_left_inverse f,
  from h2

-- 3ª demostración
example
  (d : X)
  (h : injective f)
  : has_left_inverse f :=
have h1 : left_inverse (inversa f d) f,
  from inversa_es_inversa_por_la_izquierda f d h,
show has_left_inverse f,
  from exists.intro (inversa f d) h1
