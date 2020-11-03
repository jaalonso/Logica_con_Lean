-- Propiedades de la composición de funciones
-- ==========================================

import tactic

open function

variables {X Y Z W : Type}

-- ----------------------------------------------------
-- Ej. 1. Demostrar que 
--    id ∘ f = f
-- ----------------------------------------------------

-- 1ª demostración
example
  (f : X → Y) 
  : id ∘ f = f := 
begin
  ext,
  calc (id ∘ f) x = id (f x) : by rw comp_app
       ...        = f x      : by rw id.def,
end

-- 2ª demostración
example
  (f : X → Y) 
  : id ∘ f = f := 
begin
  ext,
  rw comp_app,
  rw id.def,
end

-- 3ª demostración
example
  (f : X → Y) 
  : id ∘ f = f := 
begin
  ext,
  rw [comp_app, id.def],
end

-- 4ª demostración
example
  (f : X → Y) 
  : id ∘ f = f := 
begin
  ext,
  calc (id ∘ f) x = id (f x) : rfl
       ...        = f x      : rfl,
end

-- 5ª demostración
example
  (f : X → Y) 
  : id ∘ f = f := 
rfl

-- 6ª demostración
example
  (f : X → Y) 
  : id ∘ f = f := 
-- by library_search
left_id f 

-- 7ª demostración
example
  (f : X → Y) 
  : id ∘ f = f := 
comp.left_id f

-- ----------------------------------------------------
-- Ej. 2. Demostrar que 
--    f ∘ id = f
-- ----------------------------------------------------

-- 1ª demostración
example 
  (f : X → Y) 
  : f ∘ id = f := 
begin
  ext,
  calc (f ∘ id) x = f (id x) : by rw comp_app
       ...        = f x      : by rw id.def,
end

-- 2ª demostración
example 
  (f : X → Y) 
  : f ∘ id = f := 
begin
  ext,
  rw comp_app,
  rw id.def,
end

-- 3ª demostración
example 
  (f : X → Y) 
  : f ∘ id = f := 
begin
  ext,
  rw [comp_app, id.def],
end

-- 4ª demostración
example 
  (f : X → Y) 
  : f ∘ id = f := 
begin
  ext,
  calc (f ∘ id) x = f (id x) : rfl
       ...        = f x      : rfl,
end

-- 5ª demostración
example 
  (f : X → Y) 
  : f ∘ id = f := 
rfl

-- 6ª demostración
example 
  (f : X → Y) 
  : f ∘ id = f := 
-- by library_search
right_id f

-- 7ª demostración
example 
  (f : X → Y) 
  : f ∘ id = f := 
comp.right_id f

-- ----------------------------------------------------
-- Ej. 3. Demostrar que 
--    (f ∘ g) ∘ h = f ∘ (g ∘ h) 
-- ----------------------------------------------------

-- 1ª demostración
example
  (f : Z → W) 
  (g : Y → Z) 
  (h : X → Y) 
  : (f ∘ g) ∘ h = f ∘ (g ∘ h) := 
begin
  ext,
  calc ((f ∘ g) ∘ h) x  
           = (f ∘ g) (h x)   : by rw comp_app
       ... = f (g (h x))     : by rw comp_app
       ... = f ((g ∘ h) x)   : by rw comp_app
       ... = (f ∘ (g ∘ h)) x : by rw comp_app
end

-- 2ª demostración
example
  (f : Z → W) 
  (g : Y → Z) 
  (h : X → Y) 
  : (f ∘ g) ∘ h = f ∘ (g ∘ h) := 
begin
  ext,
  rw comp_app,
end

-- 3ª demostración
example
  (f : Z → W) 
  (g : Y → Z) 
  (h : X → Y) 
  : (f ∘ g) ∘ h = f ∘ (g ∘ h) := 
begin
  ext,
  calc ((f ∘ g) ∘ h) x  
           = (f ∘ g) (h x)   : rfl
       ... = f (g (h x))     : rfl
       ... = f ((g ∘ h) x)   : rfl
       ... = (f ∘ (g ∘ h)) x : rfl
end

-- 4ª demostración
example
  (f : Z → W) 
  (g : Y → Z) 
  (h : X → Y) 
  : (f ∘ g) ∘ h = f ∘ (g ∘ h) := 
rfl

-- 5ª demostración
example
  (f : Z → W) 
  (g : Y → Z) 
  (h : X → Y) 
  : (f ∘ g) ∘ h = f ∘ (g ∘ h) := 
comp.assoc f g h


