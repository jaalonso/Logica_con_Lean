-- Las partes simétricas de las reflexivas son reflexivas
-- ======================================================

-- ----------------------------------------------------
-- Ej. 1. La parte simétrica de una relación R es la 
-- relación S definida por
--    S x y := R x y ∧ R y x
-- 
-- Demostrar que la parte simétrica de una relación 
-- reflexiva es reflexiva.
-- ----------------------------------------------------

section

parameter A : Type
parameter R : A → A → Prop
parameter reflR : reflexive R

include reflR

def S (x y : A) := R x y ∧ R y x

-- 1ª demostración
example : reflexive S :=
begin
  intro x,
  split,
  { exact (reflR x), },
  { exact (reflR x), },
end

-- 2ª demostración
example : reflexive S :=
assume x,
have R x x, from reflR x,
show S x x, from and.intro this this

end
