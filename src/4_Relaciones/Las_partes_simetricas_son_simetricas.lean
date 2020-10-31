-- Las partes simétricas son transitivas
-- =====================================

-- ----------------------------------------------------
-- Ej. 1. La parte simétrica de una relación R es la 
-- relación S definida por
--    S x y := R x y ∧ R y x
-- 
-- Demostrar que la parte simétrica de cualquier 
-- relación es transitiva.
-- ----------------------------------------------------

section
parameter A : Type
parameter R : A → A → Prop

def S (x y : A) := R x y ∧ R y x

-- 1ª demostración
example : symmetric S :=
begin
  intros x y h,
  split,
  { exact h.right, },
  { exact h.left, },
end

-- 2ª demostración
example : symmetric S :=
assume x y,
assume h : S x y,
have h1 : R x y, from h.left,
have h2 : R y x, from h.right,
show S y x, from ⟨h2, h1⟩

-- 3ª demostración
example : symmetric S :=
assume x y,
assume h : S x y,
show S y x, from ⟨h.right, h.left⟩

-- 4ª demostración
example : symmetric S :=
λ x y h, ⟨h.right, h.left⟩

end
