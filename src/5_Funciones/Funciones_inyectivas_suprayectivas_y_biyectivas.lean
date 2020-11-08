-- Funciones inyectivas, suprayectivas y biyectivas
-- ================================================

-- ----------------------------------------------------
-- Ej. 1. Definir las funciones inyectivas, 
-- suprayectivas y biyectivas.
-- ----------------------------------------------------

variables {X Y Z : Type}

def injective (f : X → Y) : Prop :=
∀ ⦃x₁ x₂⦄, f x₁ = f x₂ → x₁ = x₂

def surjective (f : X → Y) : Prop :=
∀ y, ∃ x, f x = y

def bijective (f : X → Y) : Prop := 
injective f ∧ surjective f
