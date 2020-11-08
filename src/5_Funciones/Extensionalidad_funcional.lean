-- Extensionalidad funcional
-- =========================

-- ----------------------------------------------------
-- Ej. 1. Sean f y g funciones de X en Y. Demostrar que 
-- si
--    ∀ (x : X), f x = g x
-- entonces, las funciones f y g son iguales.
-- ----------------------------------------------------

variables {X Y : Type}
variables (f g : X → Y)

example  
  (h : ∀ x, f x = g x) 
  : f = g :=
funext h
