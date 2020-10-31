-- Las partes estrictas son irreflexivas
-- =====================================

-- ----------------------------------------------------
-- Ej. 1. La parte estricta de una relación R es la 
-- relación R' definida por
--    R' a b := R a b ∧ a ≠ b 
-- 
-- Demostrar que la parte estricta de cualquier 
-- relación es irreflexiva.
-- ----------------------------------------------------

import tactic

section

parameter {A : Type} 
parameter (R : A → A → Prop)

definition R' (a b : A) : Prop := 
  R a b ∧ a ≠ b

#reduce irreflexive R

-- 1ª demostración
example : 
  irreflexive R' :=
begin
  intros a h,
  cases h with h1 h2,
  apply h2,
  refl,
end

-- 2ª demostración
example :
  irreflexive R' :=
assume a,
assume : R' a a,
have a ≠ a, from and.right this,
have a = a, from rfl,
show false, from ‹a ≠ a› ‹a = a›

end
