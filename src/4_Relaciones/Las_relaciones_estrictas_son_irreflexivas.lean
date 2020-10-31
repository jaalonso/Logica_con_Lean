-- Las relaciones estrictas son irreflexivas
-- =========================================

import tactic

section

parameter {A : Type} 
parameter (R : A → A → Prop)

local infix ≤ := R

definition R' (a b : A) : Prop := 
  a ≤ b ∧ a ≠ b

local infix < := R'

-- 1ª demostración
example 
  (a : A) 
  : ¬ a < a :=
begin
  intro h,
  cases h with h1 h2,
  apply h2,
  refl,
end

-- 2ª demostración
example 
  (a : A) 
  : ¬ a < a :=
assume : a < a,
have a ≠ a, from and.right this,
have a = a, from rfl,
show false, from ‹a ≠ a› ‹a = a›

end
