-- Regla de eliminación de la igualdad
-- ===================================

import tactic

#check @eq.subst

-- ----------------------------------------------------
-- Ej. 1. Demostrar que
--      x + 1 = 1 + x
--      x + 1 > 1 → x + 1 > 0
--      ⊢ 1 + x > 1 → 1 + x > 0
-- ----------------------------------------------------

variable (U : Type)
variable (x : U)
variable [has_add U]
variable [has_one U]
variable [has_lt U]
variable [has_zero U]

-- 1ª demostración
example 
  (h1 : x + 1 = 1 + x)
  (h2 : x + 1 > 1 → x + 1 > 0)
  : 1 + x > 1 → 1 + x > 0 :=
eq.subst h1 h2


-- 2ª demostración
example 
  (h1 : x + 1 = 1 + x)
  (h2 : x + 1 > 1 → x + 1 > 0)
  : 1 + x > 1 → 1 + x > 0 :=
h1 ▸ h2

-- 3ª demostración
example 
  (h1 : x + 1 = 1 + x)
  (h2 : x + 1 > 1 → x + 1 > 0)
  : 1 + x > 1 → 1 + x > 0 :=
begin
  rw h1 at h2,
  exact h2,
end

-- 4ª demostración
example 
  (h1 : x + 1 = 1 + x)
  (h2 : x + 1 > 1 → x + 1 > 0)
  : 1 + x > 1 → 1 + x > 0 :=
begin
  rw ←h1,
  exact h2,
end

-- 5ª demostración
example 
  (h1 : x + 1 = 1 + x)
  (h2 : x + 1 > 1 → x + 1 > 0)
  : 1 + x > 1 → 1 + x > 0 :=
-- by hint
by finish
