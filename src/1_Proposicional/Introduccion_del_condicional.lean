-- Introducción del condicional en Lean
-- =====================================================================

-- ---------------------------------------------------------------------
-- Ejercicio 1. Demostrar que
--    P → P
-- ---------------------------------------------------------------------

import tactic          
variable (P : Prop)   

-- 1ª demostración
example : P → P :=
assume h : P, 
show P, from h

-- 2ª demostración
example : P → P :=
assume : P, 
show P, from this

-- 3ª demostración
example : P → P :=
assume : P, 
show P, from ‹P›

-- 4ª demostración
example : P → P :=
assume h : P, h

-- 5ª demostración
example : P → P :=
λ h, h

-- 6ª demostración
example : P → P :=
id

-- 7ª demostración
example : P → P :=
begin
  intro h,
  exact h,
end

-- 8ª demostración
example : P → P :=
begin
  intro,
  exact ‹P›,
end

-- 9ª demostración
example : P → P :=
begin
  intro h,
  assumption,
end

-- 10ª demostración
example : P → P :=
begin
  intro,
  assumption,
end

-- 11ª demostración
example : P → P :=
by tauto

-- 12ª demostración
example : P → P :=
by finish  

-- 13ª demostración
example : P → P :=
by simp
