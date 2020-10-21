-- Pruebas de desarrollo de producto de sumas
-- ==========================================

-- ------------------------------------------------------
-- Ej. 1. Sean a, b, c y d números enteros. Demostrar que 
--    (a + b) * (c + d) = a * c + b * c + a * d + b * d 
-- ------------------------------------------------------

import tactic
import data.int.basic

variables a b c d : ℤ

-- 1ª demostración
example : (a + b) * (c + d) = a * c + b * c + a * d + b * d :=
calc
  (a + b) * (c + d) 
      = (a + b) * c + (a + b) * d         : by rw left_distrib
  ... = (a * c + b * c) + (a + b) * d     : by rw right_distrib
  ... = (a * c + b * c) + (a * d + b * d) : by rw right_distrib
  ... = a * c + b * c + a * d + b * d     : by rw ←add_assoc

-- 2ª demostración
example : (a + b) * (c + d) = a * c + b * c + a * d + b * d :=
by rw [left_distrib, right_distrib, right_distrib, ←add_assoc]

-- 3ª demostración
example : (a + b) * (c + d) = a * c + b * c + a * d + b * d :=
begin
  rw left_distrib,
  rw right_distrib,
  rw right_distrib,
  rw ←add_assoc,
end
 
-- 4ª demostración
example : (a + b) * (c + d) = a * c + b * c + a * d + b * d :=
calc
  (a + b) * (c + d) 
      = (a + b) * c + (a + b) * d         : by rw mul_add
  ... = (a * c + b * c) + (a + b) * d     : by rw add_mul
  ... = (a * c + b * c) + (a * d + b * d) : by rw add_mul
  ... = a * c + b * c + a * d + b * d     : by rw ←add_assoc

-- 5ª demostración
example : (a + b) * (c + d) = a * c + b * c + a * d + b * d :=
-- by hint
by linarith

-- 6ª demostración
example : (a + b) * (c + d) = a * c + b * c + a * d + b * d :=
by nlinarith
 
-- 7ª demostración
example : (a + b) * (c + d) = a * c + b * c + a * d + b * d :=
by ring

