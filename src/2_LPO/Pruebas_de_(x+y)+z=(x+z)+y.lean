-- Pruebas de (x + y) + z = (x + z) + y
-- ====================================

-- ----------------------------------------------------
-- Ej. 1. Demostrar que para todo x, y, z en ℤ se tiene
--    (x + y) + z = (x + z) + y
-- ----------------------------------------------------

import tactic
import data.int.basic

variables (x y z : ℤ)

-- 1ª demostración
example : (x + y) + z = (x + z) + y :=
calc
   (x + y) + z = x + (y + z) : add_assoc x y z
           ... = x + (z + y) : eq.subst (add_comm y z) rfl
           ... = (x + z) + y : eq.symm (add_assoc x z y)

-- 2ª demostración
example : (x + y) + z = (x + z) + y :=
calc
  (x + y) + z = x + (y + z) : by rw add_assoc
          ... = x + (z + y) : by rw [add_comm y z]
          ... = (x + z) + y : by rw add_assoc

-- 3ª demostración
example : (x + y) + z = (x + z) + y :=
begin
  rw add_assoc,
  rw add_comm y z,
  rw add_assoc,
end

example : (x + y) + z = (x + z) + y :=
begin
  rw [add_assoc, add_comm y z, add_assoc],
end

-- 4ª demostración
example : (x + y) + z = (x + z) + y :=
by rw [add_assoc, add_comm y z, add_assoc]

-- 5ª demostración
example : (x + y) + z = (x + z) + y :=
-- by library_search
add_right_comm x y z

-- 6ª demostración
example : (x + y) + z = (x + z) + y :=
-- by hint
by omega

-- 7ª demostración
example : (x + y) + z = (x + z) + y :=
by linarith

-- 8ª demostración
example : (x + y) + z = (x + z) + y :=
by nlinarith

-- 9ª demostración
example : (x + y) + z = (x + z) + y :=
by ring

-- 10ª demostración
example : (x + y) + z = (x + z) + y :=
by finish

