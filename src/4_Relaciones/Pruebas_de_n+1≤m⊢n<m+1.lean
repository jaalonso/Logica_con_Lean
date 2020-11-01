-- Pruebas de n + 1 ≤ m ⊢ n < m + 1
-- ================================

-- ----------------------------------------------------
-- Ej. 1. Demostrar que si n y m son números naturales
-- tales que n + 1 ≤ m, entonces n < m + 1.
-- ----------------------------------------------------

import tactic

variables n m : ℕ

-- 1ª demostración
example 
  (h : n + 1 ≤ m) 
  : n < m + 1 :=
calc
  n   < n + 1 : lt_add_one n
  ... ≤ m     : h
  ... < m + 1 : lt_add_one m

-- 2ª demostración
example 
  (h : n + 1 ≤ m) 
  : n < m + 1 :=
have h1 : n < n + 1, from lt_add_one n,
have h2 : n < m,     from lt_of_lt_of_le h1 h,
have h3 : m < m + 1, from lt_add_one m,
show n < m + 1,      from lt.trans h2 h3

-- 3ª demostración
example 
  (h : n + 1 ≤ m) 
  : n < m + 1 :=
begin
  apply lt_trans (lt_add_one n),
  apply lt_of_le_of_lt h (lt_add_one m),
end

-- 4ª demostración
example 
  (h : n + 1 ≤ m) 
  : n < m + 1 :=
lt_trans (lt_add_one n) (lt_of_le_of_lt h (lt_add_one m))

-- 5ª demostración
example 
  (h : n + 1 ≤ m) 
  : n < m + 1 :=
-- by suggest
nat.lt.step h

-- 6ª demostración
example 
  (h : n + 1 ≤ m) 
  : n < m + 1 :=
-- by hint
by omega

-- 7ª demostración
example 
  (h : n + 1 ≤ m) 
  : n < m + 1 :=
by linarith

-- 8ª demostración
example 
  (h : n + 1 ≤ m) 
  : n < m + 1 :=
by nlinarith
