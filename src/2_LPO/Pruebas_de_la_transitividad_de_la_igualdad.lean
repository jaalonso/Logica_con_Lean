-- Pruebas de la transitividad de la igualdad
-- ==========================================

import tactic

variable  (U : Type)
variables (x y z : U)

-- ----------------------------------------------------
-- Ej. 1. Demostrar que
--    x = y, y = z ⊢ x = z
-- ----------------------------------------------------

-- 1ª demostración
example 
  (h1 : x = y)
  (h2 : y = z)
  : x = z :=
eq.subst h2 h1

-- 2ª demostración
example 
  (h1 : x = y)
  (h2 : y = z)
  : x = z :=
h2 ▸ h1

-- 3ª demostración
example 
  (h1 : x = y)
  (h2 : y = z)
  : x = z :=
eq.substr h1 h2

-- 4ª demostración
example 
  (h1 : x = y)
  (h2 : y = z)
  : x = z :=
eq.trans h1 h2

-- 5ª demostración
example 
  (h1 : x = y)
  (h2 : y = z)
  : x = z :=
begin
  rw h1,
  exact h2,
end

-- 6ª demostración
example 
  (h1 : x = y)
  (h2 : y = z)
  : x = z :=
begin
  rw h1,
  assumption,
end

-- 7ª demostración
example 
  (h1 : x = y)
  (h2 : y = z)
  : x = z :=
begin
  rwa h1,
end

-- 8ª demostración
example 
  (h1 : x = y)
  (h2 : y = z)
  : x = z :=
by rwa h1

-- 9ª demostración
example 
  (h1 : x = y)
  (h2 : y = z)
  : x = z :=
begin
  rwa ←h2,
end

-- 10ª demostración
example 
  (h1 : x = y)
  (h2 : y = z)
  : x = z :=
begin
  rwa h2 at h1,
end

-- 11ª demostración
example 
  (h1 : x = y)
  (h2 : y = z)
  : x = z :=
by simp *

-- 12ª demostración
example 
  (h1 : x = y)
  (h2 : y = z)
  : x = z :=
-- by hint
by finish



