-- Regla de introducción de la igualdad
-- ====================================

import tactic

#check @eq.refl

variable  (U : Type)
variables (x y : U)

-- ----------------------------------------------------
-- Ej. Demostrar
--    x = y ⊢ y = x 
-- ----------------------------------------------------

-- 1ª demostración
example
  (h1 : x = y)
  : y = x :=
have h2 : x = x, from eq.refl x,
show y = x,      from eq.subst h1 h2

-- 2ª demostración
example
  (h1 : x = y)
  : y = x :=
have h2 : x = x, from eq.refl x,
show y = x,      from h1 ▸ h2

-- 3ª demostración
example
  (h1 : x = y)
  : y = x :=
have h2 : x = x, from eq.refl x,
h1 ▸ h2

-- 4ª demostración
example
  (h1 : x = y)
  : y = x :=
h1 ▸ eq.refl x

-- 5ª demostración
example
  (h1 : x = y)
  : y = x :=
h1 ▸ rfl

-- 6ª demostración
example
  (h1 : x = y)
  : y = x :=
-- by library_search
eq.symm h1

-- 7ª demostración
example
  (h1 : x = y)
  : y = x :=
begin
  rw h1,
end

-- 8ª demostración
example
  (h1 : x = y)
  : y = x :=
by rw h1

-- 9ª demostración
example
  (h1 : x = y)
  : y = x :=
by simp *

-- 10ª demostración
example
  (h1 : x = y)
  : y = x :=
-- by hint
by tauto

-- 11ª demostración
example
  (h1 : x = y)
  : y = x :=
by finish

-- 12ª demostración
example
  (h1 : x = y)
  : y = x :=
by solve_by_elim



