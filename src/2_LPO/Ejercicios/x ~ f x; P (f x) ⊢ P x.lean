-- ----------------------------------------------------
-- Ejercicio. Demostrar o refutar
--    x = f x; P (f x) ⊢ P x
-- ----------------------------------------------------

import tactic

variable (U : Type)
variable (P :  U → Prop)
variable (f : U → U)
variable (x : U)

-- 1ª demostración
example
  (h1 : x = f x)
  (h2 : P (f x))
  : P x :=
begin
  rw h1,
  exact h2,
end

-- 2ª demostración
example
  (h1 : x = f x)
  (h2 : P (f x))
  : P x :=
begin
  rwa h1,
end

-- 3ª demostración
example
  (h1 : x = f x)
  (h2 : P (f x))
  : P x :=
by rwa h1
