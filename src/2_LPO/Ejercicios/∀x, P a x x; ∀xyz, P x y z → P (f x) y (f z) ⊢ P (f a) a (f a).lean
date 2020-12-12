-- ----------------------------------------------------
-- Ejercicio. Demostrar o refutar
--    ∀x, P a x x;
--    ∀xyz, P x y z → P (f x) y (f z)
--    ⊢ P (f a) a (f a)
-- ----------------------------------------------------

import tactic

variable (U : Type)
variable (P : U → U → U → Prop)
variable (a : U)
variable (f : U → U)

-- 1ª demostración
example
  (h1 : ∀ x, P a x x)
  (h2 : ∀ x y z, P x y z → P (f x) y (f z))
  : P (f a) a (f a) :=
begin
  apply h2,
  exact h1 a,
end

-- 2ª demostración
example
  (h1 : ∀ x, P a x x)
  (h2 : ∀ x y z, P x y z → P (f x) y (f z))
  : P (f a) a (f a) :=
h2 a a a (h1 a)
