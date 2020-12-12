-- ----------------------------------------------------
-- Ejercicio. Demostrar o refutar
--    ∀x, P a x x; ∀xyz, P x y z → P (f x) y (f z) ⊢ ∃z, P (f a) z (f (f a))
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
  : ∃ z, P (f a) z (f (f a)) :=
begin
  use f a,
  apply h2,
  exact h1 (f a),
end
