-- ----------------------------------------------------
-- Ejercicio. Demostrar
--      {∀ x y z, R x y ∧ R y z → R x z,
--       ∀ x, ¬(R x x)}
--      ⊢ ∀ x y, R x y → ¬(R y x)
-- ----------------------------------------------------

import tactic

variable {U : Type}
variable {R : U → U → Prop}

-- 1ª demostración
example
  (h1 : ∀ x y z, R x y ∧ R y z → R x z)
  (h2 : ∀ x, ¬(R x x))
  : ∀ x y, R x y → ¬(R y x) :=
begin
  intros a b h3 h4,
  apply h2 a,
  apply h1 a b a,
  exact ⟨h3, h4⟩,
end
