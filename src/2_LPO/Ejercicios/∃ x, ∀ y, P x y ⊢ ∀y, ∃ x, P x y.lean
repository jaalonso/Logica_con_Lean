-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    ∃ x, ∀ y, P x y ⊢ ∀y, ∃ x, P x y
-- ----------------------------------------------------

import tactic

variable {U : Type}
variable {P : U → U → Prop}

-- 1ª demostración
example
  (h : ∃ x, ∀ y, P x y)
  : ∀y, ∃ x, P x y :=
begin
  intro b,
  cases h with a h1,
  use a,
  exact h1 b,
end
