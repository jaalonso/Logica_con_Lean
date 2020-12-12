-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    ∃ x y, P x y ⊢ ∃ u v, P u v
-- ----------------------------------------------------

import tactic

variable {U : Type}
variable {P : U → U → Prop}

-- 1ª demostración
example
  (h : ∃ x y, P x y)
  : ∃ u v, P u v :=
begin
  rcases h with ⟨a,b,h1⟩,
  use [a,b],
  exact h1,
end
