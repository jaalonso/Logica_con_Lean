-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    ∃ x y, R x y ∨ R y x ⊢ ∃ x y, R x y
-- ----------------------------------------------------

import tactic

variable {U : Type}
variable {R : U → U → Prop}

-- 1ª demostración
example
  (h : ∃ x y, R x y ∨ R y x)
  : ∃ x y, R x y :=
begin
  rcases h with ⟨a, b, (h1 | h2)⟩,
  { use [a, b],
    exact h1, },
  { use [b, a],
    exact h2, },
end
