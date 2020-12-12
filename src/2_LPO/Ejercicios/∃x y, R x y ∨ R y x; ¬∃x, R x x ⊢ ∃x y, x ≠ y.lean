-- ----------------------------------------------------
-- Ejercicio. Demostrar o refutar
--    ∃x y, R x y ∨ R y x; ¬∃x, R x x ⊢ ∃x y, x ≠ y
-- ----------------------------------------------------

import tactic

variable {U : Type}
variable {R : U → U → Prop}

-- 1ª demostración
example
  (h1 : ∃x y, R x y ∨ R y x)
  (h2 : ¬(∃x, R x x))
  : ∃ (x : U) y, (x ≠ y) :=
begin
  rcases h1 with ⟨a, b, h3⟩,
  use [a, b],
  intro h4,
  apply h2,
  use b,
  cases h3 with h5 h6,
  { rwa h4 at h5, },
  { rwa h4 at h6, },
end
