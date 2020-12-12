-- ----------------------------------------------------
-- Ejercicio. Demostrar o refutar
--    ∀y, Q a y;
--    ∀xy, Q x y → Q (s x) (s y)
--    ⊢ ∃z, Q a z ∧ Q z (s (s a))
-- ----------------------------------------------------

import tactic

variable (U : Type)
variable (Q : U → U → Prop)
variable (a : U)
variable (s : U → U)

-- 1ª demostración
example
  (h1 : ∀ y, Q a y)
  (h2 : ∀ x y, Q x y → Q (s x) (s y))
  : ∃z, Q a z ∧ Q z (s (s a)) :=
begin
  use a,
  split,
  { exact h1 a, },
  { exact h1 (s (s a)), },
end
