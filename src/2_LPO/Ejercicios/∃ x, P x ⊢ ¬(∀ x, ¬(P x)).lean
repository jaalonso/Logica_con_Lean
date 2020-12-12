-- ∃ x, P x ⊢ ¬(∀ x, ¬(P x))
-- =========================

-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    ∃ x, P x ⊢ ¬(∀ x, ¬(P x))
-- ----------------------------------------------------

import tactic

variable (U : Type)
variable (P : U -> Prop)

-- 1ª demostración
example
  (h : ∃ x, P x)
  : ¬(∀ x, ¬(P x)) :=
begin
  intro h1,
  cases h with a h2,
  apply h1 a,
  exact h2,
end
