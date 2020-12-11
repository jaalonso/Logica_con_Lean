-- ∀ x, P x ⊢ ∀ y, P y
-- ===================

-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    ∀ x, P x ⊢ ∀ y, P y
-- ----------------------------------------------------

import tactic

variable {U : Type}
variable {P : U -> Prop}

-- 1ª demostración
example
  (h : ∀ x, P x)
  : ∀ y, P y :=
begin
  intro,
  exact h y,
end
