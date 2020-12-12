-- ∀ x, P x → Q a ⊢ ∃ x, P x → Q a
-- ===============================

-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    ∀ x, P x → Q a ⊢ ∃ x, P x → Q a
-- ----------------------------------------------------

import tactic

variable  (U : Type)
variable  (a : U)
variables (P Q : U -> Prop)

-- 1ª demostración
example
  (h : ∀ x, P x → Q a)
  : ∃ x, P x → Q a :=
begin
  by_cases h1: P a,
  { use a,
    exact h a, },
  { use a, },
end
