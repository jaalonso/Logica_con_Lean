-- ∃ x, P a → Q x ⊢ P a → (∃ x, Q x)
-- =================================

-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    ∃ x, P a → Q x ⊢ P a → (∃ x, Q x)
-- ----------------------------------------------------

import tactic

variable  (U : Type)
variable  (a : U)
variables (P Q : U -> Prop)

-- 1ª demostración
example
  (h : ∃ x, P a → Q x)
  : P a → (∃ x, Q x) :=
begin
  intro h1,
  cases h with b h2,
  use b,
  apply h2,
  exact h1,
end
