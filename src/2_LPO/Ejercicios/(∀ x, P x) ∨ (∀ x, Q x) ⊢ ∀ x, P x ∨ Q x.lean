-- (∀ x, P x) ∨ (∀ x, Q x) ⊢ ∀ x, P x ∨ Q x
-- ========================================

-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    (∀ x, P x) ∨ (∀ x, Q x) ⊢ ∀ x, P x ∨ Q x
-- ----------------------------------------------------

import tactic

variable  (U : Type)
variables (P Q : U → Prop)

-- 1ª demostración
example
  (h : (∀ x, P x) ∨ (∀ x, Q x))
  : ∀ x, P x ∨ Q x :=
begin
  intro a,
  rcases h with (h1 | h2),
  { left,
    exact h1 a, },
  { right,
    exact h2 a, },
end
