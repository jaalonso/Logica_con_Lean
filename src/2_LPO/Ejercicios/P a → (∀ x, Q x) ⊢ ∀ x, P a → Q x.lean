-- P a → (∀ x, Q x) ⊢ ∀ x, P a → Q x
-- =================================

-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    P a → (∀ x, Q x) ⊢ ∀ x, P a → Q x
-- ----------------------------------------------------

import tactic

variable  (U : Type)
variable  (a : U)
variables (P Q : U -> Prop)

-- 1ª demostración
example
  (h : P a → (∀ x, Q x))
  : ∀ x, P a → Q x :=
begin
  rintro b h1,
  exact (h h1) b,
end
