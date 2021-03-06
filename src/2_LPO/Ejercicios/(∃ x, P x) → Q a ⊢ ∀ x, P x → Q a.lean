-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    (∃ x, P x) → Q a ⊢ ∀ x, P x → Q a
-- ----------------------------------------------------

import tactic

variable  (U : Type)
variable  (a : U)
variables (P Q : U -> Prop)

-- 1ª demostración
example
  (h : (∃ x, P x) → Q a)
  : ∀ x, P x → Q a :=
begin
  intros b h1,
  apply h,
  use b,
  exact h1,
end
