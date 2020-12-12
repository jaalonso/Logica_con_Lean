-- ----------------------------------------------------
-- Ejercicio. Demostrar o refutar
--    P a ⊢ ∀ x, x = a → P x
-- ----------------------------------------------------

import tactic

variable  (U : Type)
variable  (a : U)
variables (P Q : U -> Prop)

-- 1ª demostración
example
  (h : P a)
  : ∀ x, x = a → P x :=
begin
  intros b h1,
  rw h1,
  exact h,
end

-- 1ª demostración
example
  (h : P a)
  : ∀ x, x = a → P x :=
begin
  intros b h1,
  rwa h1,
end
