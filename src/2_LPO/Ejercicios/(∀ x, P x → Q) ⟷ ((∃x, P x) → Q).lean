-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    (∀ x, P x → Q) ⟷ ((∃x, P x) → Q)
-- ----------------------------------------------------

import tactic

variable (U : Type)
variable (P : U -> Prop)
variable (Q : Prop)

-- 1ª demostración
example :
  (∀ x, P x → Q) ↔ ((∃x, P x) → Q) :=
begin
  split,
  { rintros h1 ⟨a, h2⟩,
    exact h1 a h2, },
  { intros h3 a h4,
    apply h3,
    use a,
    exact h4, },
end
