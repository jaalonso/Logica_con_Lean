-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    ((∀x, P x) ∧ (∀x, Q x)) ↔ (∀x, P x ∧ Q x)
-- ----------------------------------------------------

import tactic

variable  (U : Type)
variables (P Q : U → Prop)

-- 1ª demostración
example :
  ((∀x, P x) ∧ (∀x, Q x)) ↔ (∀x, P x ∧ Q x) :=
begin
  split,
  { rintros ⟨h1, h2⟩ a,
    exact ⟨h1 a, h2 a⟩, },
  { intro h3,
    split,
    { intro a,
      exact (h3 a).left, },
    { intro a,
      exact (h3 a).right, }},
end
