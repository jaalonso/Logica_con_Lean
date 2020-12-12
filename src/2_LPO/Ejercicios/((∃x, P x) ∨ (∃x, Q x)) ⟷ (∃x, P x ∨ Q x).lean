-- ((∃x, P x) ∨ (∃x, Q x)) ⟷ (∃x, P x ∨ Q x)
-- =========================================

-- ----------------------------------------------------
-- Ejercicio. Demostrar o refutar
--    ((∃x, P x) ∨ (∃x, Q x)) ⟷ (∃x, P x ∨ Q x)
-- ----------------------------------------------------

import tactic

variable  (U : Type)
variables (P Q : U → Prop)

-- 1ª demostración
example :
  ((∃x, P x) ∨ (∃x, Q x)) ↔ (∃x, P x ∨ Q x) :=
begin
  split,
  { rintro (⟨a, h1⟩ | ⟨a, h2⟩),
    { use a,
      left,
      exact h1, },
    { use a,
      right,
      exact h2, }},
  { rintro ⟨a, (h3 | h4)⟩,
    { left,
      use a,
      exact h3, },
    { right,
      use a,
      exact h4, }},
end
