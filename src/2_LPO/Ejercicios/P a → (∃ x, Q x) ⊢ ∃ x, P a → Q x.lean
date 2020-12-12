-- P a → (∃ x, Q x) ⊢ ∃ x, P a → Q x
-- =================================

-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    P a → (∃ x, Q x) ⊢ ∃ x, P a → Q x
-- ----------------------------------------------------

import tactic

variable  (U : Type)
variable  (a : U)
variables (P Q : U -> Prop)

-- 1ª demostración
example
  (h : P a → (∃ x, Q x))
  : ∃ x, P a → Q x :=
begin
  by_cases h1 : P a,
  { cases (h h1) with b h2,
    use b,
    intro,
    exact h2, },
  { use a, },
end
