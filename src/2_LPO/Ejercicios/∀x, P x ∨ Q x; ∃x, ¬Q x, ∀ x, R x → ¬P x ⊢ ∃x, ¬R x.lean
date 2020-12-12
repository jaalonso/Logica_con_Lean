-- ∀x, P x ∨ Q x; ∃x, ¬Q x, ∀ x, R x → ¬P x ⊢ ∃x, ¬R x
-- ===================================================

-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    ∀x, P x ∨ Q x; ∃x, ¬Q x; ∀ x, R x → ¬P x ⊢ ∃x, ¬R x
-- ----------------------------------------------------

import tactic

variable  (U : Type)
variables (P Q R : U → Prop)

-- 1ª demostración
example
  (h1 : ∀x, P x ∨ Q x)
  (h2 : ∃x, ¬Q x)
  (h3 : ∀ x, R x → ¬P x)
  : ∃x, ¬R x  :=
begin
  cases h2 with a h4,
  use a,
  intro h5,
  apply h4,
  cases (h1 a) with h6 h7,
  { exfalso,
    apply (h3 a) h5,
    exact h6, },
  { exact h7, },
end
