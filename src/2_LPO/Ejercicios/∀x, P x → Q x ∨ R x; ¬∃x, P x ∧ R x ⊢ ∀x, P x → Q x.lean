-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    ∀x, P x → Q x ∨ R x; ¬∃x, P x ∧ R x ⊢ ∀x, P x → Q x
-- ----------------------------------------------------

import tactic

variable  (U : Type)
variables (P Q R : U → Prop)

-- 1ª demostración
example
  (h1 : ∀x, P x → Q x ∨ R x)
  (h2 : ¬∃x, P x ∧ R x)
  : ∀x, P x → Q x :=
begin
  intros a h3,
  cases (h1 a) h3 with h4 h5,
  { exact h4, },
  { exfalso,
    apply h2,
    use a,
    exact ⟨h3, h5⟩, },
end
