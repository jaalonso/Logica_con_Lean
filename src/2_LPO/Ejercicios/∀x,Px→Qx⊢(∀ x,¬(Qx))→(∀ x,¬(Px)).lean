-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    ∀ x, P x → Q x ⊢ (∀ x, ¬(Q x)) → (∀ x, ¬(P x))
-- ----------------------------------------------------

import tactic

variable  {U : Type}
variables {P Q : U -> Prop}

-- 1ª demostración
example
  (h : ∀ x, P x → Q x)
  : (∀ x, ¬(Q x)) → (∀ x, ¬(P x)) :=
begin
  intros h1 a h2,
  apply h1 a,
  apply h a,
  exact h2,
end
