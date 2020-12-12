-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    ∀ x, P x → ¬(Q x) ⊢ ¬(∃ x, P x ∧ Q x)
-- ----------------------------------------------------

import tactic

variable  {U : Type}
variables {P Q : U -> Prop}

-- 1ª demostración
example
  (h : ∀ x, P x → ¬(Q x))
  : ¬(∃ x, P x ∧ Q x) :=
begin
  intro h1,
  cases h1 with a h2,
  apply h a,
  { exact h2.1, },
  { exact h2.2, },
end

-- 2ª demostración
example
  (h : ∀ x, P x → ¬(Q x))
  : ¬(∃ x, P x ∧ Q x) :=
begin
  rintro ⟨a,h1,h2⟩,
  apply h a,
  assumption,
  assumption,
end
