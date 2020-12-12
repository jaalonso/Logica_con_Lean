-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    ∃ x, P x ∧ Q x ⊢ (∃ x, P x) ∧ (∃ x, Q x)
-- ----------------------------------------------------

import tactic

variable  (U : Type)
variables (P Q : U → Prop)

-- 1ª demostración
example
  (h : ∃ x, P x ∧ Q x)
  : (∃ x, P x) ∧ (∃ x, Q x) :=
begin
  rcases h with ⟨a, hP, hQ⟩,
  split,
  { use a,
    exact hP, },
  { use a,
    exact hQ, },
end

-- 1ª demostración
example
  (h : ∃ x, P x ∧ Q x)
  : (∃ x, P x) ∧ (∃ x, Q x) :=
begin
  rcases h with ⟨a, hP, hQ⟩,
  exact ⟨⟨a, hP⟩, ⟨a,hQ⟩⟩,
end
