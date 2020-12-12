-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    ∀ x, ¬(P x) ⊢ ¬(∃ x, P x)
-- ----------------------------------------------------

import tactic

variable (U : Type)
variable (P : U -> Prop)

-- 1ª demostración
example
  (h : ∀ x, ¬(P x))
  : ¬(∃ x, P x) :=
begin
  rintro ⟨a, h1⟩,
  apply h a,
  exact h1,
end

-- 2ª demostración
example
  (h : ∀ x, ¬(P x))
  : ¬(∃ x, P x) :=
begin
  push_neg,
  exact h,
end

-- 3ª demostración
example
  (h : ∀ x, ¬(P x))
  : ¬(∃ x, P x) :=
-- by library_search
not_exists.mpr h
