-- ----------------------------------------------------
-- Ejercicio 30. Demostrar o refutar
--    (¬(∀ x, P x)) ↔ (∃x, ¬P x)
-- ----------------------------------------------------

import tactic

variable (U : Type)
variable (P : U -> Prop)

open_locale classical

-- 1ª demostración
example :
  (¬(∀ x, P x)) ↔ (∃x, ¬P x) :=
begin
  split,
  { intro h1,
    by_contradiction h2,
    apply h1,
    intro a,
    by_contradiction h3,
    apply h2,
    use a, },
  { rintro ⟨a, h4⟩ h5,
    apply h4,
    exact h5 a, },
end

-- 2ª demostración
example :
  (¬(∀ x, P x)) ↔ (∃x, ¬P x) :=
begin
  split,
  { intro h1,
    push_neg at h1,
    exact h1, },
  { intro h2,
    push_neg,
    exact h2, },
end

-- 3ª demostración
example :
  (¬(∀ x, P x)) ↔ (∃x, ¬P x) :=
begin
  push_neg,
  trivial,
end

-- 4ª demostración
example :
  (¬(∀ x, P x)) ↔ (∃x, ¬P x) :=
-- by library_search
not_forall
