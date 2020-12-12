-- ¬(∀ x, ¬(P x)) ⊢ ∃ x, P x
-- =========================

-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    ¬(∀ x, ¬(P x)) ⊢ ∃ x, P x
-- ----------------------------------------------------

import tactic

variable (U : Type)
variable (P : U -> Prop)

open_locale classical

-- 1ª demostración
example
  (h: ¬(∀ x, ¬(P x)))
  : ∃ x, P x :=
begin
  by_contradiction h1,
  apply h,
  intros a h2,
  apply h1,
  use a,
  exact h2,
end

-- 2ª demostración
example
  (h: ¬(∀ x, ¬(P x)))
  : ∃ x, P x :=
begin
  push_neg at h,
  exact h,
end

-- 3ª demostración
example
  (h: ¬(∀ x, ¬(P x)))
  : ∃ x, P x :=
-- by library_search
not_forall_not.mp h
