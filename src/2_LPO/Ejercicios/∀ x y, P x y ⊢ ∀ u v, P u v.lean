-- ∀ x y, P x y ⊢ ∀ u v, P u v
-- ===========================

-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    ∀ x y, P x y ⊢ ∀ u v, P u v
-- ----------------------------------------------------

import tactic

variable {U : Type}
variable {P : U → U → Prop}

-- 1ª demostración
example
  (h : ∀ x y, P x y)
  : ∀ u v, P u v :=
begin
  intros a b,
  exact h a b,
end

-- 2ª demostración
example
  (h : ∀ x y, P x y)
  : ∀ u v, P u v :=
λ a b, h a b

-- 3ª demostración
example
  (h : ∀ x y, P x y)
  : ∀ u v, P u v :=
h
