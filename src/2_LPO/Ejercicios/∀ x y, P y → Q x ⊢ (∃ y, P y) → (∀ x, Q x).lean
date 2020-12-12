-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    ∀ x y, P y → Q x ⊢ (∃ y, P y) → (∀ x, Q x)
-- ----------------------------------------------------

import tactic

variable  (U : Type)
variables (P Q : U → Prop)

-- 1ª demostración
example
  (h : ∀ x y, P y → Q x)
  : (∃ y, P y) → (∀ x, Q x) :=
begin
  intros h1 a,
  cases h1 with b h2,
  apply (h a b),
  exact h2,
end

-- 2ª demostración
example
  (h : ∀ x y, P y → Q x)
  : (∃ y, P y) → (∀ x, Q x) :=
begin
  rintro ⟨b, h1⟩ a,
  exact (h a b) h1,
end

-- 3ª demostración
example
  (h : ∀ x y, P y → Q x)
  : (∃ y, P y) → (∀ x, Q x) :=
λ ⟨b, h1⟩ a, (h a b) h1
