-- Regla de introducción del cuantificador universal
-- =================================================

-- Ej. 1. Demostrar
--    ∀x [P(x) → ¬Q(x)], ∀x P(x) ⊢ ∀x ¬Q(x)

import tactic

variable  U : Type
variables P Q : U → Prop

-- 1ª demostración
example
  (h1 : ∀x, P x → ¬Q x) 
  (h2 : ∀x, P x)
  : ∀x, ¬Q x :=
assume x₀,
have h4 : P x₀ → ¬Q x₀, from h1 x₀,
have h5 : P x₀,         from h2 x₀,
show ¬Q x₀,             from h4 h5 

-- 2ª demostración
example
  (h1 : ∀x, P x → ¬Q x) 
  (h2 : ∀x, P x)
  : ∀x, ¬Q x :=
assume x₀, (h1 x₀) (h2 x₀) 

-- 3ª demostración
example
  (h1 : ∀x, P x → ¬Q x) 
  (h2 : ∀x, P x)
  : ∀x, ¬Q x :=
λ x₀, (h1 x₀) (h2 x₀) 

-- 4ª demostración
example
  (h1 : ∀x, P x → ¬Q x) 
  (h2 : ∀x, P x)
  : ∀x, ¬Q x :=
begin
  intro x₀,
  apply h1,
  apply h2,
end

-- 5ª demostración
example
  (h1 : ∀x, P x → ¬Q x) 
  (h2 : ∀x, P x)
  : ∀x, ¬Q x :=
begin
  intro x₀,
  specialize h1 x₀,
  specialize h2 x₀,
  apply h1,
  exact h2,
end

-- 6ª demostración
example
  (h1 : ∀x, P x → ¬Q x) 
  (h2 : ∀x, P x)
  : ∀x, ¬Q x :=
begin
  intro x₀,
  specialize h1 x₀,
  specialize h2 x₀,
  exact h1 h2,
end

-- 7ª demostración
example
  (h1 : ∀x, P x → ¬Q x) 
  (h2 : ∀x, P x)
  : ∀x, ¬Q x :=
-- by hint
by tauto

-- 8ª demostración
example
  (h1 : ∀x, P x → ¬Q x) 
  (h2 : ∀x, P x)
  : ∀x, ¬Q x :=
by finish
