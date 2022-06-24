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
assume a,
have h4 : P a → ¬Q a, from h1 a,
have h5 : P a,        from h2 a,
show ¬Q a,            from h4 h5

-- 2ª demostración
example
  (h1 : ∀x, P x → ¬Q x)
  (h2 : ∀x, P x)
  : ∀x, ¬Q x :=
assume a, (h1 a) (h2 a)

-- 3ª demostración
example
  (h1 : ∀x, P x → ¬Q x)
  (h2 : ∀x, P x)
  : ∀x, ¬Q x :=
λ a, (h1 a) (h2 a)

-- 4ª demostración
example
  (h1 : ∀x, P x → ¬Q x)
  (h2 : ∀x, P x)
  : ∀x, ¬Q x :=
begin
  intro a,
  apply h1,
  apply h2,
end

-- 5ª demostración
example
  (h1 : ∀x, P x → ¬Q x)
  (h2 : ∀x, P x)
  : ∀x, ¬Q x :=
begin
  intro a,
  exact (h1 a) (h2 a),
end

-- 6ª demostración
example
  (h1 : ∀x, P x → ¬Q x)
  (h2 : ∀x, P x)
  : ∀x, ¬Q x :=
begin
  intro a,
  specialize h1 a,
  specialize h2 a,
  apply h1,
  exact h2,
end

-- 7ª demostración
example
  (h1 : ∀x, P x → ¬Q x)
  (h2 : ∀x, P x)
  : ∀x, ¬Q x :=
begin
  intro a,
  specialize h1 a,
  specialize h2 a,
  exact h1 h2,
end

-- 8ª demostración
example
  (h1 : ∀x, P x → ¬Q x)
  (h2 : ∀x, P x)
  : ∀x, ¬Q x :=
-- by hint
by tauto

-- 9ª demostración
example
  (h1 : ∀x, P x → ¬Q x)
  (h2 : ∀x, P x)
  : ∀x, ¬Q x :=
by finish
