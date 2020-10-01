-- Regla de eliminación del cuantificador existencial
-- ==================================================

-- Ej. 1. Demostrar
--    ∀x [P(x) → Q(x)], ∃x P(x) ⊢ ∃x Q(x)

import tactic

variable  U : Type
variables P Q : U -> Prop

-- 1ª demostración
-- ===============

example 
  (h1 : ∀x, P x → Q x) 
  (h2 : ∃x, P x)
  : ∃x, Q x :=
exists.elim h2 
  ( assume x₀ (h3 : P x₀),
    have h4 : P x₀ → Q x₀, from h1 x₀,
    have h5 : Q x₀,        from h4 h3,
    show ∃x, Q x,          from exists.intro x₀ h5 )

-- 2ª demostración
-- ===============

example 
  (h1 : ∀x, P x → Q x) 
  (h2 : ∃x, P x)
  : ∃x, Q x :=
exists.elim h2 
  ( assume x₀ (h3 : P x₀),
    have h4 : P x₀ → Q x₀, from h1 x₀,
    have h5 : Q x₀,        from h4 h3,
    show ∃x, Q x,          from ⟨x₀, h5⟩ )

-- 3ª demostración
-- ===============

example 
  (h1 : ∀x, P x → Q x) 
  (h2 : ∃x, P x)
  : ∃x, Q x :=
exists.elim h2 
  ( assume x₀ (h3 : P x₀),
    have h4 : P x₀ → Q x₀, from h1 x₀,
    have h5 : Q x₀,        from h4 h3,
    ⟨x₀, h5⟩ )

-- 4ª demostración
-- ===============

example 
  (h1 : ∀x, P x → Q x) 
  (h2 : ∃x, P x)
  : ∃x, Q x :=
exists.elim h2 
  ( assume x₀ (h3 : P x₀),
    have h4 : P x₀ → Q x₀, from h1 x₀,
    ⟨x₀, h4 h3⟩ )

-- 5ª demostración
-- ===============

example 
  (h1 : ∀x, P x → Q x) 
  (h2 : ∃x, P x)
  : ∃x, Q x :=
exists.elim h2 
  ( assume x₀ (h3 : P x₀),
    ⟨x₀, h1 x₀ h3⟩ )

-- 6ª demostración
-- ===============

example 
  (h1 : ∀x, P x → Q x) 
  (h2 : ∃x, P x)
  : ∃x, Q x :=
exists.elim h2 (λ x₀ h3, ⟨x₀, h1 x₀ h3⟩)

-- 7ª demostración
-- ===============

example 
  (h1 : ∀x, P x → Q x) 
  (h2 : ∃x, P x)
  : ∃x, Q x :=
-- by library_search
Exists.imp h1 h2

-- 8ª demostración
-- ===============

example 
  (h1 : ∀x, P x → Q x) 
  (h2 : ∃x, P x)
  : ∃x, Q x :=
begin
  cases h2 with x₀ h3,
  use x₀,
  apply h1,
  exact h3,
end

-- 9ª demostración
-- ===============

example 
  (h1 : ∀x, P x → Q x) 
  (h2 : ∃x, P x)
  : ∃x, Q x :=
begin
  cases h2 with x₀ h3,
  use x₀,
  specialize h1 x₀,
  apply h1,
  exact h3,
end

-- 10ª demostración
-- ===============

example 
  (h1 : ∀x, P x → Q x) 
  (h2 : ∃x, P x)
  : ∃x, Q x :=
-- by hint
by tauto

-- 11ª demostración
-- ===============

example 
  (h1 : ∀x, P x → Q x) 
  (h2 : ∃x, P x)
  : ∃x, Q x :=
by finish
