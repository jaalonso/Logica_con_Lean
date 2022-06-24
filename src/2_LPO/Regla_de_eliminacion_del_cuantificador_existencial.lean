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
  ( assume a (h3 : P a),
    have h4 : P a → Q a, from h1 a,
    have h5 : Q a,       from h4 h3,
    show ∃x, Q x,        from exists.intro a h5 )

-- 2ª demostración
-- ===============

example
  (h1 : ∀x, P x → Q x)
  (h2 : ∃x, P x)
  : ∃x, Q x :=
exists.elim h2
  ( assume a (h3 : P a),
    have h4 : P a → Q a, from h1 a,
    have h5 : Q a,       from h4 h3,
    show ∃x, Q x,        from ⟨a, h5⟩ )

-- 3ª demostración
-- ===============

example
  (h1 : ∀x, P x → Q x)
  (h2 : ∃x, P x)
  : ∃x, Q x :=
exists.elim h2
  ( assume a (h3 : P a),
    have h4 : P a → Q a, from h1 a,
    have h5 : Q a,       from h4 h3,
    ⟨a, h5⟩ )

-- 4ª demostración
-- ===============

example
  (h1 : ∀x, P x → Q x)
  (h2 : ∃x, P x)
  : ∃x, Q x :=
exists.elim h2
  ( assume a (h3 : P a),
    have h4 : P a → Q a, from h1 a,
    ⟨a, h4 h3⟩ )

-- 5ª demostración
-- ===============

example
  (h1 : ∀x, P x → Q x)
  (h2 : ∃x, P x)
  : ∃x, Q x :=
exists.elim h2
  ( assume a (h3 : P a),
    ⟨a, h1 a h3⟩ )

-- 6ª demostración
-- ===============

example
  (h1 : ∀x, P x → Q x)
  (h2 : ∃x, P x)
  : ∃x, Q x :=
exists.elim h2 (λ a h3, ⟨a, h1 a h3⟩)

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
  cases h2 with a h3,
  use a,
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
  cases h2 with a h3,
  use a,
  specialize h1 a,
  apply h1,
  exact h3,
end

-- 10ª demostración
-- ===============

example
  (h1 : ∀x, P x → Q x)
  (h2 : ∃x, P x)
  : ∃x, Q x :=
begin
  cases h2 with a h3,
  use a,
  exact (h1 a) h3,
end

-- 11ª demostración
-- ===============

example
  (h1 : ∀x, P x → Q x)
  (h2 : ∃x, P x)
  : ∃x, Q x :=
begin
  cases h2 with a h3,
  exact ⟨a, (h1 a) h3⟩,
end

-- 12ª demostración
-- ===============

example
  (h1 : ∀x, P x → Q x)
  (h2 : ∃x, P x)
  : ∃x, Q x :=
-- by hint
by tauto

-- 13ª demostración
-- ===============

example
  (h1 : ∀x, P x → Q x)
  (h2 : ∃x, P x)
  : ∃x, Q x :=
by finish
