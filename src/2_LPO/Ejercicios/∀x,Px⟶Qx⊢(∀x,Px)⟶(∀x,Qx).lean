-- ∀ x, P x ⟶ Q x ⊢ (∀ x, P x) ⟶ (∀ x, Q x)
-- =====================================

-- ----------------------------------------------------
-- Ejercicio 1. Demostrar
--    ∀ x, P x ⟶ Q x ⊢ (∀ x, P x) ⟶ (∀ x, Q x)
-- ----------------------------------------------------

import tactic

variable  {U : Type}
variables {P Q : U -> Prop}

-- 1ª demostración
example
  (h : ∀ x, P x → Q x)
  : (∀ x, P x) → (∀ x, Q x) :=
begin
  intros h1 a,
  exact (h a) (h1 a),
end

-- 2ª demostración
example
  (h : ∀ x, P x → Q x)
  : (∀ x, P x) → (∀ x, Q x) :=
λ h1 a, (h a) (h1 a)

-- 3ª demostración
example
  (h : ∀ x, P x → Q x)
  : (∀ x, P x) → (∀ x, Q x) :=
assume h1 : ∀ x, P x,
show ∀ x, Q x, from
  assume a,
  have h2 : P a → Q a,
    from h a,
  have h3 : P a,
    from h1 a,
  show Q a,
    from h2 h3

-- 4ª demostración
example
  (h : ∀ x, P x → Q x)
  : (∀ x, P x) → (∀ x, Q x) :=
assume h1 : ∀ x, P x,
show ∀ x, Q x, from
  assume a,
  have h2 : P a → Q a,
    from h a,
  have h3 : P a,
    from h1 a,
  h2 h3

-- 5ª demostración
example
  (h : ∀ x, P x → Q x)
  : (∀ x, P x) → (∀ x, Q x) :=
assume h1 : ∀ x, P x,
show ∀ x, Q x, from
  assume a,
  (h a) (h1 a)

-- 6ª demostración
example
  (h : ∀ x, P x → Q x)
  : (∀ x, P x) → (∀ x, Q x) :=
assume h1 : ∀ x, P x,
λ a, (h a) (h1 a)

-- 7ª demostración
example
  (h : ∀ x, P x → Q x)
  : (∀ x, P x) → (∀ x, Q x) :=
λ h1 a, (h a) (h1 a)

-- 8ª demostración
example
  (h : ∀ x, P x → Q x)
  : (∀ x, P x) → (∀ x, Q x) :=
-- by library_search
forall_imp h

-- 9ª demostración
example
  (h : ∀ x, P x → Q x)
  : (∀ x, P x) → (∀ x, Q x) :=
-- by hint
by tauto

-- 10ª demostración
example
  (h : ∀ x, P x → Q x)
  : (∀ x, P x) → (∀ x, Q x) :=
by finish
