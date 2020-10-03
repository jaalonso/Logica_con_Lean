-- Pruebas de ∀x (P(x) ∧ Q(x)) ↔ ∀x P(x) ∧ ∀x Q(x)
-- ===============================================

import tactic

section

variable  {U : Type}
variables {P Q : U -> Prop}

-- ------------------------------------------------------
-- Ej. 1. Demostrar
--    ∀x (P(x) ∧ Q(x)) ⊢ ∀x P(x) ∧ ∀x Q(x)
-- ------------------------------------------------------

-- 1ª demostración
example
  (h1 : ∀x, P x ∧ Q x)
  : (∀x, P x) ∧ (∀x, Q x) :=
have h5 : ∀x, P x, from
    assume x₀,
    have h3 : P x₀ ∧ Q x₀,  from h1 x₀,
    show P x₀,              from and.elim_left h3,
have h9 : ∀x, Q x, from
    assume x₁,
    have h7 : P x₁ ∧ Q x₁,  from h1 x₁,
    show Q x₁,              from and.elim_right h7,
show (∀x, P x) ∧ (∀x, Q x), from and.intro h5 h9

-- 2ª demostración
example
  (h1 : ∀x, P x ∧ Q x)
  : (∀x, P x) ∧ (∀x, Q x) :=
have h5 : ∀x, P x, from
    assume x₀,
    have h3 : P x₀ ∧ Q x₀,  from h1 x₀,
    show P x₀,              from h3.left,
have h9 : ∀x, Q x, from
    assume x₁,
    have h7 : P x₁ ∧ Q x₁,  from h1 x₁,
    show Q x₁,              from h7.right,
show (∀x, P x) ∧ (∀x, Q x), from ⟨h5, h9⟩

-- 3ª demostración
example
  (h1 : ∀x, P x ∧ Q x)
  : (∀x, P x) ∧ (∀x, Q x) :=
have h5 : ∀x, P x, from
    assume x₀,
    have h3 : P x₀ ∧ Q x₀,  from h1 x₀,
    h3.left,
have h9 : ∀x, Q x, from
    assume x₁,
    have h7 : P x₁ ∧ Q x₁,  from h1 x₁,
    h7.right,
show (∀x, P x) ∧ (∀x, Q x), from ⟨h5, h9⟩

-- 4ª demostración
example
  (h1 : ∀x, P x ∧ Q x)
  : (∀x, P x) ∧ (∀x, Q x) :=
have h5 : ∀x, P x, from
    assume x₀,
    (h1 x₀).left,
have h9 : ∀x, Q x, from
    assume x₁,
    (h1 x₁).right,
show (∀x, P x) ∧ (∀x, Q x), from ⟨h5, h9⟩

-- 5ª demostración
example
  (h1 : ∀x, P x ∧ Q x)
  : (∀x, P x) ∧ (∀x, Q x) :=
have h5 : ∀x, P x, from
    λ x₀, (h1 x₀).left,
have h9 : ∀x, Q x, from
    λ x₁, (h1 x₁).right,
show (∀x, P x) ∧ (∀x, Q x), from ⟨h5, h9⟩

-- 6ª demostración
example
  (h1 : ∀x, P x ∧ Q x)
  : (∀x, P x) ∧ (∀x, Q x) :=
have h5 : ∀x, P x, from
    λ x₀, (h1 x₀).left,
have h9 : ∀x, Q x, from
    λ x₁, (h1 x₁).right,
⟨h5, h9⟩

-- 7ª demostración
example
  (h1 : ∀x, P x ∧ Q x)
  : (∀x, P x) ∧ (∀x, Q x) :=
⟨λ x₀, (h1 x₀).left, λ x₁, (h1 x₁).right⟩

-- 8ª demostración
example
  (h1 : ∀x, P x ∧ Q x)
  : (∀x, P x) ∧ (∀x, Q x) :=
-- by library_search
forall_and_distrib.mp h1

-- 9ª demostración
example
  (h1 : ∀x, P x ∧ Q x)
  : (∀x, P x) ∧ (∀x, Q x) :=
begin
  split,
  { intro x₀,
    specialize h1 x₀,
    exact h1.left, },
  { intro x₁,
    specialize h1 x₁,
    exact h1.right, },
end

-- 9ª demostración
lemma aux1
  (h1 : ∀x, P x ∧ Q x)
  : (∀x, P x) ∧ (∀x, Q x) :=
-- by hint
by finish

-- ------------------------------------------------------
-- Ej. 2. Demostrar
--    ∀x P(x) ∧ ∀x Q(x) ⊢ ∀x (P(x) ∧ Q(x))
-- ------------------------------------------------------

-- 1ª demostración
example
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
assume x₀,
have h3 : ∀x, P x, from and.elim_left h1,
have h4 : P x₀,    from h3 x₀,
have h5 : ∀x, Q x, from and.elim_right h1,
have h6 : Q x₀,    from h5 x₀,
show P x₀ ∧ Q x₀,  from and.intro h4 h6

-- 2ª demostración
example
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
assume x₀,
have h3 : ∀x, P x, from h1.left,
have h4 : P x₀,    from h3 x₀,
have h5 : ∀x, Q x, from h1.right,
have h6 : Q x₀,    from h5 x₀,
show P x₀ ∧ Q x₀,  from ⟨h4, h6⟩

-- 3ª demostración
example
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
assume x₀,
have h3 : ∀x, P x, from h1.left,
have h4 : P x₀,    from h3 x₀,
have h5 : ∀x, Q x, from h1.right,
have h6 : Q x₀,    from h5 x₀,
⟨h4, h6⟩

-- 4ª demostración
example
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
assume x₀,
have h3 : ∀x, P x, from h1.left,
have h4 : P x₀,    from h3 x₀,
have h5 : ∀x, Q x, from h1.right,
⟨h4, h5 x₀⟩

-- 5ª demostración
example
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
assume x₀,
have h3 : ∀x, P x, from h1.left,
have h4 : P x₀,    from h3 x₀,
⟨h4, h1.right x₀⟩

-- 6ª demostración
example
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
assume x₀,
have h3 : ∀x, P x, from h1.left,
⟨h3 x₀, h1.right x₀⟩

-- 7ª demostración
example
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
assume x₀,
⟨h1.left x₀, h1.right x₀⟩

-- 8ª demostración
example
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
λ x₀, ⟨h1.left x₀, h1.right x₀⟩

-- 9ª demostración
example
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
-- by library_search
forall_and_distrib.mpr h1

-- 10ª demostración
example
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
begin
  cases h1 with h2 h3,
  intro x₀,
  split,
  { apply h2, },
  { apply h3, },
end

-- 11ª demostración
example
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
-- by hint
by tauto

-- 12ª demostración
lemma aux2
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
by finish

-- ------------------------------------------------------
-- Ej. 3. Demostrar
--    ∀x (P(x) ∧ Q(x)) ↔ ∀x P(x) ∧ ∀x Q(x)
-- ------------------------------------------------------

-- 1ª demostración
example :
  (∀x, P x ∧ Q x) ↔ (∀x, P x) ∧ (∀x, Q x) :=
iff.intro aux1 aux2

-- 2ª demostración
example :
  (∀x, P x ∧ Q x) ↔ (∀x, P x) ∧ (∀x, Q x) :=
-- by library_search
forall_and_distrib

-- 3ª demostración
example :
  (∀x, P x ∧ Q x) ↔ (∀x, P x) ∧ (∀x, Q x) :=
-- by hint
by finish

end
