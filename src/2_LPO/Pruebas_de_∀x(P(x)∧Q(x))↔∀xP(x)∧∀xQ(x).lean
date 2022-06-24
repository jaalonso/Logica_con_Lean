-- Pruebas de ∀x (P(x) ∧ Q(x)) ↔ ∀x P(x) ∧ ∀x Q(x)
-- ===============================================

import tactic

section

variable  {U : Type}
variables {P Q : U -> Prop}

-- ----------------------------------------------------
-- Ej. 1. Demostrar
--    ∀x (P(x) ∧ Q(x)) ⊢ ∀x P(x) ∧ ∀x Q(x)
-- ----------------------------------------------------

-- 1ª demostración
example
  (h1 : ∀x, P x ∧ Q x)
  : (∀x, P x) ∧ (∀x, Q x) :=
have h5 : ∀x, P x, from
    assume a,
    have h3 : P a ∧ Q a,  from h1 a,
    show P a,             from and.elim_left h3,
have h9 : ∀x, Q x, from
    assume b,
    have h7 : P b ∧ Q b,  from h1 b,
    show Q b,              from and.elim_right h7,
show (∀x, P x) ∧ (∀x, Q x), from and.intro h5 h9

-- 2ª demostración
example
  (h1 : ∀x, P x ∧ Q x)
  : (∀x, P x) ∧ (∀x, Q x) :=
have h5 : ∀x, P x, from
    assume a,
    have h3 : P a ∧ Q a,  from h1 a,
    show P a,             from h3.left,
have h9 : ∀x, Q x, from
    assume b,
    have h7 : P b ∧ Q b,  from h1 b,
    show Q b,              from h7.right,
show (∀x, P x) ∧ (∀x, Q x), from ⟨h5, h9⟩

-- 3ª demostración
example
  (h1 : ∀x, P x ∧ Q x)
  : (∀x, P x) ∧ (∀x, Q x) :=
have h5 : ∀x, P x, from
    assume a,
    have h3 : P a ∧ Q a,  from h1 a,
    h3.left,
have h9 : ∀x, Q x, from
    assume b,
    have h7 : P b ∧ Q b,  from h1 b,
    h7.right,
show (∀x, P x) ∧ (∀x, Q x), from ⟨h5, h9⟩

-- 4ª demostración
example
  (h1 : ∀x, P x ∧ Q x)
  : (∀x, P x) ∧ (∀x, Q x) :=
have h5 : ∀x, P x, from
    assume a,
    (h1 a).left,
have h9 : ∀x, Q x, from
    assume b,
    (h1 b).right,
show (∀x, P x) ∧ (∀x, Q x), from ⟨h5, h9⟩

-- 5ª demostración
example
  (h1 : ∀x, P x ∧ Q x)
  : (∀x, P x) ∧ (∀x, Q x) :=
have h5 : ∀x, P x, from
    λ a, (h1 a).left,
have h9 : ∀x, Q x, from
    λ b, (h1 b).right,
show (∀x, P x) ∧ (∀x, Q x), from ⟨h5, h9⟩

-- 6ª demostración
example
  (h1 : ∀x, P x ∧ Q x)
  : (∀x, P x) ∧ (∀x, Q x) :=
have h5 : ∀x, P x, from
    λ a, (h1 a).left,
have h9 : ∀x, Q x, from
    λ b, (h1 b).right,
⟨h5, h9⟩

-- 7ª demostración
example
  (h1 : ∀x, P x ∧ Q x)
  : (∀x, P x) ∧ (∀x, Q x) :=
⟨λ a, (h1 a).left, λ b, (h1 b).right⟩

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
  { intro a,
    specialize h1 a,
    exact h1.left, },
  { intro b,
    specialize h1 b,
    exact h1.right, },
end

-- 9ª demostración
lemma aux1
  (h1 : ∀x, P x ∧ Q x)
  : (∀x, P x) ∧ (∀x, Q x) :=
-- by hint
by finish

-- ----------------------------------------------------
-- Ej. 2. Demostrar
--    ∀x P(x) ∧ ∀x Q(x) ⊢ ∀x (P(x) ∧ Q(x))
-- ----------------------------------------------------

-- 1ª demostración
example
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
assume a,
have h3 : ∀x, P x, from and.elim_left h1,
have h4 : P a,     from h3 a,
have h5 : ∀x, Q x, from and.elim_right h1,
have h6 : Q a,     from h5 a,
show P a ∧ Q a,    from and.intro h4 h6

-- 2ª demostración
example
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
assume a,
have h3 : ∀x, P x, from h1.left,
have h4 : P a,     from h3 a,
have h5 : ∀x, Q x, from h1.right,
have h6 : Q a,     from h5 a,
show P a ∧ Q a,    from ⟨h4, h6⟩

-- 3ª demostración
example
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
assume a,
have h3 : ∀x, P x, from h1.left,
have h4 : P a,     from h3 a,
have h5 : ∀x, Q x, from h1.right,
have h6 : Q a,     from h5 a,
⟨h4, h6⟩

-- 4ª demostración
example
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
assume a,
have h3 : ∀x, P x, from h1.left,
have h4 : P a,     from h3 a,
have h5 : ∀x, Q x, from h1.right,
⟨h4, h5 a⟩

-- 5ª demostración
example
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
assume a,
have h3 : ∀x, P x, from h1.left,
have h4 : P a,     from h3 a,
⟨h4, h1.right a⟩

-- 6ª demostración
example
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
assume a,
have h3 : ∀x, P x, from h1.left,
⟨h3 a, h1.right a⟩

-- 7ª demostración
example
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
assume a,
⟨h1.left a, h1.right a⟩

-- 8ª demostración
example
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
λ a, ⟨h1.left a, h1.right a⟩

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
  intro a,
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

-- ----------------------------------------------------
-- Ej. 3. Demostrar
--    ∀x (P(x) ∧ Q(x)) ↔ ∀x P(x) ∧ ∀x Q(x)
-- ----------------------------------------------------

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
