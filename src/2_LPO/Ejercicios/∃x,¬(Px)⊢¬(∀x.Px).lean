-- ∃ x, ¬(P x) ⊢ ¬(∀ x, P x)
-- =========================

-- ----------------------------------------------------
-- Ejercicio 2. Demostrar
--    ∃ x, ¬(P x) ⊢ ¬(∀ x, P x)
-- ----------------------------------------------------

import tactic

variable {U : Type}
variable {P : U -> Prop}

-- 1ª demostración
example
  (h: ∃ x, ¬(P x))
  : ¬(∀ x, P x) :=
begin
  intro h1,
  cases h with a h2,
  apply h2,
  exact h1 a,
end

-- 2ª demostración
example
  (h: ∃ x, ¬(P x))
  : ¬(∀ x, P x) :=
begin
  intro h1,
  cases h with a h2,
  exact h2 (h1 a),
end

-- 3ª demostración
example :
  (∃ x, ¬(P x)) → ¬(∀ x, P x) :=
begin
  rintro ⟨a, h2⟩ h1,
  exact h2 (h1 a),
end

-- 4ª demostración
example :
  (∃ x, ¬(P x)) → ¬(∀ x, P x) :=
λ ⟨a, h2⟩ h1, h2 (h1 a)

-- 5ª demostración
example
  (h: ∃ x, ¬(P x))
  : ¬(∀ x, P x) :=
assume h1 : ∀ x, P x,
exists.elim h
  ( assume a,
    assume h2 : ¬(P a),
    have h3 : P a,
      from h1 a,
    show false,
      from h2 h3 )

-- 6ª demostración
example
  (h: ∃ x, ¬(P x))
  : ¬(∀ x, P x) :=
assume h1 : ∀ x, P x,
exists.elim h
  ( assume a,
    assume h2 : ¬(P a),
    h2 (h1 a) )

-- 7ª demostración
example
  (h: ∃ x, ¬(P x))
  : ¬(∀ x, P x) :=
assume h1 : ∀ x, P x,
exists.elim h
  (λ a h2, h2 (h1 a) )

-- 8ª demostración
example
  (h: ∃ x, ¬(P x))
  : ¬(∀ x, P x) :=
λ h1, exists.elim h (λ a h2, h2 (h1 a) )

-- 9ª demostración
example
  (h: ∃ x, ¬(P x))
  : ¬(∀ x, P x) :=
-- by library_search
not_forall.mpr h

-- 10ª demostración
example
  (h: ∃ x, ¬(P x))
  : ¬(∀ x, P x) :=
-- by hint
by tauto

-- 11ª demostración
example
  (h: ∃ x, ¬(P x))
  : ¬(∀ x, P x) :=
by finish
