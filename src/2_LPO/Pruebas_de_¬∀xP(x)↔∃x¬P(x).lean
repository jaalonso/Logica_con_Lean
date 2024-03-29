-- Pruebas de ¬∀x P(x) ↔ ∃x ¬P(x)
-- ==============================

import tactic

variable {U : Type}
variable {P : U -> Prop}

-- ----------------------------------------------------
-- Ej. 1. Demostrar que
--    ¬∀x P(x) ⊢ ∃x ¬P(x)
-- ----------------------------------------------------

-- 1ª demostración
example
  (h1 : ¬∀x, P x)
  : ∃x, ¬P x :=
by_contra
  ( assume h2 : ¬∃x, ¬P x,
    have h8 : ∀x, P x, from
      ( assume a,
        show P a, from
          by_contra
            ( assume h4 : ¬P a,
              have h5 : ∃x, ¬P x,
                from exists.intro a h4,
              show false, from h2 h5 )),
    show false, from h1 h8)

-- 2ª demostración
example
  (h1 : ¬∀x, P x)
  : ∃x, ¬P x :=
by_contra
  ( assume h2 : ¬∃x, ¬P x,
    have h8 : ∀x, P x, from
      ( assume a,
        show P a, from
          by_contra
            ( assume h4 : ¬P a,
              have h5 : ∃x, ¬P x,
                from exists.intro a h4,
              show false, from h2 h5 )),
    h1 h8)

-- 3ª demostración
example
  (h1 : ¬∀x, P x)
  : ∃x, ¬P x :=
by_contra
  ( assume h2 : ¬∃x, ¬P x,
    have h8 : ∀x, P x, from
      ( assume a,
        show P a, from
          by_contra
            ( assume h4 : ¬P a,
              have h5 : ∃x, ¬P x,
                from exists.intro a h4,
              h2 h5 )),
    h1 h8)

-- 4ª demostración
example
  (h1 : ¬∀x, P x)
  : ∃x, ¬P x :=
by_contra
  ( assume h2 : ¬∃x, ¬P x,
    have h8 : ∀x, P x, from
      ( assume a,
        show P a, from
          by_contra
            ( assume h4 : ¬P a,
              have h5 : ∃x, ¬P x, from ⟨a, h4⟩,
              h2 h5 )),
    h1 h8)

-- 5ª demostración
example
  (h1 : ¬∀x, P x)
  : ∃x, ¬P x :=
by_contra
  ( assume h2 : ¬∃x, ¬P x,
    have h8 : ∀x, P x, from
      ( assume a,
        show P a, from
          by_contra
            ( assume h4 : ¬P a,
              h2 ⟨a, h4⟩ )),
    h1 h8)

-- 6ª demostración
example
  (h1 : ¬∀x, P x)
  : ∃x, ¬P x :=
by_contra
  ( assume h2 : ¬∃x, ¬P x,
    have h8 : ∀x, P x, from
      ( assume a,
        show P a, from
          by_contra (λ h4, h2 ⟨a, h4⟩)),
    h1 h8)

-- 7ª demostración
example
  (h1 : ¬∀x, P x)
  : ∃x, ¬P x :=
by_contra
  ( assume h2 : ¬∃x, ¬P x,
    have h8 : ∀x, P x, from
      ( assume a,
        by_contra (λ h4, h2 ⟨a, h4⟩)),
    h1 h8)

-- 8ª demostración
example
  (h1 : ¬∀x, P x)
  : ∃x, ¬P x :=
by_contra
  ( assume h2 : ¬∃x, ¬P x,
    have h8 : ∀x, P x, from
      (λ a, by_contra (λ h4, h2 ⟨a, h4⟩)),
    h1 h8)

-- 9ª demostración
example
  (h1 : ¬∀x, P x)
  : ∃x, ¬P x :=
by_contra
  ( assume h2 : ¬∃x, ¬P x,
    h1 (λ a, by_contra (λ h4, h2 ⟨a, h4⟩)))

-- 10ª demostración
example
  (h1 : ¬∀x, P x)
  : ∃x, ¬P x :=
by_contra (λ h2, h1 (λ a, by_contra (λ h4, h2 ⟨a, h4⟩)))

-- 11ª demostración
example
  (h1 : ¬∀x, P x)
  : ∃x, ¬P x :=
-- by library_search
not_forall.mp h1

-- 12ª demostración
lemma aux1
  (h1 : ¬∀x, P x)
  : ∃x, ¬P x :=
-- by hint
by finish

-- ----------------------------------------------------
-- Ej. 2. Demostrar que
--    ∃x ¬P(x) ⊢ ¬∀x P(x)
-- ----------------------------------------------------

-- 1ª demostración
example
  (h1 : ∃x, ¬P x)
  : ¬∀x, P x :=
assume h2 : ∀x, P x,
exists.elim h1
  ( assume a (h3 : ¬P a),
    have h4 : P a, from h2 a,
    show false, from h3 h4)

-- 2ª demostración
example
  (h1 : ∃x, ¬P x)
  : ¬∀x, P x :=
assume h2 : ∀x, P x,
exists.elim h1
  ( assume a (h3 : ¬P a),
    have h4 : P a, from h2 a,
    h3 h4)

-- 3ª demostración
example
  (h1 : ∃x, ¬P x)
  : ¬∀x, P x :=
assume h2 : ∀x, P x,
exists.elim h1
  ( assume a (h3 : ¬P a),
    h3 (h2 a))

-- 4ª demostración
example
  (h1 : ∃x, ¬P x)
  : ¬∀x, P x :=
assume h2 : ∀x, P x,
exists.elim h1
  (λ a h3, h3 (h2 a))

-- 5ª demostración
example
  (h1 : ∃x, ¬P x)
  : ¬∀x, P x :=
λ h2, exists.elim h1 (λ a h3, h3 (h2 a))

-- 6ª demostración
example
  (h1 : ∃x, ¬P x)
  : ¬∀x, P x :=
-- by library_search
not_forall.mpr h1

-- 7ª demostración
example
  (h1 : ∃x, ¬P x)
  : ¬∀x, P x :=
assume h2 : ∀x, P x,
match h1 with ⟨a, (h3 : ¬P a)⟩ :=
  ( have h4 : P a, from h2 a,
    show false,     from h3 h4)
end

-- 8ª demostración
example
  (h1 : ∃x, ¬P x)
  : ¬∀x, P x :=
begin
  intro h2,
  cases h1 with a h3,
  apply h3,
  apply h2,
end

example
  (h1 : ∃x, ¬P x)
  : ¬∀x, P x :=
begin
  intro h2,
  obtain ⟨a, h3⟩ := h1,
  apply h3,
  apply h2,
end

-- 9ª demostración
example
  (h1 : ∃x, ¬P x)
  : ¬∀x, P x :=
-- by hint
by tauto

-- 10ª demostración
lemma aux2
  (h1 : ∃x, ¬P x)
  : ¬∀x, P x :=
by finish

#print axioms aux2

-- ----------------------------------------------------
-- Ej. 3. Demostrar que
--    ¬∀x P(x) ↔ ∃x ¬P(x)
-- ----------------------------------------------------

-- 1ª demostración
example :
  (¬∀x, P x) ↔ (∃x, ¬P x) :=
iff.intro
  ( assume h1 : ¬∀x, P x,
    show ∃x, ¬P x, from aux1 h1)
  ( assume h2 : ∃x, ¬P x,
    show ¬∀x, P x, from aux2 h2)

-- 2ª demostración
example :
  (¬∀x, P x) ↔ (∃x, ¬P x) :=
iff.intro aux1 aux2

-- 3ª demostración
example :
  (¬∀x, P x) ↔ (∃x, ¬P x) :=
-- by library_search
not_forall

-- 4ª demostración
example :
  (¬∀x, P x) ↔ (∃x, ¬P x) :=
begin
  split,
  { exact aux1, },
  { exact aux2, },
end

-- 5ª demostración
example :
  (¬∀x, P x) ↔ (∃x, ¬P x) :=
-- by hint
by finish
