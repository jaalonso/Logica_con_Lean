-- Pruebas de P, ¬¬(Q ∧ R) ⊢ ¬¬P ∧ R
-- =================================

-- ----------------------------------------------------
-- Ej. 1. (p. 5) Demostrar
--    P, ¬¬(Q ∧ R) ⊢ ¬¬P ∧ R
-- ----------------------------------------------------

import tactic

variables (P Q R : Prop)

open_locale classical

-- 1ª demostración
example
  (h1 : P)
  (h2 : ¬¬(Q ∧ R))
  : ¬¬P ∧ R :=
have h3 : ¬¬P,   from not_not_intro h1,
have h4 : Q ∧ R, from not_not.mp h2,
have h5 : R,     from and.elim_right h4,
show ¬¬P ∧ R,    from and.intro h3 h5

-- 2ª demostración
example
  (h1 : P)
  (h2 : ¬¬(Q ∧ R))
  : ¬¬P ∧ R :=
have h3 : ¬¬P,   from not_not_intro h1,
have h4 : Q ∧ R, from not_not.mp h2,
have h5 : R,     from and.elim_right h4,
and.intro h3 h5

-- 3ª demostración
example
  (h1 : P)
  (h2 : ¬¬(Q ∧ R))
  : ¬¬P ∧ R :=
have h3 : ¬¬P,   from not_not_intro h1,
have h4 : Q ∧ R, from not_not.mp h2,
have h5 : R,     from h4.2,
and.intro h3 h5

-- 5ª demostración
example
  (h1 : P)
  (h2 : ¬¬(Q ∧ R))
  : ¬¬P ∧ R :=
and.intro (not_not_intro h1) (not_not.mp h2).2

-- 6ª demostración
example
  (h1 : P)
  (h2 : ¬¬(Q ∧ R))
  : ¬¬P ∧ R :=
begin
  split,
  { exact not_not_intro h1, },
  { push_neg at h2,
    exact h2.2, },
end

-- 7ª demostración
example
  (h1 : P)
  (h2 : ¬¬(Q ∧ R))
  : ¬¬P ∧ R :=
-- by hint
by tauto

-- 8ª demostración
lemma aux
  (h1 : P)
  (h2 : ¬¬(Q ∧ R))
  : ¬¬P ∧ R :=
by finish

#print axioms aux
