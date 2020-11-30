-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    ¬(¬p ∨ ¬q) ⊢ p ∧ q
-- ----------------------------------------------------

import tactic
variables (p q : Prop)

open_locale classical

-- 1ª demostración
example
  (H : ¬(¬p ∨ ¬q))
  : p ∧ q :=
begin
  split,
  { by_contra Hnp,
    apply H,
    exact or.inl Hnp, },
  { by_contra Hnq,
    apply H,
    exact or.inr Hnq, },
end

-- 2ª demostración
example
  (H : ¬(¬p ∨ ¬q))
  : p ∧ q :=
begin
  split,
  { by_contra Hnp,
    exact H (or.inl Hnp), },
  { by_contra Hnq,
    exact H (or.inr Hnq), },
end

-- 3ª demostración
example
  (H : ¬(¬p ∨ ¬q))
  : p ∧ q :=
begin
  split,
  { exact by_contra (λ Hnp, H (or.inl Hnp)), },
  { exact by_contra (λ Hnq, H (or.inr Hnq)), },
end

-- 4ª demostración
example
  (H : ¬(¬p ∨ ¬q))
  : p ∧ q :=
⟨by_contra (λ Hnp, H (or.inl Hnp)),
 by_contra (λ Hnq, H (or.inr Hnq))⟩

-- 5ª demostración
example
  (H : ¬(¬p ∨ ¬q))
  : p ∧ q :=
-- by library_search
and_iff_not_or_not.mpr H

-- 6ª demostración
example
  (H : ¬(¬p ∨ ¬q))
  : p ∧ q :=
and.intro
  ( show p, from by_contradiction
      ( assume Hnp : ¬p,
        have H' : ¬p ∨ ¬ q,
          from or.inl Hnp,
        show false,
          from H H'))
  ( show q, from by_contradiction
      ( assume Hnq : ¬q,
        have H' : ¬p ∨ ¬ q,
          from or.inr Hnq,
        show false,
          from H H'))

-- 7ª demostración
example
  (H : ¬(¬p ∨ ¬q))
  : p ∧ q :=
-- by hint
by tauto

-- 8ª demostración
example
  (H : ¬(¬p ∨ ¬q))
  : p ∧ q :=
by finish
