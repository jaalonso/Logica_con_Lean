-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    (p ∨ q) ∨ r ⊢ p ∨ (q ∨ r)
-- ----------------------------------------------------

import tactic
variables (p q r : Prop)

-- 1ª demostración
example
  (H : (p ∨ q) ∨ r)
  : p ∨ (q ∨ r) :=
begin
  rcases H with ((Hp | Hq) | Hr),
  { left,
    exact Hp, },
  { right,
    left,
    exact Hq, },
  { right,
    right,
    exact Hr, },
end

-- 2ª demostración
example
  (H : (p ∨ q) ∨ r)
  : p ∨ (q ∨ r) :=
or.elim H
  ( assume Hpq : p ∨ q,
    show p ∨ q ∨ r, from
      or.elim Hpq
        ( assume Hp : p,
          show p ∨ (q ∨ r),
            from or.inl Hp)
        ( assume Hq : q,
          have Hqr: q ∨ r,
            from or.inl Hq,
          show p ∨ (q ∨ r),
            from or.inr Hqr))
  ( assume Hr : r,
    have Hqr: q ∨ r,
      from or.inr Hr,
    show p ∨ (q ∨ r),
      from or.inr Hqr)

-- 3ª demostración
example
  (H : (p ∨ q) ∨ r)
  : p ∨ (q ∨ r) :=
or.elim H
  ( λ Hpq, or.elim Hpq or.inl (λ Hq, or.inr (or.inl Hq)))
  ( λ Hr, or.inr (or.inr Hr))

-- 4ª demostración
example
  (H : (p ∨ q) ∨ r)
  : p ∨ (q ∨ r) :=
-- by library_search
or.assoc.mp H

-- 5ª demostración
example
  (H : (p ∨ q) ∨ r)
  : p ∨ (q ∨ r) :=
-- by hint
by tauto

-- 6ª demostración
example
  (H : (p ∨ q) ∨ r)
  : p ∨ (q ∨ r) :=
by finish
