-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    p ∨ (q ∨ r) ⊢ (p ∨ q) ∨ r
-- ----------------------------------------------------

import tactic
variables (p q r : Prop)

-- 1ª demostración
example
  (H : p ∨ (q ∨ r))
  : (p ∨ q) ∨ r :=
begin
  cases H with Hp Hqr,
  { left,
    left,
    exact Hp, },
  { cases Hqr with Hq Hr,
    { left,
      right,
      exact Hq, },
    { right,
      exact Hr, }},
end

-- 2ª demostración
example
  (H : p ∨ (q ∨ r))
  : (p ∨ q) ∨ r :=
or.elim H
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    show (p ∨ q) ∨ r,
      from or.inl Hpq)
  ( assume Hqr : q ∨ r,
    show (p ∨ q) ∨ r, from
      or.elim Hqr
        ( assume Hq : q,
          have Hpq : p ∨ q,
            from or.inr Hq,
          show (p ∨ q) ∨ r,
            from or.inl Hpq)
        ( assume Hr : r,
          show (p ∨ q) ∨ r,
            from or.inr Hr))

-- 3ª demostración
example
  (H : p ∨ (q ∨ r))
  : (p ∨ q) ∨ r :=
or.elim H
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    show (p ∨ q) ∨ r,
      from or.inl Hpq)
  ( assume Hqr : q ∨ r,
    show (p ∨ q) ∨ r, from
      or.elim Hqr
        ( assume Hq : q,
          have Hpq : p ∨ q,
            from or.inr Hq,
          or.inl Hpq)
        ( assume Hr : r,
          or.inr Hr))

-- 4ª demostración
example
  (H : p ∨ (q ∨ r))
  : (p ∨ q) ∨ r :=
or.elim H
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    show (p ∨ q) ∨ r,
      from or.inl Hpq)
  ( assume Hqr : q ∨ r,
    show (p ∨ q) ∨ r, from
      or.elim Hqr
        ( assume Hq : q,
          have Hpq : p ∨ q,
            from or.inr Hq,
          or.inl Hpq)
        or.inr)

-- 5ª demostración
example
  (H : p ∨ (q ∨ r))
  : (p ∨ q) ∨ r :=
or.elim H
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    show (p ∨ q) ∨ r,
      from or.inl Hpq)
  ( assume Hqr : q ∨ r,
    show (p ∨ q) ∨ r, from
      or.elim Hqr
        ( λ Hq, or.inl (or.inr Hq))
        or.inr)

-- 6ª demostración
example
  (H : p ∨ (q ∨ r))
  : (p ∨ q) ∨ r :=
or.elim H
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    show (p ∨ q) ∨ r,
      from or.inl Hpq)
  ( λ Hqr, or.elim Hqr ( λ Hq, or.inl (or.inr Hq)) or.inr)

-- 7ª demostración
example
  (H : p ∨ (q ∨ r))
  : (p ∨ q) ∨ r :=
or.elim H
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    or.inl Hpq)
  (λ Hqr, or.elim Hqr ( λ Hq, or.inl (or.inr Hq)) or.inr)

-- 8ª demostración
example
  (H : p ∨ (q ∨ r))
  : (p ∨ q) ∨ r :=
or.elim H
  ( assume Hp : p,
    or.inl (or.inl Hp))
  (λ Hqr, or.elim Hqr ( λ Hq, or.inl (or.inr Hq)) or.inr)

-- 9ª demostración
example
  (H : p ∨ (q ∨ r))
  : (p ∨ q) ∨ r :=
or.elim H
  (λ Hp, or.inl (or.inl Hp))
  (λ Hqr, or.elim Hqr ( λ Hq, or.inl (or.inr Hq)) or.inr)

-- 10ª demostración
example
  (H : p ∨ (q ∨ r))
  : (p ∨ q) ∨ r :=
-- by library_search
or.assoc.mpr H

-- 11ª demostración
example
  (H : p ∨ (q ∨ r))
  : (p ∨ q) ∨ r :=
-- by hint
by tauto

-- 12ª demostración
example
  (H : p ∨ (q ∨ r))
  : (p ∨ q) ∨ r :=
by finish
