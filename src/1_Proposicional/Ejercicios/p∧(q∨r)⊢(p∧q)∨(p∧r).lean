-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    p ∧ (q ∨ r) ⊢ (p ∧ q) ∨ (p ∧ r)
-- ----------------------------------------------------

import tactic
variables (p q r : Prop)

-- 1ª demostración
example
  (H : p ∧ (q ∨ r))
  : (p ∧ q) ∨ (p ∧ r) :=
begin
  cases H with Hp Hqr,
  cases Hqr with Hq Hr,
  { left,
    split,
    { exact Hp, },
    { exact Hq, }},
  { right,
    split,
    { exact Hp, },
    { exact Hr, }},
end

-- 2ª demostración
example
  (H : p ∧ (q ∨ r))
  : (p ∧ q) ∨ (p ∧ r) :=
begin
  cases H with Hp Hqr,
  cases Hqr with Hq Hr,
  { left,
    exact ⟨Hp, Hq⟩, },
  { right,
    exact ⟨Hp, Hr⟩, },
end

-- 3ª demostración
example
  (H : p ∧ (q ∨ r))
  : (p ∧ q) ∨ (p ∧ r) :=
have Hp : p,
  from and.left H,
have Hqr : q ∨ r,
  from and.right H,
or.elim Hqr
  ( assume Hq : q,
    have Hpq : p ∧ q,
      from and.intro Hp Hq,
    show (p ∧ q) ∨ (p ∧ r),
      from or.inl Hpq)
  ( assume Hr : r,
    have Hpr : p ∧ r,
      from and.intro Hp Hr,
    show (p ∧ q) ∨ (p ∧ r),
      from or.inr Hpr)

-- 4ª demostración
example
  (H : p ∧ (q ∨ r))
  : (p ∧ q) ∨ (p ∧ r) :=
or.elim H.2
  (λ Hq, or.inl ⟨H.1, Hq⟩)
  (λ Hr, or.inr ⟨H.1, Hr⟩)

-- 5ª demostración
example
  (H : p ∧ (q ∨ r))
  : (p ∧ q) ∨ (p ∧ r) :=
-- by library_search
and_or_distrib_left.mp H

-- 6ª demostración
example
  (H : p ∧ (q ∨ r))
  : (p ∧ q) ∨ (p ∧ r) :=
-- by hint
by finish
