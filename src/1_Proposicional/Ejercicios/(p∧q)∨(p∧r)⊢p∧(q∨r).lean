-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    (p ∧ q) ∨ (p ∧ r) ⊢ p ∧ (q ∨ r)
-- ----------------------------------------------------

import tactic
variables (p q r : Prop)

-- 1ª demostración
example
  (H : (p ∧ q) ∨ (p ∧ r))
  : p ∧ (q ∨ r) :=
begin
  rcases H with (⟨Hp,Hq⟩ | ⟨Hp, Hr⟩),
  { exact ⟨Hp, or.inl Hq⟩, },
  { exact ⟨Hp, or.inr Hr⟩, },
end

-- 2ª demostración
example
  (H : (p ∧ q) ∨ (p ∧ r))
  : p ∧ (q ∨ r) :=
or.elim H
  ( assume Hpq : p ∧ q,
    have Hp : p,
      from and.left Hpq,
    have Hq : q,
      from and.right Hpq,
    have Hqr : q ∨ r,
      from or.inl Hq,
    show p ∧ (q ∨ r),
      from and.intro Hp Hqr)
  ( assume Hpr : p ∧ r,
    have Hp : p,
      from and.left Hpr,
    have Hr : r,
      from and.right Hpr,
    have Hqr : q ∨ r,
      from or.inr Hr,
    show p ∧ (q ∨ r),
      from and.intro Hp Hqr)

-- 3ª demostración
example
  (H : (p ∧ q) ∨ (p ∧ r))
  : p ∧ (q ∨ r) :=
or.elim H
  ( assume ⟨Hp, Hq⟩,
    have Hqr : q ∨ r,
      from or.inl Hq,
    show p ∧ (q ∨ r),
      from and.intro Hp Hqr)
  ( assume ⟨Hp, Hr⟩,
    have Hqr : q ∨ r,
      from or.inr Hr,
    show p ∧ (q ∨ r),
      from and.intro Hp Hqr)

-- 4ª demostración
example
  (H : (p ∧ q) ∨ (p ∧ r))
  : p ∧ (q ∨ r) :=
or.elim H
  (λ ⟨Hp, Hq⟩, ⟨Hp ,or.inl Hq⟩)
  (λ ⟨Hp, Hr⟩, ⟨Hp, or.inr Hr⟩)

-- 5ª demostración
example
  (H : (p ∧ q) ∨ (p ∧ r))
  : p ∧ (q ∨ r) :=
-- by library_search
and_or_distrib_left.mpr H

-- 6ª demostración
example
  (H : (p ∧ q) ∨ (p ∧ r))
  : p ∧ (q ∨ r) :=
-- by hint
by tauto

-- 7ª demostración
example
  (H : (p ∧ q) ∨ (p ∧ r))
  : p ∧ (q ∨ r) :=
by finish
