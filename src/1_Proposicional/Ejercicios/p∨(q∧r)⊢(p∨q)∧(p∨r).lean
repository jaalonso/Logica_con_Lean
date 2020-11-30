-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    p ∨ (q ∧ r) ⊢ (p ∨ q) ∧ (p ∨ r)
-- ----------------------------------------------------

import tactic
variables (p q r : Prop)

-- 1ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
begin
  cases H with Hp Hqr,
  { split,
    { left,
      exact Hp, },
    { left,
      exact Hp, }},
  { split,
    { right,
      exact Hqr.left, },
    { right,
      exact Hqr.right, }},
end

-- 2ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
begin
  cases H with Hp Hqr,
  { split,
    { exact or.inl Hp, },
    { exact or.inl Hp, }},
  { split,
    { exact or.inr Hqr.left, },
    { exact or.inr Hqr.right, }},
end

-- 3ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
begin
  cases H with Hp Hqr,
  { exact ⟨or.inl Hp, or.inl Hp⟩, },
  { exact ⟨or.inr Hqr.left, or.inr Hqr.right⟩, },
end

-- 4ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
or.elim H
  (λ Hp, ⟨or.inl Hp, or.inl Hp⟩)
  (λ Hqr, ⟨or.inr Hqr.1, or.inr Hqr.2⟩)

-- 5ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
or.elim H
  (λ h, ⟨or.inl h,   or.inl h⟩)
  (λ h, ⟨or.inr h.1, or.inr h.2⟩)

-- 6ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
or.elim H
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    have Hpr : p ∨ r,
      from or.inl Hp,
    show (p ∨ q) ∧ (p ∨ r),
      from and.intro Hpq Hpr)
  ( assume Hqr : q ∧ r,
    have Hq : q,
      from and.left Hqr,
    have Hr : r,
      from and.right Hqr,
    have Hpq : p ∨ q,
      from or.inr Hq,
    have Hpr : p ∨ r,
      from or.inr Hr,
    show (p ∨ q) ∧ (p ∨ r),
      from and.intro Hpq Hpr)

-- 7ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
or.elim H
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    have Hpr : p ∨ r,
      from or.inl Hp,
    show (p ∨ q) ∧ (p ∨ r),
      from and.intro Hpq Hpr)
  ( assume Hqr : q ∧ r,
    have Hq : q,
      from and.left Hqr,
    have Hr : r,
      from and.right Hqr,
    have Hpq : p ∨ q,
      from or.inr Hq,
    have Hpr : p ∨ r,
      from or.inr Hr,
    and.intro Hpq Hpr)

-- 8ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
or.elim H
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    have Hpr : p ∨ r,
      from or.inl Hp,
    show (p ∨ q) ∧ (p ∨ r),
      from and.intro Hpq Hpr)
  ( assume Hqr : q ∧ r,
    have Hq : q,
      from and.left Hqr,
    have Hr : r,
      from and.right Hqr,
    and.intro (or.inr Hq) (or.inr Hr))

-- 9ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
or.elim H
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    have Hpr : p ∨ r,
      from or.inl Hp,
    show (p ∨ q) ∧ (p ∨ r),
      from and.intro Hpq Hpr)
  ( assume Hqr : q ∧ r,
    and.intro (or.inr (and.left Hqr)) (or.inr (and.right Hqr)))

-- 10ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
or.elim H
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    have Hpr : p ∨ r,
      from or.inl Hp,
    show (p ∨ q) ∧ (p ∨ r),
      from and.intro Hpq Hpr)
  ( assume Hqr : q ∧ r,
    and.intro (or.inr Hqr.1) (or.inr Hqr.2))

-- 11ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
or.elim H
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    have Hpr : p ∨ r,
      from or.inl Hp,
    show (p ∨ q) ∧ (p ∨ r),
      from and.intro Hpq Hpr)
  ( assume Hqr : q ∧ r,
    ⟨or.inr Hqr.1, or.inr Hqr.2⟩)

-- 12ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
or.elim H
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    have Hpr : p ∨ r,
      from or.inl Hp,
    show (p ∨ q) ∧ (p ∨ r),
      from and.intro Hpq Hpr)
  ( λ Hqr, ⟨or.inr Hqr.1, or.inr Hqr.2⟩)

-- 13ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
or.elim H
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    have Hpr : p ∨ r,
      from or.inl Hp,
    and.intro Hpq Hpr)
  ( λ Hqr, ⟨or.inr Hqr.1, or.inr Hqr.2⟩)

-- 14ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
or.elim H
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    have Hpr : p ∨ r,
      from or.inl Hp,
    ⟨Hpq, Hpr⟩)
  ( λ Hqr, ⟨or.inr Hqr.1, or.inr Hqr.2⟩)

-- 15ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
or.elim H
  ( assume Hp : p,
    ⟨or.inl Hp, or.inl Hp⟩)
  ( λ Hqr, ⟨or.inr Hqr.1, or.inr Hqr.2⟩)

-- 16ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
or.elim H
  ( λ Hp, ⟨or.inl Hp, or.inl Hp⟩)
  ( λ Hqr, ⟨or.inr Hqr.1, or.inr Hqr.2⟩)

-- 17ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
-- by library_search
or_and_distrib_left.mp H

-- 18ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
-- by hint
by tauto

-- 19ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
by finish
