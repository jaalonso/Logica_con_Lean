-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    (p ∨ q) ∧ (p ∨ r) ⊢ p ∨ (q ∧ r)
-- ----------------------------------------------------

import tactic
variables (p q r : Prop)

-- 1ª demostración
example
  (H : (p ∨ q) ∧ (p ∨ r))
  : p ∨ (q ∧ r) :=
begin
  cases H with Hpq Hpr,
  cases Hpq with Hp Hq,
  { left,
    exact Hp, },
  { cases Hpr with Hp Hr,
    { left,
      exact Hp, },
    { right,
      split,
      { exact Hq, },
      { exact Hr, }}},
end

-- 2ª demostración
example
  (H : (p ∨ q) ∧ (p ∨ r))
  : p ∨ (q ∧ r) :=
begin
  cases H with Hpq Hpr,
  cases Hpq with Hp Hq,
  { left,
    exact Hp, },
  { cases Hpr with Hp Hr,
    { left,
      exact Hp, },
    { right,
      exact ⟨Hq, Hr⟩, }},
end

-- 3ª demostración
example
  (H : (p ∨ q) ∧ (p ∨ r))
  : p ∨ (q ∧ r) :=
begin
  cases H with Hpq Hpr,
  cases Hpq with Hp Hq,
  { left,
    exact Hp, },
  { cases Hpr with Hp Hr,
    { left,
      exact Hp, },
    { exact or.inr ⟨Hq, Hr⟩, }},
end

-- 4ª demostración
example
  (H : (p ∨ q) ∧ (p ∨ r))
  : p ∨ (q ∧ r) :=
begin
  cases H with Hpq Hpr,
  cases Hpq with Hp Hq,
  { left,
    exact Hp, },
  { cases Hpr with Hp Hr,
    { exact or.inl Hp, },
    { exact or.inr ⟨Hq, Hr⟩, }},
end

-- 5ª demostración
example
  (H : (p ∨ q) ∧ (p ∨ r))
  : p ∨ (q ∧ r) :=
begin
  cases H with Hpq Hpr,
  cases Hpq with Hp Hq,
  { exact or.inl Hp, },
  { cases Hpr with Hp Hr,
    { exact or.inl Hp, },
    { exact or.inr ⟨Hq, Hr⟩, }},
end

-- 6ª demostración
example
  (H : (p ∨ q) ∧ (p ∨ r))
  : p ∨ (q ∧ r) :=
begin
  rcases H with ⟨Hp | Hq, Hp | Hr⟩,
  { exact or.inl Hp, },
  { exact or.inl Hp, },
  { exact or.inl Hp, },
  { exact or.inr ⟨Hq, Hr⟩, },
end

-- 7ª demostración
example
  (H : (p ∨ q) ∧ (p ∨ r))
  : p ∨ (q ∧ r) :=
-- by library_search
or_and_distrib_left.mpr H

-- 8ª demostración
example
  (H : (p ∨ q) ∧ (p ∨ r))
  : p ∨ (q ∧ r) :=
have Hpq : p ∨ q,
  from and.left H,
or.elim Hpq
  ( assume Hp : p,
    show p ∨ (q ∧ r),
      from or.inl Hp )
  ( assume Hq : q,
    have Hpr : p ∨ r,
      from and.right H,
    or.elim Hpr
      ( assume Hp : p,
        show p ∨ (q ∧ r),
          from or.inl Hp )
      ( assume Hr : r,
        have Hqr : q ∧ r,
          from and.intro Hq Hr,
        show p ∨ (q ∧ r),
          from or.inr Hqr ))

-- 9ª demostración
example
  (H : (p ∨ q) ∧ (p ∨ r))
  : p ∨ (q ∧ r) :=
or.elim (and.left H)
  or.inl
  (λ Hq, or.elim (and.right H)
           or.inl
           (λ Hr, or.inr ⟨Hq, Hr⟩))

-- 10ª demostración
example
  (H : (p ∨ q) ∧ (p ∨ r))
  : p ∨ (q ∧ r) :=
-- by hint
by tauto

-- 11ª demostración
example
  (H : (p ∨ q) ∧ (p ∨ r))
  : p ∨ (q ∧ r) :=
by finish
