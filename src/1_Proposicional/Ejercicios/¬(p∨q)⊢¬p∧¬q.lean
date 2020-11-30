-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    ¬(p ∨ q) ⊢ ¬p ∧ ¬q
-- ----------------------------------------------------

import tactic
variables (p q : Prop)

-- 1ª demostración
example
  (H : ¬(p ∨ q))
  : ¬p ∧ ¬q :=
begin
  split,
  { intro Hp,
    apply H,
    exact or.inl Hp, },
  { intro Hq,
    apply H,
    exact or.inr Hq, },
end

-- 2ª demostración
example
  (H : ¬(p ∨ q))
  : ¬p ∧ ¬q :=
begin
  split,
  { intro Hp,
    exact H (or.inl Hp), },
  { intro Hq,
    exact H (or.inr Hq), },
end

-- 3ª demostración
example
  (H : ¬(p ∨ q))
  : ¬p ∧ ¬q :=
⟨ λ Hp, H (or.inl Hp),
  λ Hq, H (or.inr Hq)⟩

-- 4ª demostración
example
  (H : ¬(p ∨ q))
  : ¬p ∧ ¬q :=
-- by library_search
not_or_distrib.mp H

-- 5ª demostración
example
  (H : ¬(p ∨ q))
  : ¬p ∧ ¬q :=
have H1 : ¬p, from
  assume Hp : p,
  have H2: p ∨ q,
    from or.inl Hp,
  show false,
    from absurd H2 H,
have H3 : ¬q, from
  assume Hq : q,
  have H4: p ∨ q,
    from or.inr Hq,
  show false,
    from absurd H4 H,
show ¬p ∧ ¬q,
  from and.intro H1 H3

-- 6ª demostración
example
  (H : ¬(p ∨ q))
  : ¬p ∧ ¬q :=
-- by hint
by tauto

-- 7ª demostración
example
  (H : ¬(p ∨ q))
  : ¬p ∧ ¬q :=
by finish
