-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    p ∨ q ⊢ ¬(¬p ∧ ¬q)
-- ----------------------------------------------------

import tactic
variables (p q : Prop)

-- 1ª demostración
example
  (H : p ∨ q)
  : ¬(¬p ∧ ¬q) :=
begin
  intro H1,
  cases H1 with H2 H3,
  cases H with H4 H5,
  { exact H2 H4, },
  { exact H3 H5, },
end

-- 2ª demostración
example
  (H : p ∨ q)
  : ¬(¬p ∧ ¬q) :=
begin
  rintro ⟨H2, H3⟩,
  cases H with H4 H5,
  { exact H2 H4, },
  { exact H3 H5, },
end

-- 3ª demostración
example
  (H : p ∨ q)
  : ¬(¬p ∧ ¬q) :=
λ ⟨H2, H3⟩, or.elim H (λ H4, H2 H4) (λ H5, H3 H5)

-- 4ª demostración
example
  (H : p ∨ q)
  : ¬(¬p ∧ ¬q) :=
-- by library_search
or_iff_not_and_not.mp H

-- 5ª demostración
example
  (H : p ∨ q)
  : ¬(¬p ∧ ¬q) :=
assume H3 : ¬p ∧ ¬q,
or.elim H
  ( assume Hp : p,
    show false,
      from absurd Hp (and.left H3))
  ( assume Hq : q,
    show false,
      from absurd Hq (and.right H3))

-- 6ª demostración
example
  (H : p ∨ q)
  : ¬(¬p ∧ ¬q) :=
-- by hint
by tauto

-- 7ª demostración
example
  (H : p ∨ q)
  : ¬(¬p ∧ ¬q) :=
by finish
