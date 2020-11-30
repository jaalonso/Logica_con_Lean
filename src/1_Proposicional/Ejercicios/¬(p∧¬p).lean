-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    ⊢ ¬(p ∧ ¬p)
-- ----------------------------------------------------

import tactic
variables (p q : Prop)

-- 1ª demostración
example :
  ¬(p ∧ ¬p) :=
begin
  intro H,
  apply H.right,
  exact H.left,
end

-- 2ª demostración
example :
  ¬(p ∧ ¬p) :=
begin
  intro H,
  exact H.right (H.left),
end

-- 3ª demostración
example :
  ¬(p ∧ ¬p) :=
λ H, H.right (H.left)

-- 4ª demostración
example :
  ¬(p ∧ ¬p) :=
begin
  rintro ⟨H1, H2⟩,
  exact H2 H1,
end

-- 5ª demostración
example :
  ¬(p ∧ ¬p) :=
λ ⟨H1, H2⟩, H2 H1

-- 6ª demostración
example :
  ¬(p ∧ ¬p) :=
-- by suggest
(and_not_self p).mp

-- 7ª demostración
example :
  ¬(p ∧ ¬p) :=
assume H : p ∧ ¬p,
have H1 : p,
  from and.left H,
have H2 : ¬p,
  from and.right H,
show false,
  from H2 H1

-- 8ª demostración
example :
  ¬(p ∧ ¬p) :=
-- by hint
by tauto

-- 9ª demostración
example :
  ¬(p ∧ ¬p) :=
by finish

-- 10ª demostración
example :
  ¬(p ∧ ¬p) :=
by simp
