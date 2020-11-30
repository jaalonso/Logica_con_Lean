-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    p ∨ p ⊢ p
-- ----------------------------------------------------

import tactic
variable (p : Prop)

-- 1ª demostración
example
  (H : p ∨ p)
  : p :=
begin
  cases H with Hp Hp,
  { exact Hp, },
  { exact Hp, },
end

-- 2ª demostración
example
  (H : p ∨ p)
  : p :=
by cases H ; assumption

-- 3ª demostración
example
  (H : p ∨ p)
  : p :=
or.elim H
  ( assume Hp : p,
    show p,
      from Hp)
  ( assume Hp : p,
    show p,
      from Hp)

-- 4ª demostración
example
  (H : p ∨ p)
  : p :=
or.elim H
  ( assume Hp : p,
    Hp)
  ( assume Hp : p,
    Hp)

-- 5ª demostración
example
  (H : p ∨ p)
  : p :=
or.elim H
  ( λ Hp, Hp)
  ( λ Hp, Hp)

-- 6ª demostración
example
  (H : p ∨ p)
  : p :=
or.elim H id id

-- 7ª demostración
example
  (H : p ∨ p)
  : p :=
-- by library_search
(or_self p).mp H

-- 8ª demostración
example
  (H : p ∨ p)
  : p :=
-- by hint
by tauto

-- 9ª demostración
example
  (H : p ∨ p)
  : p :=
by finish
