-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    p ∨ q, ¬q ⊢ p
-- ----------------------------------------------------

import tactic
variables (p q : Prop)

-- 1ª demostración
example
  (Hpq : p ∨ q)
  (Hnq : ¬q)
  : p :=
begin
  cases Hpq with Hp Hq,
  { exact Hp, },
  { exact absurd Hq Hnq, },
end

-- 2ª demostración
example
  (Hpq : p ∨ q)
  (Hnq : ¬q)
  : p :=
-- by library_search
or.resolve_right Hpq Hnq

-- 3ª demostración
example
  (Hpq : p ∨ q)
  (Hnq : ¬q)
  : p :=
or.elim Hpq
  ( assume Hp : p,
    show p,
      from Hp)
  ( assume Hq : q,
    show p,
      from absurd Hq Hnq)

-- 4ª demostración
example
  (Hpq : p ∨ q)
  (Hnq : ¬q)
  : p :=
or.elim Hpq
  ( assume Hp : p,
    show p,
      from Hp)
  ( assume Hq : q,
    absurd Hq Hnq)

-- 5ª demostración
example
  (Hpq : p ∨ q)
  (Hnq : ¬q)
  : p :=
or.elim Hpq
  ( assume Hp : p,
    show p,
      from Hp)
  ( λ Hq, absurd Hq Hnq)

-- 6ª demostración
example
  (Hpq : p ∨ q)
  (Hnq : ¬q)
  : p :=
or.elim Hpq
  ( assume Hp : p,
    Hp)
  ( λ Hq, absurd Hq Hnq)

-- 7ª demostración
example
  (Hpq : p ∨ q)
  (Hnq : ¬q)
  : p :=
or.elim Hpq id (λ Hq, absurd Hq Hnq)

-- 8ª demostración
example
  (Hpq : p ∨ q)
  (Hnq : ¬q)
  : p :=
-- by hint
by tauto

-- 9ª demostración
example
  (Hpq : p ∨ q)
  (Hnq : ¬q)
  : p :=
by finish
