-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    p → q ⊢ ¬q → ¬p
-- ----------------------------------------------------

import tactic
variables (p q : Prop)

-- 1ª demostración
example
  (H : p → q)
  : ¬q → ¬p :=
begin
  intro Hnq,
  intro Hp,
  apply Hnq,
  exact H Hp,
end

-- 2ª demostración
example
  (H : p → q)
  : ¬q → ¬p :=
begin
  intro Hnq,
  intro Hp,
  exact Hnq (H Hp),
end

-- 3ª demostración
example
  (H : p → q)
  : ¬q → ¬p :=
begin
  intros Hnq Hp,
  exact Hnq (H Hp),
end

-- 4ª demostración
example
  (H : p → q)
  : ¬q → ¬p :=
λ Hnq Hp, Hnq (H Hp)

-- 5ª demostración
example
  (H : p → q)
  : ¬q → ¬p :=
-- by library_search
mt H

-- 6ª demostración
example
  (H : p → q)
  : ¬q → ¬p :=
assume Hnq : ¬q,
assume Hp : p,
have Hq : q,
  from H Hp,
show false,
  from Hnq Hq

-- 7ª demostración
example
  (H : p → q)
  : ¬q → ¬p :=
assume Hnq : ¬q,
assume Hp : p,
have Hq : q,
  from H Hp,
Hnq Hq

-- 8ª demostración
example
  (H : p → q)
  : ¬q → ¬p :=
assume Hnq : ¬q,
assume Hp : p,
Hnq (H Hp)

-- 9ª demostración
example
  (H : p → q)
  : ¬q → ¬p :=
assume Hnq : ¬q,
λ Hp, Hnq (H Hp)

-- 10ª demostración
example
  (H : p → q)
  : ¬q → ¬p :=
λ Hnq Hp, Hnq (H Hp)

-- 11ª demostración
example
  (H : p → q)
  : ¬q → ¬p :=
-- by hint
by tauto

-- 12ª demostración
example
  (H : p → q)
  : ¬q → ¬p :=
by finish
