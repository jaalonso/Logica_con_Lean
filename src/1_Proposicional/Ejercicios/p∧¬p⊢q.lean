-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    p ∧ ¬p ⊢ q
-- ----------------------------------------------------

import tactic
variables (p q : Prop)

-- 1ª demostración
example
  (H : p ∧ ¬p)
  : q :=
begin
  exfalso,
  apply H.2,
  exact H.1,
end

-- 2ª demostración
example
  (H : p ∧ ¬p)
  : q :=
begin
  exfalso,
  exact H.2 H.1,
end

-- 3ª demostración
example
  (H : p ∧ ¬p)
  : q :=
false.elim (H.2 H.1)

-- 4ª demostración
example
  (H : p ∧ ¬p)
  : q :=
have Hp : p,
  from and.left H,
have Hnp : ¬p,
  from and.right H,
have Hf : false,
  from Hnp Hp,
show q,
  from false.elim Hf

-- 5ª demostración
example
  (H : p ∧ ¬p)
  : q :=
-- by hint
by tauto

-- 6ª demostración
example
  (H : p ∧ ¬p)
  : q :=
by finish
