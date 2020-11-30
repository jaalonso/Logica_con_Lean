-- ----------------------------------------------------
-- Ejercicio . Demostrar
--    ¬¬p ⊢ p
-- ----------------------------------------------------

import tactic
variable (p : Prop)

open_locale classical

-- 1ª demostración
example
  (h1 : ¬¬p)
  : p :=
by_contra
  ( assume h2 : ¬p,
    show false,
      from h1 h2 )

-- 2ª demostración
example
  (h1 : ¬¬p)
  : p :=
by_contra
  ( assume h2 : ¬p,
    h1 h2 )

-- 3ª demostración
example
  (h1 : ¬¬p)
  : p :=
by_contra (λ h2, h1 h2)

-- 4ª demostración
example
  (h1 : ¬¬p)
  : p :=
-- by library_search
not_not.mp h1

-- 5ª demostración
example
  (h1 : ¬¬p)
  : p :=
begin
  by_contradiction h2,
  exact h1 h2,
end

-- 6ª demostración
example
  (h1 : ¬¬p)
  : p :=
-- by hint
by tauto

-- 7ª demostración
lemma aux
  (h1 : ¬¬p)
  : p :=
by finish
