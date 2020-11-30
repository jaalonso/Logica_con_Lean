-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    ⊢ ((p → q) → p) → p
-- ----------------------------------------------------

import tactic
variables (p q : Prop)

open_locale classical

-- 1ª demostración
example :
  ((p → q) → p) → p :=
begin
  intro h1,
  by_cases h2 : p → q,
  { exact h1 h2, },
  { by_contra h3,
    apply h2,
    intro h4,
    exfalso,
    exact h3 h4, },
end

-- 2ª demostración
example :
  ((p → q) → p) → p :=
begin
  by_cases hp : p,
  { intro h1,
    exact hp, },
  { intro h2,
    exact h2 hp.elim, },
end

-- 3ª demostración
example :
  ((p → q) → p) → p :=
if hp : p then λ h, hp else λ h, h hp.elim

-- 4ª demostración
example :
  ((p → q) → p) → p :=
-- by library_search
peirce p q

-- 5ª demostración
example :
  ((p → q) → p) → p :=
assume h1 : (p → q) → p,
show p, from
  by_contradiction
    ( assume h2 : ¬p,
      have h3 : ¬(p → q),
        by exact mt h1 h2,
      have h4 : p → q, from
        assume h5 : p,
        show q,
          from not.elim h2 h5,
      show false,
        from h3 h4)

-- 6ª demostración
example :
  ((p → q) → p) → p :=
-- by hint
by tauto

-- 7ª demostración
example :
  ((p → q) → p) → p :=
by finish
