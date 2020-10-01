-- Regla de introducción del cuantificador existencial
-- ===================================================

-- Ej. 1. Demostrar
--    ∀x P(x) ⊢ ∃x P(x)

import tactic

variable U : Type
variable c : U
variable P : U -> Prop

-- 1ª demostración
example 
  (h1 : ∀x, P x)
  : ∃x, P x :=
have h2 : P c, from h1 c,
show ∃x, P x,  from exists.intro c h2

-- 2ª demostración
example 
  (h1 : ∀x, P x)
  : ∃x, P x :=
have h2 : P c, from h1 c,
show ∃x, P x,  from exists.intro c h2

-- 3ª demostración
example 
  (h1 : ∀x, P x)
  : ∃x, P x :=
exists.intro c (h1 c)

-- 4ª demostración
example 
  (c : U)
  (h1 : ∀x, P x)
  : ∃x, P x :=
begin
  use c,
  apply h1,
end
