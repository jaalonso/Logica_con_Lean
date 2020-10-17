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
show ∃x, P x,  from exists.intro c (h1 c)

-- 3ª demostración
example 
  (h1 : ∀x, P x)
  : ∃x, P x :=
exists.intro c (h1 c)

-- 4ª demostración
example 
  (h1 : ∀x, P x)
  : ∃x, P x :=
⟨c, h1 c⟩

-- 5ª demostración
example 
  (a : U)
  (h1 : ∀x, P x)
  : ∃x, P x :=
begin
  use a,
  apply h1,
end

-- 6ª demostración
example 
  (a : U)
  (h1 : ∀x, P x)
  : ∃x, P x :=
begin
  constructor,
  apply h1 a,
end

-- 7ª demostración
example 
  [inhabited U]
  (h1 : ∀x, P x)
  : ∃x, P x :=
begin
  constructor,
  apply h1 (default U),
end

-- 8ª demostración
example 
  (h : nonempty U)
  (h1 : ∀x, P x)
  : ∃x, P x :=
begin
  use (classical.choice h),
  apply h1,
end

