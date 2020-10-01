-- Regla de eliminación del cuantificador universal
-- ================================================

-- Ej. 1. Demostrar
--    P(c), ∀x (P(x) → ¬Q(x)) ⊢ ¬Q(c)

import tactic

variable  U : Type
variable  c : U
variables P Q : U → Prop

-- 1ª demostración
example
  (h1 : P c) 
  (h2 : ∀x, P x → ¬Q x)
  : ¬Q c :=
have h3 : P c → ¬Q c, from h2 c,
show ¬Q c,            from h3 h1

-- 2ª demostración
example
  (h1 : P c) 
  (h2 : ∀x, P x → ¬Q x)
  : ¬Q c :=
have h3 : P c → ¬Q c, from h2 c,
h3 h1

-- 3ª demostración
example
  (h1 : P c) 
  (h2 : ∀x, P x → ¬Q x)
  : ¬Q c :=
(h2 c) h1

-- 4ª demostración
example
  (h1 : P c) 
  (h2 : ∀x, P x → ¬Q x)
  : ¬Q c :=
-- by library_search
h2 c h1

-- 5ª demostración
example
  (h1 : P c) 
  (h2 : ∀x, P x → ¬Q x)
  : ¬Q c :=
-- by hint
by tauto

-- 6ª demostración
example
  (h1 : P c) 
  (h2 : ∀x, P x → ¬Q x)
  : ¬Q c :=
by finish
