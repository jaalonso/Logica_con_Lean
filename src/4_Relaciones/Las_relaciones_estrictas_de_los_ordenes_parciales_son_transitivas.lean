-- Las relaciones estrictas de los órdenes parciales son transitivas
-- =================================================================

-- ----------------------------------------------------
-- Ej. 1. Demostrar que si R es un orden parcial y R' 
-- es su relación estricta, entonces R' es transitiva.
-- ----------------------------------------------------

import tactic

section

parameter {A : Type} 
parameter (R : A → A → Prop)
parameter (reflR    : reflexive R)
parameter (transR   : transitive R)
parameter (antisimR : anti_symmetric R)
variables {a b c : A}

definition R' (a b : A) : Prop := 
  R a b ∧ a ≠ b

include transR
include antisimR

-- 1ª demostración
example : R' a b → R' b c → R' a c :=
begin
  rintros ⟨h1,h2⟩ ⟨h3,h4⟩,
  split,
  { apply (transR h1 h3), },
  { intro h5,
    apply h4,
    apply (antisimR h3),
    rw ←h5,
    exact h1, },
end

-- 2ª demostración
-- ===============

local infix ≤ := R
local infix < := R'

example  
  (h₁ : a < b) 
  (h₂ : b < c) 
  : a < c :=
have a ≤ b, from and.left h₁,
have a ≠ b, from and.right h₁,
have b ≤ c, from and.left h₂,
have b ≠ c, from and.right h₂,
have a ≤ c, from transR ‹a ≤ b› ‹b ≤ c›,
have a ≠ c, from
    assume : a = c,
    have c ≤ b, from eq.subst ‹a = c› ‹a ≤ b›,
    have b = c, from antisimR ‹b ≤ c› ‹c ≤ b›,
    show false, from ‹b ≠ c› ‹b = c›,
show a < c, from and.intro ‹a ≤ c› ‹a ≠ c›

end
