-- Pruebas del modus tollens
-- =========================

import tactic

variables (P Q R : Prop)

example 
  (h1 : P → Q)
  (h2 : Q → R)
  : P → R :=
h2 ∘ h1

example 
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
mt h1 h2

example 
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
h2 ∘ h1
