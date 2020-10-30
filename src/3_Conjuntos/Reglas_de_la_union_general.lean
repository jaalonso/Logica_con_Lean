-- Reglas de la unión general
-- ==========================

import data.set

open set

variables {I U : Type}
variables {A : I → set U}
variable  {x : U}
variable  (i : I)

-- Regla de introducción de la unión
-- =================================

-- 1ª demostración
example
  (h : x ∈ A i) 
  : x ∈ ⋃ i, A i :=
begin
  simp,
  existsi i, 
  exact h
end

-- 2ª demostración
theorem Union.intro 
  (h : x ∈ A i) 
  : x ∈ ⋃ i, A i :=
by {simp, existsi i, exact h}

-- Regla de eliminación de la unión
-- ================================

-- 1ª demostración
example
  {b : Prop}
  (h₁ : x ∈ ⋃ i, A i) 
  (h₂ : ∀ (i : I), x ∈ A i → b) 
  : b :=
begin
  simp at h₁, 
  cases h₁ with i h,
  exact h₂ i h,
end

-- 2ª demostración
theorem Union.elim 
  {b : Prop}
  (h₁ : x ∈ ⋃ i, A i) 
  (h₂ : ∀ (i : I), x ∈ A i → b) 
  : b :=
by {simp at h₁, cases h₁ with i h, exact h₂ i h}


