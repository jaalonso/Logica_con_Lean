-- Reglas de la intersección general
-- =================================

import data.set
open set

section
variables {I U : Type}
variables {A : I → set U}
variable  {x : U}

-- Regla de introducción de la intersección
-- ========================================

-- 1ª demostración
example
  (h : ∀ i, x ∈ A i) 
  : x ∈ ⋂ i, A i :=
begin
  simp,
  assumption,
end

-- 2ª demostración
theorem Inter.intro  
  (h : ∀ i, x ∈ A i) 
  : x ∈ ⋂ i, A i :=
by simp; assumption

-- Regla de eliminación de la intersección
-- =======================================

-- 1ª demostración
example
  (h : x ∈ ⋂ i, A i) 
  (i : I) 
  : x ∈ A i :=
begin
  simp at h,
  apply h,
end

-- 2ª demostración
@[elab_simple]
theorem Inter.elim 
  (h : x ∈ ⋂ i, A i) 
  (i : I) 
  : x ∈ A i :=
by simp at h; apply h

end
