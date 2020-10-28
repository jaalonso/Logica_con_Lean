-- Pruebas de la propiedad distributiva de la intersección
-- =======================================================

import data.set
import tactic
open set

variables {I U : Type}
variables {A B : I → set U}

-- ?ª demostración
example : 
  (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
begin
  ext,
  split,
  { intro h,
    rw mem_Inter at h,
    split,
    { rw mem_Inter,
      intro i,
      exact (h i).left, },
    { rw mem_Inter,
      intro i,
      exact (h i).right, }},
  { rintro ⟨h1, h2⟩,
    rw mem_Inter at *,
    intro i,
    exact ⟨h1 i, h2 i⟩, },
end

-- ?ª demostración
example : 
  (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
ext $
assume x : U,
iff.intro
( assume h : x ∈ ⋂ i, A i ∩ B i,
  have h1 : ∀ i, x ∈ A i ∩ B i,     
    from mem_Inter.mp h,
  have h2 : ∀ i, x ∈ A i,           
    from assume i, and.left (h1 i),
  have h3 : ∀ i, x ∈ B i,           
    from assume i, and.right (h1 i),
  have h4 : x ∈ ⋂ i, A i,           
    from mem_Inter.mpr h2,
  have h5 : x ∈ ⋂ i, B i,           
    from mem_Inter.mpr h3,
  show x ∈ (⋂ i, A i) ∩ (⋂ i, B i), 
    from and.intro h4 h5)
( assume h : x ∈ (⋂ i, A i) ∩ (⋂ i, B i),
  have h1 : ∀ i, x ∈ A i,
    from mem_Inter.mp (and.left h), 
  have h2 : ∀ i, x ∈ B i,
    from mem_Inter.mp (and.right h),
  have h3 : ∀ i, x ∈ A i ∩ B i,
    from assume i, and.intro (h1 i) (h2 i),
  show x ∈ ⋂ i, A i ∩ B i, 
    from mem_Inter.mpr h3)

-- ?ª demostración
example : 
  (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
-- by library_search
Inter_inter_distrib A B

-- ?ª demostración
example : 
  (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
ext (by finish)
