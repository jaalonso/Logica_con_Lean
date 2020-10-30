-- Pruebas de (⋃i, ⋂j, A i j) ⊆ (⋂j, ⋃i, A i j)
-- ============================================

-- ----------------------------------------------------
-- Ej. 1. Demostrar
--    (⋃i, ⋂j, A i j) ⊆ (⋂j, ⋃i, A i j)
-- ----------------------------------------------------

import data.set

open set

variables {I J U : Type}
variables (A : I → J → set U)

-- 1ª demostración
example : (⋃i, ⋂j, A i j) ⊆ (⋂j, ⋃i, A i j) :=
begin
  intros x h,
  rw mem_Union at h,
  cases h with i hi,
  rw mem_Inter at hi,
  apply mem_Inter.mpr,
  intro j,
  apply mem_Union.mpr,
  use i,
  exact (hi j),
end

-- 2ª demostración
example : (⋃i, ⋂j, A i j) ⊆ (⋂j, ⋃i, A i j) :=
begin
  intros x h,
  simp * at *,
  cases h with i hi,
  intro j,
  use i,
  exact (hi j),
end

 
