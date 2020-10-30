-- Pruebas de intersección sobre unión general
-- ===========================================

import data.set

open set

variables {I U : Type}
variables {A : I → set U}
variable  {C : set U}

-- ----------------------------------------------------
-- Ej. 1. Demostrar
--    C ∩ (⋃i, A i) ⊆ (⋃ i, C ∩ A i) 
-- ----------------------------------------------------

-- 1ª demostración
example : 
  C ∩ (⋃i, A i) ⊆ (⋃ i, C ∩ A i)  :=
begin
  rintros x ⟨hC, hU⟩,
  rw mem_Union at hU,
  cases hU with i hA,
  apply mem_Union.mpr,
  use i,
  split,
  assumption',
end

-- 2ª demostración
example : 
  C ∩ (⋃i, A i) ⊆ (⋃ i, C ∩ A i)  :=
begin
  intros x h,
  simp * at *,
end

-- 3ª demostración
lemma inter_Uni_l1 : 
  C ∩ (⋃i, A i) ⊆ (⋃ i, C ∩ A i)  :=
by {intros x h, simp * at *}

-- ----------------------------------------------------
-- Ej. 2. Demostrar
--    (⋃ i, C ∩ A i) ⊆ C ∩ (⋃i, A i) 
-- ----------------------------------------------------

-- 1ª demostración
example : 
  (⋃ i, C ∩ A i) ⊆ C ∩ (⋃i, A i) :=
begin
  intros x h,
  rw mem_Union at h,
  cases h with i hi,
  cases hi with hC hA,
  split,
  { exact hC, },
  { apply mem_Union.mpr,
    use i,
    exact hA, },
end

-- 2ª demostración
example : (⋃ i, C ∩ A i) ⊆ C ∩ (⋃i, A i) :=
begin
  intros x h,
  rw mem_Union at h,
  rcases h with ⟨i, hC, hA⟩,
  split,
  { exact hC, },
  { apply mem_Union.mpr,
    use i,
    exact hA, },
end

-- 3ª demostración
example : 
  (⋃ i, C ∩ A i) ⊆ C ∩ (⋃i, A i) :=
begin
  intros x h,
  simp * at *,
end

-- 4ª demostración
lemma inter_Uni_l2 : 
  (⋃ i, C ∩ A i) ⊆ C ∩ (⋃i, A i) :=
by {intros x h, simp * at *}

-- ----------------------------------------------------
-- Ej. 3. Demostrar
--    C ∩ (⋃i, A i) = (⋃ i, C ∩ A i) 
-- ----------------------------------------------------

-- 1ª demostración
example : 
  C ∩ (⋃i, A i) = (⋃ i, C ∩ A i) :=
eq_of_subset_of_subset inter_Uni_l1 inter_Uni_l2

-- 2ª demostración
example : 
  C ∩ (⋃i, A i) = (⋃ i, C ∩ A i) :=
-- by library_search
inter_Union C A

-- 3ª demostración
example : 
  C ∩ (⋃i, A i) = (⋃ i, C ∩ A i) :=
ext $ by simp

-- 4ª demostración
example : 
  C ∩ (⋃i, A i) = (⋃ i, C ∩ A i) :=
by {ext, simp}

