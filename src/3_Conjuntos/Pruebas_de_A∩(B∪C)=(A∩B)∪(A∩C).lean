-- Pruebas de A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)
-- ==========================================

import data.set
open set

variable  {U : Type}
variables A B C : set U

-- ----------------------------------------------------
-- Ej. 1. Demostrar
--    A ∩ (B ∪ C) ⊆ (A ∩ B) ∪ (A ∩ C) 
-- ----------------------------------------------------

-- 1ª demostración
example :
  A ∩ (B ∪ C) ⊆ (A ∩ B) ∪ (A ∩ C) :=
begin
  intros x h,
  cases h with ha hbc,
  cases hbc with hb hc,
  { left,
    split,
    { exact ha, },
    { exact hb, }},
  { right,
    split, 
    { exact ha, },
    { exact hc, }},
end

-- 2ª demostración
example :
  A ∩ (B ∪ C) ⊆ (A ∩ B) ∪ (A ∩ C) :=
begin
  intros x h,
  cases h with ha hbc,
  cases hbc with hb hc,
  { left,
    split,
    { assumption, },
    { assumption, }},
  { right,
    split, 
    { assumption, },
    { assumption, }},
end

-- 3ª demostración
example :
  A ∩ (B ∪ C) ⊆ (A ∩ B) ∪ (A ∩ C) :=
begin
  intros x h,
  cases h with ha hbc,
  cases hbc with hb hc,
  { left,
    split, 
    assumption', },
  { right,
    split,
    assumption', },
end

-- 4ª demostración
example :
  A ∩ (B ∪ C) ⊆ (A ∩ B) ∪ (A ∩ C) :=
begin
  rintros x ⟨ha, (hb | hc)⟩,
  { left,
    split, 
    assumption', },
  { right,
    split,
    assumption', },
end

-- 5ª demostración
example :
  A ∩ (B ∪ C) ⊆ (A ∩ B) ∪ (A ∩ C) :=
assume x,
assume h : x ∈ A ∩ (B ∪ C),
have x ∈ A, from and.left h,
have x ∈ B ∪ C, from and.right h,
or.elim (‹x ∈ B ∪ C›)
  ( assume : x ∈ B,
    have x ∈ A ∩ B, from and.intro ‹x ∈ A› ‹x ∈ B›,
    show x ∈ (A ∩ B) ∪ (A ∩ C), from or.inl this)
  ( assume : x ∈ C,
    have x ∈ A ∩ C, from and.intro ‹x ∈ A› ‹x ∈ C›,
    show x ∈ (A ∩ B) ∪ (A ∩ C), from or.inr this)

-- 6ª demostración
lemma inter_union_l1 :
  A ∩ (B ∪ C) ⊆ (A ∩ B) ∪ (A ∩ C) :=
assume x,
assume h : x ∈ A ∩ (B ∪ C),
have ha : x ∈ A, from and.left h,
have hbc : x ∈ B ∪ C, from and.right h,
or.elim hbc
  ( assume hb : x ∈ B,
    have hab: x ∈ A ∩ B, from and.intro ha hb, 
    show x ∈ (A ∩ B) ∪ (A ∩ C), from or.inl hab)
  ( assume hc : x ∈ C,
    have hac : x ∈ A ∩ C, from and.intro ha hc,
    show x ∈ (A ∩ B) ∪ (A ∩ C), from or.inr hac)

-- ----------------------------------------------------
-- Ej. 2. Demostrar
--    (A ∩ B) ∪ (A ∩ C) ⊆ A ∩ (B ∪ C)
-- ----------------------------------------------------

-- 1ª demostración
example :
  (A ∩ B) ∪ (A ∩ C) ⊆ A ∩ (B ∪ C) :=
begin
  intros x h,
  cases h with hab hac,
  { split,
    { exact hab.left, },
    { left,
      exact hab.right, }},
  { split,
    { exact hac.left, },
    { right,
      exact hac.right, }},
end

-- 2ª demostración
example :
  (A ∩ B) ∪ (A ∩ C) ⊆ A ∩ (B ∪ C) :=
begin
  rintros x (⟨ha, hb⟩ | ⟨ha, hc⟩),
  { split,
    { exact ha, },
    { left,
      exact hb, }},
  { split,
    { exact ha, },
    { right,
      exact hc, }},
end

-- 3ª demostración
lemma inter_union_l2 :
  (A ∩ B) ∪ (A ∩ C) ⊆ A ∩ (B ∪ C) :=
assume x,
assume : x ∈ (A ∩ B) ∪ (A ∩ C),
or.elim this
  ( assume h : x ∈ A ∩ B,
    have x ∈ A, from and.left h,
    have x ∈ B, from and.right h,
    have x ∈ B ∪ C, from or.inl this,
    show x ∈ A ∩ (B ∪ C), from and.intro ‹x ∈ A› this)
  ( assume h : x ∈ A ∩ C,
    have x ∈ A, from and.left h,
    have x ∈ C, from and.right h,
    have x ∈ B ∪ C, from or.inr this,
    show x ∈ A ∩ (B ∪ C), from and.intro ‹x ∈ A› this)

-- ----------------------------------------------------
-- Ej. 3. Demostrar
--    (A ∩ B) ∪ (A ∩ C) = A ∩ (B ∪ C)
-- ----------------------------------------------------

-- 1ª demostración
example : 
  A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
-- by library_search
inter_distrib_left A B C

-- 2ª demostración
theorem inter_union : 
  A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
eq_of_subset_of_subset
  (inter_union_l1 A B C)
  (inter_union_l2 A B C)

-- 3ª demostración
example : 
  A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
begin
  ext,
  simp,
  exact and_or_distrib_left,
end

-- 4ª demostración
example : 
  A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
begin
  ext,
  exact and_or_distrib_left,
end

-- 5ª demostración
example : 
  A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
ext (λ x, and_or_distrib_left)
