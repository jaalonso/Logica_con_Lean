-- Conjuntos con Lean
-- ==================

import data.set
open set

section Conjuntos

variable  {U : Type}
variable  {x : U}
variables {A B C : set U}

-- * Elementos básicos sobre conjuntos
-- ===================================

-- ** Pruebas de la reflexividad de la inclusión de conjuntos
-- ==========================================================

-- ----------------------------------------------------
-- Ej. 1. Demostrar
--    A ⊆ A
-- ----------------------------------------------------

-- #reduce x ∈ A
-- #reduce B ⊆ C

-- 1ª demostración
example : A ⊆ A :=
begin
  intros x h,
  exact h,
end

-- 2ª demostración
example : A ⊆ A :=
assume x, 
assume h : x ∈ A,
show x ∈ A, from h

-- 3ª demostración
example : A ⊆ A :=
assume x, 
assume h : x ∈ A,
h

-- 4ª demostración
example : A ⊆ A :=
assume x, 
λ h : x ∈ A, h

-- 5ª demostración
example : A ⊆ A :=
assume x, 
id

-- 6ª demostración
example : A ⊆ A :=
λ x, id

-- 7ª demostración
example : A ⊆ A :=
-- by library_search
set.subset.rfl

open set

-- 8ª demostración
example : A ⊆ A :=
subset.rfl

-- 9ª demostración
example : A ⊆ A :=
-- by hint
by tauto

-- 10ª demostración
example : A ⊆ A :=
by finish

-- 11ª demostración
example : A ⊆ A :=
by refl 

-- ** Pruebas de la antisimetría de la inclusión de conjuntos
-- ==========================================================

-- ----------------------------------------------------
-- Ej. 2. Demostrar
--    A ⊆ B, B ⊆ A ⊢ A = B 
-- ----------------------------------------------------

-- 1ª demostración
example 
  (h1 : A ⊆ B)
  (h2 : B ⊆ A)
  : A = B :=
begin
  ext,
  split,
  { intro h,
    exact h1 h, },
  { intro h,
    exact h2 h, },
end

-- 2ª demostración
example 
  (h1 : A ⊆ B)
  (h2 : B ⊆ A)
  : A = B :=
ext 
( assume x, 
  iff.intro
  ( assume h : x ∈ A,
    show x ∈ B, from h1 h)
  ( assume h : x ∈ B,
    show x ∈ A, from h2 h))

-- 3ª demostración
example 
  (h1 : A ⊆ B)
  (h2 : B ⊆ A)
  : A = B :=
ext 
(λ x, 
 iff.intro
 (λ h, h1 h)
 (λ h, h2 h))

-- 4ª demostración
example 
  (h1 : A ⊆ B)
  (h2 : B ⊆ A)
  : A = B :=
eq_of_subset_of_subset
  ( assume x,
    assume h : x ∈ A,
    show x ∈ B, from h1 h)
  ( assume x,
    assume h : x ∈ B,
    show x ∈ A, from h2 h)

-- 5ª demostración
example 
  (h1 : A ⊆ B)
  (h2 : B ⊆ A)
  : A = B :=
eq_of_subset_of_subset h1 h2

-- 6ª demostración
example 
  (h1 : A ⊆ B)
  (h2 : B ⊆ A)
  : A = B :=
-- by library_search
subset.antisymm h1 h2

-- ** Introducción de la intersección
-- ==================================

-- ----------------------------------------------------
-- Ej. 3. Demostrar
--    x ∈ A → x ∈ B → x ∈ A ∩ B
-- ----------------------------------------------------

-- #reduce x ∈ A ∩ B

-- 1ª demostración
example : x ∈ A → x ∈ B → x ∈ A ∩ B :=
begin
  intros h1 h2,
  simp,
  split,
  { exact h1, },
  { exact h2, },
end

-- 2ª demostración
example : x ∈ A → x ∈ B → x ∈ A ∩ B :=
begin
  intros h1 h2,
  split,
  { exact h1, },
  { exact h2, },
end

-- 3ª demostración
example : x ∈ A → x ∈ B → x ∈ A ∩ B :=
assume h1 : x ∈ A,
assume h2 : x ∈ B,
show x ∈ A ∩ B, from and.intro h1 h2

-- 4ª demostración
example : x ∈ A → x ∈ B → x ∈ A ∩ B :=
assume h1 : x ∈ A,
assume h2 : x ∈ B,
show x ∈ A ∩ B, from ⟨h1, h2⟩

-- 5ª demostración
example : x ∈ A → x ∈ B → x ∈ A ∩ B :=
assume h1 : x ∈ A,
assume h2 : x ∈ B,
⟨h1, h2⟩

-- 6ª demostración
example : x ∈ A → x ∈ B → x ∈ A ∩ B :=
λ h1 h2, ⟨h1, h2⟩

-- 7ª demostración
example : x ∈ A → x ∈ B → x ∈ A ∩ B :=
-- by library_search
mem_inter

-- *** Introducción de la unión
-- ============================

-- ----------------------------------------------------
-- Ej. 4. Demostrar
--    A ⊆ A ∪ B
-- ----------------------------------------------------

-- #reduce x ∈ A ∪ B

-- 1ª demostración
example : A ⊆ A ∪ B :=
begin
  intros x h,
  simp,
  left,
  exact h,
end

-- 2ª demostración
example : A ⊆ A ∪ B :=
begin
  intros x h,
  left,
  exact h,
end

-- 3ª demostración
example : A ⊆ A ∪ B :=
assume x,
assume h : x ∈ A,
show x ∈ A ∪ B, from or.inl h

-- 4ª demostración
example : A ⊆ A ∪ B :=
assume x,
assume h : x ∈ A,
or.inl h

-- 5ª demostración
example : A ⊆ A ∪ B :=
assume x,
λ h : x ∈ A, or.inl h

-- 6ª demostración
example : A ⊆ A ∪ B :=
assume x, or.inl 

-- 7ª demostración
example : A ⊆ A ∪ B :=
λ x, or.inl 

-- 8ª demostración
example : A ⊆ A ∪ B :=
-- by library_search
subset_union_left A B

-- 9ª demostración
example : A ⊆ A ∪ B :=
λ x, mem_union_left B

-- 10ª demostración
example : A ⊆ A ∪ B :=
-- by hint
by finish

-- 11ª demostración
example : A ⊆ A ∪ B :=
by simp

-- ** El conjunto vacío
-- ====================

-- ----------------------------------------------------
-- Ej. 5. Demostrar
--    ∅ ⊆ A
-- ----------------------------------------------------

-- #reduce (∅ : set U)
-- #reduce x ∈ (∅ : set U) 

-- 1ª demostración
example : ∅ ⊆ A :=
begin
  intros x h,
  simp at h,
  exfalso,
  exact h,
end

-- 2ª demostración
example : ∅ ⊆ A :=
begin
  intros x h,
  exfalso,
  exact h,
end

-- 3ª demostración
example : ∅ ⊆ A :=
assume x,
assume h : x ∈ (∅ : set U),
show x ∈ A, from false.elim h

-- 4ª demostración
example : ∅ ⊆ A :=
λ x, λ h, false.elim h

-- 5ª demostración
example : ∅ ⊆ A :=
λ _, false.elim 

-- 6ª demostración
example : ∅ ⊆ A :=
-- by library_search
empty_subset A

-- 7ª demostración
example : ∅ ⊆ A :=
assume x,
assume h : x ∈ (∅ : set U),
show x ∈ A, from absurd h (not_mem_empty x)

-- 8ª demostración
example : ∅ ⊆ A :=
λ x h, absurd h (not_mem_empty x)

-- 9ª demostración
example : ∅ ⊆ A :=
-- by hint
by tauto

-- 10ª demostración
example : ∅ ⊆ A :=
by finish

-- 11ª demostración
example : ∅ ⊆ A :=
by simp 

-- ** Diferencia de conjuntos
-- ==========================

-- ----------------------------------------------------
-- Ej. 6. Demostrar
--    A \ B ⊆ A
-- ----------------------------------------------------

-- #reduce (A \ B)
-- #reduce x ∈ A \ B

-- 1ª demostración
example : A \ B ⊆ A :=
begin
  intros x h,
  simp at h,
  exact h.left,
end

-- 2ª demostración
example : A \ B ⊆ A :=
begin
  intros x h,
  exact h.left,
end

-- 3ª demostración
example : A \ B ⊆ A :=
assume x,
assume h : x ∈ A \ B,
show x ∈ A, from h.left

-- 4ª demostración
example : A \ B ⊆ A :=
assume x,
assume h : x ∈ A \ B,
and.left h

-- 5ª demostración
example : A \ B ⊆ A :=
assume x,
λ h, and.left h

-- 6ª demostración
example : A \ B ⊆ A :=
assume x, and.left 

-- 7ª demostración
example : A \ B ⊆ A :=
λ _, and.left 

-- 8ª demostración
example : A \ B ⊆ A :=
-- by library_search
diff_subset A B

-- 9ª demostración
example : A \ B ⊆ A :=
assume x,
assume h : x ∈ A \ B,
show x ∈ A, from mem_of_mem_diff h

-- 10ª demostración
example : A \ B ⊆ A :=
λ _, mem_of_mem_diff 

-- 11ª demostración
example : A \ B ⊆ A :=
by finish [subset_def]

-- ** Complementario de un conjunto
-- ================================

-- ----------------------------------------------------
-- Ej. 7. Demostrar
--    A \ B ⊆ Bᶜ
-- ----------------------------------------------------

-- #reduce x ∈ Bᶜ
-- #reduce Bᶜ

-- 1ª demostración
example : A \ B ⊆ Bᶜ :=
begin
  intros x h,
  simp at *,
  exact h.right,
end

-- 2ª demostración
example : A \ B ⊆ Bᶜ :=
begin
  intros x h,
  exact h.right,
end

-- 3ª demostración
example : A \ B ⊆ Bᶜ :=
assume x,
assume h1 : x ∈ A \ B,
have h2 : x ∉ B, from and.right h1,
show x ∈ Bᶜ,     from h2

-- 4ª demostración
example : A \ B ⊆ Bᶜ :=
assume x,
assume h1 : x ∈ A \ B,
show x ∈ Bᶜ, from and.right h1

-- 5ª demostración
example : A \ B ⊆ Bᶜ :=
assume x,
λ h1, and.right h1

-- 6ª demostración
example : A \ B ⊆ Bᶜ :=
assume x, 
and.right

-- 7ª demostración
example : A \ B ⊆ Bᶜ :=
λ _, and.right 

-- 8ª demostración
example : A \ B ⊆ Bᶜ :=
λ _, not_mem_of_mem_diff 

-- ** Pruebas de la conmutatividad de la intersección
-- ==================================================

-- ----------------------------------------------------
-- Ej. 8. Demostrar
--    A ∩ B ⊆ B ∩ A
-- ----------------------------------------------------

-- 1ª demostración
example : A ∩ B ⊆ B ∩ A :=
begin
  intros x h,
  simp at *,
  split,
  { exact h.right, },
  { exact h.left,  },
end

-- 2ª demostración
example : A ∩ B ⊆ B ∩ A :=
begin
  intros x h,
  split,
  { exact h.right, },
  { exact h.left,  },
end

-- 3ª demostración
example : A ∩ B ⊆ B ∩ A :=
begin
  rintros x ⟨h1, h2⟩,
  split,
  { exact h2, },
  { exact h1, },
end

-- 4ª demostración
example : A ∩ B ⊆ B ∩ A :=
begin
  rintros x ⟨h1, h2⟩,
  exact ⟨h2, h1⟩,
end

-- 5ª demostración
example : A ∩ B ⊆ B ∩ A :=
assume x,
assume h : x ∈ A ∩ B,
have h1 : x ∈ A, from and.left h,
have h2 : x ∈ B, from and.right h,
show x ∈ B ∩ A,  from and.intro h2 h1

-- 6ª demostración
example : A ∩ B ⊆ B ∩ A :=
assume x,
assume h : x ∈ A ∩ B,
have h1 : x ∈ A ∧ x ∈ B, from h,
have h2 : x ∈ B ∧ x ∈ A, from and.comm.mp h1,
show x ∈ B ∩ A,          from h2 

-- 7ª demostración
example : A ∩ B ⊆ B ∩ A :=
assume x,
assume h : x ∈ A ∩ B,
show x ∈ B ∩ A, from and.comm.mp h

-- 8ª demostración
example : A ∩ B ⊆ B ∩ A :=
assume x,
assume h : x ∈ A ∩ B,
and.comm.mp h

-- 9ª demostración
example : A ∩ B ⊆ B ∩ A :=
assume x,
λ h, and.comm.mp h

-- 10ª demostración
example : A ∩ B ⊆ B ∩ A :=
assume x,
and.comm.mp 

-- 10ª demostración
example : A ∩ B ⊆ B ∩ A :=
λ _, and.comm.mp 

-- 11ª demostración
example : A ∩ B ⊆ B ∩ A :=
-- by hint
by finish

-- 12ª demostración
lemma aux : A ∩ B ⊆ B ∩ A :=
by simp

-- ----------------------------------------------------
-- Ej. 9. Demostrar
--    A ∩ B = B ∩ A
-- ----------------------------------------------------

-- 1ª demostración
example : A ∩ B = B ∩ A :=
begin
  apply eq_of_subset_of_subset,
  { exact aux, },
  { exact aux, },
end

-- 2ª demostración
example : A ∩ B = B ∩ A :=
eq_of_subset_of_subset aux aux

-- 3ª demostración
example : A ∩ B = B ∩ A :=
-- by library_search
inter_comm A B

-- 4ª demostración
example : A ∩ B = B ∩ A :=
-- by hint
by finish

-- * Identidades conjuntistas
-- ==========================

-- ** Distributiva de la intersección sobre la unión
-- =================================================

-- ----------------------------------------------------
-- Ej. 10. Demostrar
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
-- Ej. 11. Demostrar
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
-- Ej. 12. Demostrar
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
eq_of_subset_of_subset inter_union_l1 inter_union_l2

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

-- ** (A ∩ Bᶜ) ∪ B = A ∪ B
-- =======================

-- ----------------------------------------------------
-- Ej. 1e. Demostrar
--    (A ∩ Bᶜ) ∪ B = A ∪ B
-- ----------------------------------------------------

-- 1ª demostración
-- ===============

example : (A ∩ Bᶜ) ∪ B = A ∪ B :=
calc
  (A ∩ Bᶜ) ∪ B = (A ∪ B) ∩ (Bᶜ ∪ B) : by rw union_distrib_right
           ... = (A ∪ B) ∩ univ     : by rw compl_union_self
           ... = A ∪ B              : by rw inter_univ

example : (A ∩ B) ∪ C = (A ∪ C) ∩ (B ∪ C) :=
-- by library_search 
union_distrib_right A B C

example : Bᶜ ∪ B = univ :=
-- by library_search
compl_union_self B

example : A ∩ univ = A :=
-- by library_search
inter_univ A

-- 2ª demostración
-- ===============

example : (A ∩ Bᶜ) ∪ B = A ∪ B :=
begin
  rw union_distrib_right,
  rw compl_union_self,
  rw inter_univ,
end

-- 3ª demostración
-- ===============

example : (A ∩ Bᶜ) ∪ B = A ∪ B :=
by rw [union_distrib_right, compl_union_self, inter_univ]

-- 4ª demostración
-- ===============

example : (A ∩ Bᶜ) ∪ B = A ∪ B :=
by simp [union_distrib_right]

end Conjuntos

-- * Familias de conjuntos
-- =======================

section Familias

variables {I U : Type}
variable  {x : U}
variables {A B : I → set U}

-- ** Pertenencia a uniones e intersecciones de familias
-- =====================================================

-- ----------------------------------------------------
-- Ej. 14. Demostrar que
--    (x ∈ ⋃ i, A i) ↔ (∃ i, x ∈ A i) 
-- ----------------------------------------------------

-- 1ª demostración
example :
  (x ∈ ⋃ i, A i) ↔ (∃ i, x ∈ A i) :=
-- by library_search
mem_Union

-- 2ª demostración
example :
  (x ∈ ⋃ i, A i) ↔ (∃ i, x ∈ A i) :=
by simp 

-- ----------------------------------------------------
-- Ej. 15. Demostrar que
--    (x ∈ ⋂ i, A i) ↔ (∀ i, x ∈ A i)
-- ----------------------------------------------------

-- 1ª demostración
example :
  (x ∈ ⋂ i, A i) ↔ (∀ i, x ∈ A i) :=
-- by library_search
mem_Inter

-- 2ª demostración
example :
  (x ∈ ⋂ i, A i) ↔ (∀ i, x ∈ A i) :=
by simp

-- ** Distributiva de la intersección general sobre la intersección
-- ================================================================

-- 1ª demostración
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

-- 2ª demostración
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

-- 3ª demostración
example : 
  (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
-- by library_search
Inter_inter_distrib A B

-- 4ª demostración
example : 
  (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
ext (by finish)

-- ** Pruebas de intersección sobre unión general
-- ==============================================

variable  {C : set U}

-- ----------------------------------------------------
-- Ej. 16. Demostrar
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
-- Ej. 17. Demostrar
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
-- Ej. 18. Demostrar
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

end Familias

-- ** Pruebas de (⋃i, ⋂j, A i j) ⊆ (⋂j, ⋃i, A i j)
-- ===============================================

section FamiliaDoble

variables {I J U : Type}
variables (A : I → J → set U)

-- ----------------------------------------------------
-- Ej. 19. Demostrar
--    (⋃i, ⋂j, A i j) ⊆ (⋂j, ⋃i, A i j)
-- ----------------------------------------------------

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

end FamiliaDoble

-- * Conjunto potencia
-- ===================

section Potencia

variable  {U : Type}
variables {A B C : set U}

-- ** Monotonía del conjunto potencia
-- ==================================

-- #reduce 𝒫 A
-- #reduce B ∈ 𝒫 A

-- ----------------------------------------------------
-- Ej. 20. Demostrar
--    𝒫 A ⊆ 𝒫 B → A ⊆ B 
-- ----------------------------------------------------

-- 1ª demostración
example : 𝒫 A ⊆ 𝒫 B → A ⊆ B :=
begin
  intro h,
  apply subset_of_mem_powerset,
  apply h,
  apply mem_powerset,
  exact subset.rfl,
end

-- 2ª demostración
example : 𝒫 A ⊆ 𝒫 B → A ⊆ B :=
begin
  intro h,
  apply h,
  exact subset.rfl,
end

-- 3ª demostración
example : 𝒫 A ⊆ 𝒫 B → A ⊆ B :=
begin
  intro h,
  exact (h subset.rfl),
end

-- 4ª demostración
example : 𝒫 A ⊆ 𝒫 B → A ⊆ B :=
λ h, h subset.rfl

-- 5ª demostración
example : 𝒫 A ⊆ 𝒫 B → A ⊆ B :=
assume h1 : 𝒫 A ⊆ 𝒫 B,
have h2 : A ⊆ A, from subset.rfl,
have h3 : A ∈ 𝒫 A, from h2,
have h4 : A ∈ 𝒫 B, from h1 h3,
show A ⊆ B, from h4

-- 6ª demostración
example : 𝒫 A ⊆ 𝒫 B → A ⊆ B :=
assume h1 : 𝒫 A ⊆ 𝒫 B,
have h2 : A ⊆ A, from subset.rfl,
have h3 : A ∈ 𝒫 A, from h2,
h1 h3

-- 7ª demostración
example : 𝒫 A ⊆ 𝒫 B → A ⊆ B :=
assume h1 : 𝒫 A ⊆ 𝒫 B,
have h2 : A ⊆ A, from subset.rfl,
h1 h2

-- 8ª demostración
example : 𝒫 A ⊆ 𝒫 B → A ⊆ B :=
assume h1 : 𝒫 A ⊆ 𝒫 B,
h1 subset.rfl

-- 9ª demostración
lemma aux1 : 𝒫 A ⊆ 𝒫 B → A ⊆ B :=
λ h, h subset.rfl

-- 10ª demostración
example : 𝒫 A ⊆ 𝒫 B → A ⊆ B :=
powerset_mono.mp

-- ----------------------------------------------------
-- Ej. 21. Demostrar
--    A ⊆ B → 𝒫 A ⊆ 𝒫 B 
-- ----------------------------------------------------

-- 1ª demostración
example : A ⊆ B → 𝒫 A ⊆ 𝒫 B :=
begin
  intro h,
  intros C hCA,
  apply mem_powerset,
  apply subset.trans hCA h,
end

-- 2ª demostración
example : A ⊆ B → 𝒫 A ⊆ 𝒫 B :=
begin
  intros h C hCA,
  apply subset.trans hCA h,
end

-- 3ª demostración
lemma aux2 : A ⊆ B → 𝒫 A ⊆ 𝒫 B :=
λ h C hCA, subset.trans hCA h

-- 4ª demostración
example : A ⊆ B → 𝒫 A ⊆ 𝒫 B :=
powerset_mono.mpr

-- ----------------------------------------------------
-- Ej. 22. Demostrar
--    𝒫 A ⊆ 𝒫 B ↔ A ⊆ B
-- ----------------------------------------------------

-- 1ª demostración
example : 𝒫 A ⊆ 𝒫 B ↔ A ⊆ B :=
iff.intro aux1 aux2

-- 2ª demostración
example : 𝒫 A ⊆ 𝒫 B ↔ A ⊆ B :=
-- by library_search
powerset_mono

-- 3ª demostración
example : 𝒫 A ⊆ 𝒫 B ↔ A ⊆ B :=
-- by hint
by finish

-- 4ª demostración
example : 𝒫 A ⊆ 𝒫 B ↔ A ⊆ B :=
by simp

end Potencia
