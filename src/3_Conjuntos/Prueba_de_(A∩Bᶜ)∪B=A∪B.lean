-- Prueba de (A ∩ Bᶜ) ∪ B = A ∪ B
-- ==============================

-- ----------------------------------------------------
-- Ej. 1. Demostrar
--    (A ∩ Bᶜ) ∪ B = A ∪ B
-- ----------------------------------------------------

import data.set
import logic.basic
open set
variable  U : Type
variables A B C : set U

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
  rw inter_univ
end

-- ?ª demostración
-- ===============

example : (A ∩ Bᶜ) ∪ B = A ∪ B :=
by rw [union_distrib_right, compl_union_self, inter_univ]

-- ?ª demostración
-- ===============

example : (A ∩ Bᶜ) ∪ B = A ∪ B :=
by simp [union_distrib_right]

