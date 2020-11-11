-- La composición de suprayectivas parciales es suprayectiva
-- =========================================================

-- ----------------------------------------------------
-- Ej. 1. Sean A un conjunto de elementos de X, B un
-- conjunto de elementos de Y, C un conjunto de
-- elementos de Z, f una función de X en Y y g una
-- función de Y en Z. Si f es suprayectiva de A en B y
-- g es suprayectiva de B en C, entonces (g ∘ f) es
-- suprayectiva de A en C.
-- ----------------------------------------------------

import data.set
open set function

variables {X Y Z : Type}
variable  (A : set X)
variable  (B : set Y)
variable  (C : set Z)
variable  (f : X → Y)
variable  (g : Y → Z)

-- #reduce surj_on f A B
-- #reduce surj_on g B C
-- #reduce surj_on (g ∘ f) A C

-- 1ª demostración
example
  (hf: surj_on f A B)
  (hg : surj_on g B C)
  : surj_on (g ∘ f) A C :=
begin
  intros z zC,
  simp,
  specialize (hg zC),
  simp at hg,
  cases hg with y h1,
  specialize (hf h1.left),
  simp at hf,
  cases hf with x h2,
  use x,
  split,
  { exact h2.left, },
  { calc g (f x) = g y : by rw h2.right
             ... = z   : by rw h1.right },
end

-- 2ª demostración
example
  (hf: surj_on f A B)
  (hg : surj_on g B C)
  : surj_on (g ∘ f) A C :=
begin
  intros z zC,
  specialize (hg zC),
  cases hg with y h1,
  specialize (hf h1.left),
  cases hf with x h2,
  use x,
  split,
  { exact h2.left, },
  { calc g (f x) = g y : by rw h2.right
             ... = z   : by rw h1.right },
end

-- 3ª demostración
example
  (hf: surj_on f A B)
  (hg : surj_on g B C)
  : surj_on (g ∘ f) A C :=
begin
  intros z zC,
  cases (hg zC) with y h1,
  cases (hf h1.left) with x h2,
  use x,
  split,
  { exact h2.left, },
  { calc g (f x) = g y : by rw h2.right
             ... = z   : by rw h1.right },
end

-- 4ª demostración
example
  (hf: surj_on f A B)
  (hg : surj_on g B C)
  : surj_on (g ∘ f) A C :=
begin
  intros z zC,
  cases (hg zC) with y h1,
  cases (hf h1.left) with x h2,
  exact ⟨x,
         ⟨h2.left,
          calc g (f x) = g y : by rw h2.right
                   ... = z   : by rw h1.right⟩⟩,
end

-- 5ª demostración
example
  (hf: surj_on f A B)
  (hg : surj_on g B C)
  : surj_on (g ∘ f) A C :=
assume z,
assume zC : z ∈ C,
exists.elim (hg zC)
  ( assume y (h1 : y ∈ B ∧ g y = z),
    exists.elim (hf (and.left h1))
    ( assume x (h2 : x ∈ A ∧ f x = y),
      show ∃x, x ∈ A ∧ g (f x) = z, from
        exists.intro x
          (and.intro
            (and.left h2)
            (calc
              g (f x) = g y : by rw and.right h2
                  ... = z   : by rw and.right h1))))

-- 6ª demostración
example
  (hf: surj_on f A B)
  (hg : surj_on g B C)
  : surj_on (g ∘ f) A C :=
-- by library_search
surj_on.comp hg hf
