-- Pruebas de A ∈ 𝒫 (A ∪ B)
-- ========================

import data.set
open set

variable  {U : Type}
variables (A B : set U)

#reduce powerset A
#reduce B ∈ powerset A
#reduce 𝒫 A
#reduce B ∈ 𝒫 A

-- ?ª demostración
example : A ∈ 𝒫 (A ∪ B) :=
begin
  intros x h,
  simp,
  left,
  exact h,
end

-- ?ª demostración
example : A ∈ 𝒫 (A ∪ B) :=
begin
  intros x h,
  exact or.inl h,
end

-- ?ª demostración
example : A ∈ 𝒫 (A ∪ B) :=
λ x, or.inl 

-- ?ª demostración
example : A ∈ 𝒫 (A ∪ B) :=
assume x,
assume : x ∈ A,
show x ∈ A ∪ B, from or.inl ‹x ∈ A›


