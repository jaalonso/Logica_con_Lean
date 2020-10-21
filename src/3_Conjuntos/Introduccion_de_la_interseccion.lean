-- Introducción de la intersección
-- ===============================

-- ----------------------------------------------------
-- Ej. 1. Demostrar
--    x ∈ A → x ∈ B → x ∈ A ∩ B
-- ----------------------------------------------------

import data.set

variable  {U : Type}
variables A B : set U
variable  x : U

open set

-- #reduce x ∈ A
-- #reduce x ∈ A ∩ B

-- 1ª demostración
example : x ∈ A → x ∈ B → x ∈ A ∩ B :=
begin
  intros h1 h2,
  split,
  { exact h1, },
  { exact h2, },
end

-- 2ª demostración
example : x ∈ A → x ∈ B → x ∈ A ∩ B :=
assume h1 : x ∈ A,
assume h2 : x ∈ B,
show x ∈ A ∩ B, from and.intro h1 h2

-- 3ª demostración
example : x ∈ A → x ∈ B → x ∈ A ∩ B :=
assume h1 : x ∈ A,
assume h2 : x ∈ B,
show x ∈ A ∩ B, from ⟨h1, h2⟩

-- 4ª demostración
example : x ∈ A → x ∈ B → x ∈ A ∩ B :=
assume h1 : x ∈ A,
assume h2 : x ∈ B,
⟨h1, h2⟩

-- 5ª demostración
example : x ∈ A → x ∈ B → x ∈ A ∩ B :=
λ h1 h2, ⟨h1, h2⟩

-- 6ª demostración
example : x ∈ A → x ∈ B → x ∈ A ∩ B :=
-- by library_search
mem_inter


