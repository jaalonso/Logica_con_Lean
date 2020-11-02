-- Las relaciones reflexivas y euclídeas son de equivalencia
-- =========================================================

import tactic

section

parameter {A : Type} 
parameter (R : A → A → Prop)

local infix ≈ := R

parameter reflexivaR : reflexive (≈)
parameter euclideaR : ∀ {a b c}, a ≈ b → c ≈ b → a ≈ c

include reflexivaR euclideaR 

-- ----------------------------------------------------
-- Ej. 1. Demostrar que las relaciones reflexivas y 
-- y euclideas son simétricas.
-- ----------------------------------------------------

-- 1ª demostración
example : symmetric (≈) :=
begin
  intros a b h,
  exact euclideaR (reflexivaR b) h,
end

-- 2ª demostración
example : symmetric (≈) :=
λ a b h, euclideaR (reflexivaR b) h

-- 3ª demostración
lemma simetricaR : symmetric (≈) :=
assume a b (h1 : a ≈ b),
have h2 : b ≈ b, from (reflexivaR b),
show b ≈ a, from euclideaR h2 h1

-- ----------------------------------------------------
-- Ej. 2. Demostrar que las relaciones reflexivas y 
-- y euclideas son transitivas.
-- ----------------------------------------------------

-- 1ª demostración
example : transitive (≈) :=
begin
  rintros a b c h1 h2,
  apply euclideaR h1,
  exact euclideaR (reflexivaR c) h2,
end

-- 2ª demostración
lemma transitivaR : transitive (≈) :=
λ a b c h1 h2, (euclideaR h1) (euclideaR (reflexivaR c) h2)

-- 3ª demostración
example : transitive (≈) :=
assume a b c (h1 : a ≈ b) (h2 : b ≈ c),
have h3 : c ≈ b, from euclideaR (reflexivaR c) h2,
show a ≈ c, from euclideaR h1 h3

-- ----------------------------------------------------
-- Ej. 3. Demostrar que las relaciones reflexivas y 
-- y euclideas son de equivalencia.
-- ----------------------------------------------------

example : equivalence (≈) :=
⟨reflexivaR, simetricaR, transitivaR⟩

end
