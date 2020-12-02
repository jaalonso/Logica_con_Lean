-- Relaciones en Lean
-- ==================

import tactic

-- * Relaciones de orden
-- =====================

-- ** Las irreflexivas y transitivas son asimétricas
-- =================================================

-- ----------------------------------------------------
-- Ej. 1. Demostrar que las relaciones irreflexivas y
-- transitivas son asimétricas.
-- ----------------------------------------------------

section Ej_1

variable A : Type
variable R : A → A → Prop

-- #reduce irreflexive R
-- #reduce transitive R

-- 1ª demostración
example
  (h1 : irreflexive R)
  (h2 : transitive R)
  : ∀ x y, R x y → ¬ R y x :=
begin
  intros x y h3 h4,
  apply h1 x,
  apply h2 h3 h4,
end

-- 2ª demostración
example
  (h1 : irreflexive R)
  (h2 : transitive R)
  : ∀ x y, R x y → ¬ R y x :=
begin
  intros x y h3 h4,
  apply (h1 x) (h2 h3 h4),
end

-- 3ª demostración
example
  (h1 : irreflexive R)
  (h2 : transitive R)
  : ∀ x y, R x y → ¬ R y x :=
λ x y h3 h4, (h1 x) (h2 h3 h4)

-- 4ª demostración
example
  (h1 : irreflexive R)
  (h2 : transitive R)
  : ∀ x y, R x y → ¬ R y x :=
assume x y,
assume h3 : R x y,
assume h4 : R y x,
have h5 : R x x, from h2 h3 h4,
have h6 : ¬ R x x, from h1 x,
show false, from h6 h5

end Ej_1

-- ** Las partes estrictas son irreflexivas
-- ========================================

-- ----------------------------------------------------
-- Ej. 2. La parte estricta de una relación R es la
-- relación R' definida por
--    R' a b := R a b ∧ a ≠ b
--
-- Demostrar que la parte estricta de cualquier
-- relación es irreflexiva.
-- ----------------------------------------------------

section Ej_2

parameter {A : Type}
parameter (R : A → A → Prop)

definition R' (a b : A) : Prop :=
  R a b ∧ a ≠ b

-- #reduce irreflexive R

-- 1ª demostración
example :
  irreflexive R' :=
begin
  intros a h,
  cases h with h1 h2,
  apply h2,
  refl,
end

-- 2ª demostración
example :
  irreflexive R' :=
assume a,
assume : R' a a,
have a ≠ a, from and.right this,
have a = a, from rfl,
show false, from ‹a ≠ a› ‹a = a›

end Ej_2

-- ** Las partes estrictas de los órdenes parciales son transitivas
-- ================================================================

-- ----------------------------------------------------
-- Ej. 3. Demostrar que si R es un orden parcial,
-- entonces su parte estricta es transitiva.
-- ----------------------------------------------------

section Ej_3

parameter {A : Type}
parameter (R : A → A → Prop)
parameter (reflR    : reflexive R)
parameter (transR   : transitive R)
parameter (antisimR : anti_symmetric R)
variables {a b c : A}

definition R1 (a b : A) : Prop :=
  R a b ∧ a ≠ b

include transR
include antisimR

-- 1ª demostración
example : transitive R1 :=
begin
  rintros a b c ⟨h1,h2⟩ ⟨h3,h4⟩,
  split,
  { apply (transR h1 h3), },
  { intro h5,
    apply h4,
    apply (antisimR h3),
    rw ←h5,
    exact h1, },
end

-- 2ª demostración
-- ===============

local infix ≤ := R
local infix < := R1

example : transitive (<) :=
assume a b c,
assume h₁ : a < b,
assume h₂ : b < c,
have a ≤ b, from and.left h₁,
have a ≠ b, from and.right h₁,
have b ≤ c, from and.left h₂,
have b ≠ c, from and.right h₂,
have a ≤ c, from transR ‹a ≤ b› ‹b ≤ c›,
have a ≠ c, from
    assume : a = c,
    have c ≤ b, from eq.subst ‹a = c› ‹a ≤ b›,
    have b = c, from antisimR ‹b ≤ c› ‹c ≤ b›,
    show false, from ‹b ≠ c› ‹b = c›,
show a < c, from and.intro ‹a ≤ c› ‹a ≠ c›

end Ej_3

-- ** Las partes simétricas de las reflexivas son reflexivas
-- =========================================================

-- ----------------------------------------------------
-- Ej. 4. La parte simétrica de una relación R es la
-- relación S definida por
--    S x y := R x y ∧ R y x
--
-- Demostrar que la parte simétrica de una relación
-- reflexiva es reflexiva.
-- ----------------------------------------------------

section Ej_4

parameter A : Type
parameter R : A → A → Prop
parameter reflR : reflexive R

include reflR

def S (x y : A) := R x y ∧ R y x

-- 1ª demostración
example : reflexive S :=
begin
  intro x,
  split,
  { exact (reflR x), },
  { exact (reflR x), },
end

-- 2ª demostración
example : reflexive S :=
assume x,
have R x x, from reflR x,
show S x x, from and.intro this this

-- 3ª demostración
example : reflexive S :=
assume x,
show S x x, from and.intro (reflR x) (reflR x)

-- 4ª demostración
example : reflexive S :=
assume x,
and.intro (reflR x) (reflR x)

-- 5ª demostración
example : reflexive S :=
λ x, ⟨reflR x, reflR x⟩

-- ** Las partes simétricas son simétricas
-- =======================================

-- ----------------------------------------------------
-- Ej. 4b. Demostrar que la parte simétrica de cualquier
-- relación es simétrica.
-- ----------------------------------------------------

-- 1ª demostración
example : symmetric S :=
begin
  intros x y h,
  split,
  { exact h.right, },
  { exact h.left, },
end

-- 2ª demostración
example : symmetric S :=
begin
  intros x y h,
  exact ⟨h.right, h.left⟩,
end

-- 3ª demostración
example : symmetric S :=
λ x y h, ⟨h.right, h.left⟩

-- 4ª demostración
example : symmetric S :=
assume x y,
assume h : S x y,
have h1 : R x y, from h.left,
have h2 : R y x, from h.right,
show S y x, from ⟨h2, h1⟩

-- 5ª demostración
example : symmetric S :=
assume x y,
assume h : S x y,
show S y x, from ⟨h.right, h.left⟩

-- 6ª demostración
example : symmetric S :=
λ x y h, ⟨h.right, h.left⟩

end Ej_4

-- * Órdenes sobre números
-- =======================

-- ** Pruebas de n + 1 ≤ m ⊢ n < m + 1
-- ===================================

-- ----------------------------------------------------
-- Ej. 5. Demostrar que si n y m son números naturales
-- tales que n + 1 ≤ m, entonces n < m + 1.
-- ----------------------------------------------------

variables n m : ℕ

-- 1ª demostración
example
  (h : n + 1 ≤ m)
  : n < m + 1 :=
calc
  n   < n + 1 : lt_add_one n
  ... ≤ m     : h
  ... < m + 1 : lt_add_one m

-- 2ª demostración
example
  (h : n + 1 ≤ m)
  : n < m + 1 :=
have h1 : n < n + 1, from lt_add_one n,
have h2 : n < m,     from lt_of_lt_of_le h1 h,
have h3 : m < m + 1, from lt_add_one m,
show n < m + 1,      from lt.trans h2 h3

-- 3ª demostración
example
  (h : n + 1 ≤ m)
  : n < m + 1 :=
begin
  apply lt_trans (lt_add_one n),
  apply lt_of_le_of_lt h (lt_add_one m),
end

-- 4ª demostración
example
  (h : n + 1 ≤ m)
  : n < m + 1 :=
lt_trans (lt_add_one n) (lt_of_le_of_lt h (lt_add_one m))

-- 5ª demostración
example
  (h : n + 1 ≤ m)
  : n < m + 1 :=
-- by suggest
nat.lt.step h

-- 6ª demostración
example
  (h : n + 1 ≤ m)
  : n < m + 1 :=
-- by hint
by omega

-- 7ª demostración
example
  (h : n + 1 ≤ m)
  : n < m + 1 :=
by linarith

-- 8ª demostración
example
  (h : n + 1 ≤ m)
  : n < m + 1 :=
by nlinarith

-- * Relaciones de equivalencia
-- ============================

-- ** Las equivalencias son preórdenes simétricos
-- ==============================================

-- ----------------------------------------------------
-- Ej. 6. Un preorden es una relación reflexiva y
-- transitiva.
--
-- Demostrar que las relaciones de equivalencias son
-- los prórdenes simétricos.
-- ----------------------------------------------------

section Ej_6

variable {A : Type}
variable R : A → A → Prop

def preorden (R : A → A → Prop) : Prop :=
  reflexive R ∧ transitive R

-- #print equivalence
-- #print symmetric

-- 1ª demostración
example :
  equivalence R ↔ preorden R ∧ symmetric R :=
begin
  split,
  { rintros ⟨h1, h2, h3⟩,
    exact ⟨⟨h1, h3⟩, h2⟩, },
  { rintros ⟨⟨h1, h3⟩, h2⟩,
    exact ⟨h1, h2, h3⟩, },
end

-- 2ª demostración
example :
  equivalence R ↔ preorden R ∧ symmetric R :=
⟨λ ⟨h1, h2, h3⟩, ⟨⟨h1, h3⟩, h2⟩,
 λ ⟨⟨h1, h3⟩, h2⟩, ⟨h1, h2, h3⟩⟩

-- 3ª demostración
example :
  equivalence R ↔ preorden R ∧ symmetric R :=
iff.intro
  ( assume h1 : equivalence R,
    have h2 : reflexive R, from and.left h1,
    have h3 : symmetric R, from and.left (and.right h1),
    have h4 : transitive R, from and.right (and.right h1),
    show preorden R ∧ symmetric R,
      from and.intro (and.intro h2 h4) h3)
  ( assume h1 : preorden R ∧ symmetric R,
    have h2 : preorden R, from and.left h1,
    show equivalence R,
      from and.intro (and.left h2)
             (and.intro (and.right h1) (and.right h2)))

-- 4ª demostración
example :
  equivalence R ↔ preorden R ∧ symmetric R :=
begin
  unfold equivalence preorden,
  tauto,
end

-- 5ª demostración
example :
  equivalence R ↔ preorden R ∧ symmetric R :=
by finish [preorden]

end Ej_6

-- ** Las relaciones reflexivas y euclídeas son de equivalencia
-- ============================================================

-- ----------------------------------------------------
-- Ej. 7. Una relación binaria (≈) es euclídea si
--    ∀ {a b c}, a ≈ b → c ≈ b → a ≈ c
--
-- El objetivo de este ejercicio es demostrar que si una
-- relación es reflexiva y euclídea, entonces es de
-- equivalencia.
-- ----------------------------------------------------

section Ej_7

parameter {A : Type}
parameter (R : A → A → Prop)

local infix ≈ := R

parameter reflexivaR : reflexive (≈)
parameter euclideaR : ∀ {a b c}, a ≈ b → c ≈ b → a ≈ c

include reflexivaR euclideaR

-- ----------------------------------------------------
-- Ej. 7a. Demostrar que las relaciones reflexivas y
-- y euclídeas son simétricas.
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
-- Ej. 7b. Demostrar que las relaciones reflexivas y
-- y euclídeas son transitivas.
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
-- Ej. 7c. Demostrar que las relaciones reflexivas y
-- y euclídeas son de equivalencia.
-- ----------------------------------------------------

-- 1ª demostración
example : equivalence (≈) :=
begin
  unfold equivalence,
  exact ⟨reflexivaR, simetricaR, transitivaR⟩,
end

-- 2ª demostración
example : equivalence (≈) :=
⟨reflexivaR, simetricaR, transitivaR⟩

end Ej_7
