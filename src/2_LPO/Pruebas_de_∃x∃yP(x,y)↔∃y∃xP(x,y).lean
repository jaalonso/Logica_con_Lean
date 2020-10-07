-- Pruebas de ∃x∃yP(x,y) ↔ ∃y∃xP(x,y)
-- ==================================

import tactic

section

variable {U : Type}
variable {P : U -> U -> Prop}

-- ------------------------------------------------------
-- Ej. 1. Demostrar que
--    ∃x∃yP(x,y) → ∃y∃xP(x,y)
-- ------------------------------------------------------

-- 1ª demostración
example :
  (∃ x, ∃ y, P x y) → (∃ y, ∃ x, P x y) :=
assume h1 : ∃ x, ∃ y, P x y,
exists.elim h1 
  ( assume x₀ (h2 : ∃ y, P x₀ y), 
    exists.elim h2
      ( assume y₀ (h3 : P x₀ y₀),
        have h5 : ∃ x, P x y₀, from exists.intro x₀ h3,
        show ∃ y, ∃ x, P x y,  from exists.intro y₀ h5))

-- 2ª demostración
example :
  (∃ x, ∃ y, P x y) → (∃ y, ∃ x, P x y) :=
assume ⟨x₀, y₀, (h1 : P x₀ y₀)⟩,
have h2 : ∃ x, P x y₀, from ⟨x₀, h1⟩,
show (∃ y, ∃ x, P x y), from ⟨y₀, h2⟩

-- 3ª demostración
example :
  (∃ x, ∃ y, P x y) → (∃ y, ∃ x, P x y) :=
assume ⟨x₀, y₀, (h1 : P x₀ y₀)⟩,
show (∃ y, ∃ x, P x y), from ⟨y₀, ⟨x₀, h1⟩⟩

-- 4ª demostración
example :
  (∃ x, ∃ y, P x y) → (∃ y, ∃ x, P x y) :=
assume ⟨x₀, y₀, (h1 : P x₀ y₀)⟩,
show (∃ y, ∃ x, P x y), from ⟨y₀, x₀, h1⟩

-- 5ª demostración
example :
  (∃ x, ∃ y, P x y) → (∃ y, ∃ x, P x y) :=
assume ⟨x₀, y₀, (h1 : P x₀ y₀)⟩,
⟨y₀, x₀, h1⟩

-- 6ª demostración
example :
  (∃ x, ∃ y, P x y) → (∃ y, ∃ x, P x y) :=
λ ⟨x₀, y₀, h1⟩, ⟨y₀, x₀, h1⟩

-- 7ª demostración
example :
  (∃ x, ∃ y, P x y) → (∃ y, ∃ x, P x y) :=
-- by library_search
exists_comm.mp 

-- 8ª demostración
example :
  (∃ x, ∃ y, P x y) → (∃ y, ∃ x, P x y) :=
begin
  intro h1,
  cases h1 with x₀ h2,
  cases h2 with y₀ h3,
  use y₀,
  use x₀,
  exact h3,
end

-- 9ª demostración
example :
  (∃ x, ∃ y, P x y) → (∃ y, ∃ x, P x y) :=
begin
  intro h1,
  cases h1 with x₀ h2,
  cases h2 with y₀ h3,
  use [y₀, x₀],
  exact h3,
end

-- 10ª demostración
example :
  (∃ x, ∃ y, P x y) → (∃ y, ∃ x, P x y) :=
begin
  intro h1,
  rcases h1 with ⟨x₀, y₀, h2⟩,
  use [y₀, x₀],
  exact h2,
end

-- 11ª demostración
example :
  (∃ x, ∃ y, P x y) → (∃ y, ∃ x, P x y) :=
begin
  intro h1,
  rcases h1 with ⟨x₀, y₀, h2⟩,
  exact ⟨y₀, x₀, h2⟩,
end

-- 12ª demostración
example :
  (∃ x, ∃ y, P x y) → (∃ y, ∃ x, P x y) :=
begin
  rintro ⟨x₀, y₀, h2⟩,
  exact ⟨y₀, x₀, h2⟩,
end

-- 13ª demostración
example :
  (∃ x, ∃ y, P x y) → (∃ y, ∃ x, P x y) :=
-- by hint
by tauto

-- 14ª demostración
lemma aux :
  (∃ x, ∃ y, P x y) → (∃ y, ∃ x, P x y) :=
by finish

-- ------------------------------------------------------
-- Ej. 2. Demostrar que
--    ∃x∃yP(x,y) ↔ ∃y∃xP(x,y)
-- ------------------------------------------------------

-- 1ª demostración
example :
  (∃ x y, P x y) ↔ (∃ y x, P x y) :=
iff.intro aux aux

-- 2ª demostración
example :
  (∃ x y, P x y) ↔ (∃ y x, P x y) :=
⟨aux, aux⟩

-- 3ª demostración
example :
  (∃ x y, P x y) ↔ (∃ y x, P x y) :=
-- by library_search
exists_comm

-- 4ª demostración
example :
  (∃ x y, P x y) ↔ (∃ y x, P x y) :=
-- by hint
by tauto

end
