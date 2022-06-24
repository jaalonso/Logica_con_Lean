-- Pruebas de ∃x∃yP(x,y) ↔ ∃y∃xP(x,y)
-- ==================================

import tactic

section

variable {U : Type}
variable {P : U -> U -> Prop}

-- ----------------------------------------------------
-- Ej. 1. Demostrar que
--    ∃x∃yP(x,y) → ∃y∃xP(x,y)
-- ----------------------------------------------------

-- 1ª demostración
example :
  (∃ x, ∃ y, P x y) → (∃ y, ∃ x, P x y) :=
assume h1 : ∃ x, ∃ y, P x y,
exists.elim h1
  ( assume a (h2 : ∃ y, P a y),
    exists.elim h2
      ( assume b (h3 : P a b),
        have h4 : ∃ x, P x b, from exists.intro a h3,
        show ∃ y, ∃ x, P x y,  from exists.intro b h4))

-- 2ª demostración
example :
  (∃ x, ∃ y, P x y) → (∃ y, ∃ x, P x y) :=
assume ⟨a, b, (h1 : P a b)⟩,
have h2 : ∃ x, P x b,  from ⟨a, h1⟩,
show (∃ y, ∃ x, P x y), from ⟨b, h2⟩

-- 3ª demostración
example :
  (∃ x, ∃ y, P x y) → (∃ y, ∃ x, P x y) :=
assume ⟨a, b, (h1 : P a b)⟩,
show (∃ y, ∃ x, P x y), from ⟨b, ⟨a, h1⟩⟩

-- 4ª demostración
example :
  (∃ x, ∃ y, P x y) → (∃ y, ∃ x, P x y) :=
assume ⟨a, b, (h1 : P a b)⟩,
show (∃ y, ∃ x, P x y), from ⟨b, a, h1⟩

-- 5ª demostración
example :
  (∃ x, ∃ y, P x y) → (∃ y, ∃ x, P x y) :=
assume ⟨a, b, (h1 : P a b)⟩,
⟨b, a, h1⟩

-- 6ª demostración
example :
  (∃ x, ∃ y, P x y) → (∃ y, ∃ x, P x y) :=
λ ⟨a, b, h1⟩, ⟨b, a, h1⟩

-- 7ª demostración
example :
  (∃ x y, P x y) → (∃ y x, P x y) :=
-- by library_search
exists_comm.mp

-- 8ª demostración
example :
  (∃ x, ∃ y, P x y) → (∃ y, ∃ x, P x y) :=
begin
  intro h1,
  cases h1 with a h2,
  cases h2 with b h3,
  use b,
  use a,
  exact h3,
end

-- 9ª demostración
example :
  (∃ x, ∃ y, P x y) → (∃ y, ∃ x, P x y) :=
begin
  intro h1,
  cases h1 with a h2,
  cases h2 with b h3,
  use [b, a],
  exact h3,
end

-- 10ª demostración
example :
  (∃ x, ∃ y, P x y) → (∃ y, ∃ x, P x y) :=
begin
  intro h1,
  rcases h1 with ⟨a, b, h2⟩,
  use [b, a],
  exact h2,
end

-- 11ª demostración
example :
  (∃ x, ∃ y, P x y) → (∃ y, ∃ x, P x y) :=
begin
  intro h1,
  rcases h1 with ⟨a, b, h2⟩,
  exact ⟨b, a, h2⟩,
end

-- 12ª demostración
example :
  (∃ x, ∃ y, P x y) → (∃ y, ∃ x, P x y) :=
begin
  rintro ⟨a, b, h2⟩,
  exact ⟨b, a, h2⟩,
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

-- ----------------------------------------------------
-- Ej. 2. Demostrar que
--    ∃x∃yP(x,y) ↔ ∃y∃xP(x,y)
-- ----------------------------------------------------

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
