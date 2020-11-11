-- La composición de inyectivas parciales es inyectiva
-- ===================================================

-- ----------------------------------------------------
-- Ej. 1. Sean A un conjunto de elementos de X, B un
-- conjunto de elementos de Y, f una función de X en Y
-- y g una función de Y en Z. Si B contiene a la imagen
-- de A por f, f es inyectiva sobre A y g es inyectiva
-- sobre B, entonces (g ∘ f) es inyectiva sobre A.
-- ----------------------------------------------------

import data.set
open set function

variables {X Y Z : Type}
variable  (A : set X)
variable  (B : set Y)
variable  (f : X → Y)
variable  (g : Y → Z)

-- #reduce maps_to f A B
-- #reduce inj_on f A
-- #reduce inj_on g B

-- 1ª demostración
example
  (h  : maps_to f A B)
  (hf : inj_on f A)
  (hg : inj_on g B)
  : inj_on (g ∘ f) A :=
begin
  intros x1 x1A x2 x2A h1,
  apply hf x1A x2A,
  apply hg,
  { exact h x1A, },
  { exact h x2A, },
  exact h1,
end

-- 2ª demostración
example
  (h  : maps_to f A B)
  (hf : inj_on f A)
  (hg : inj_on g B)
  : inj_on (g ∘ f) A :=
begin
  intros x1 x1A x2 x2A h1,
  apply hf x1A x2A,
  apply hg (h x1A) (h x2A),
  exact h1,
end

-- 3ª demostración
example
  (h  : maps_to f A B)
  (hf : inj_on f A)
  (hg : inj_on g B)
  : inj_on (g ∘ f) A :=
begin
  intros x1 x1A x2 x2A h1,
  apply hf x1A x2A,
  exact (hg (h x1A) (h x2A)) h1,
end

-- 4ª demostración
example
  (h  : maps_to f A B)
  (hf : inj_on f A)
  (hg : inj_on g B)
  : inj_on (g ∘ f) A :=
begin
  intros x1 x1A x2 x2A h1,
  exact hf x1A x2A (hg (h x1A) (h x2A) h1),
end

-- 5ª demostración
example
  (h  : maps_to f A B)
  (hf : inj_on f A)
  (hg : inj_on g B)
  : inj_on (g ∘ f) A :=
λ x1 x1A x2 x2A h1, hf x1A x2A (hg (h x1A) (h x2A) h1)

-- 6ª demostración
example
  (h  : maps_to f A B)
  (hf : inj_on f A)
  (hg : inj_on g B)
  : inj_on (g ∘ f) A :=
assume x1 : X,
assume x1A : x1 ∈ A,
assume x2 : X,
assume x2A : x2 ∈ A,
have fx1B : f x1 ∈ B, from h x1A,
have fx2B : f x2 ∈ B, from h x2A,
assume h1 : g (f x1) = g (f x2),
have h2 : f x1 = f x2, from hg fx1B fx2B h1,
show x1 = x2, from hf x1A x2A h2

-- 7ª demostración
example
  (h  : maps_to f A B)
  (hf : inj_on f A)
  (hg : inj_on g B)
  : inj_on (g ∘ f) A :=
-- by library_search
inj_on.comp hg hf h
