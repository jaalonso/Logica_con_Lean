-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    p ∧ q → r ⊢ p → (q → r)
-- ----------------------------------------------------

import tactic
variables (p q r : Prop)

-- 1ª demostración
example
  (H : p ∧ q → r)
  : p → (q → r) :=
begin
  intros Hp Hq,
  apply H,
  split,
  { exact Hp, },
  { exact Hq, },
end

-- 2ª demostración
example
  (H : p ∧ q → r)
  : p → (q → r) :=
begin
  intros Hp Hq,
  apply H,
  exact ⟨Hp, Hq⟩,
end

-- 3ª demostración
example
  (H : p ∧ q → r)
  : p → (q → r) :=
begin
  intros Hp Hq,
  exact H ⟨Hp, Hq⟩,
end

-- 4ª demostración
example
  (H : p ∧ q → r)
  : p → (q → r) :=
λ Hp Hq, H ⟨Hp, Hq⟩

-- 5ª demostración
example
  (H : p ∧ q → r)
  : p → (q → r) :=
assume Hp : p,
show q → r, from
  assume Hq : q,
  have Hpq : p ∧ q,
    from and.intro Hp Hq,
  show r,
    from H Hpq

-- 6ª demostración
example
  (H : p ∧ q → r)
  : p → (q → r) :=
-- by library_search
and_imp.mp H

-- 7ª demostración
example
  (H : p ∧ q → r)
  : p → (q → r) :=
-- by hint
by finish
