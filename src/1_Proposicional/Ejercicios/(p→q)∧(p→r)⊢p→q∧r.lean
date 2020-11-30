-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    (p → q) ∧ (p → r) ⊢ p → q ∧ r
-- ----------------------------------------------------

import tactic
variables (p q r : Prop)

-- 1ª demostración
example
  (H : (p → q) ∧ (p → r))
  : p → q ∧ r :=
begin
  cases H with Hpq Hpr,
  intro Hp,
  split,
  { apply Hpq,
    exact Hp, },
  { apply Hpr,
    exact Hp, },
end

-- 2ª demostración
example
  (H : (p → q) ∧ (p → r))
  : p → q ∧ r :=
begin
  cases H with Hpq Hpr,
  intro Hp,
  split,
  { exact Hpq Hp, },
  { exact Hpr Hp, },
end

-- 3ª demostración
example
  (H : (p → q) ∧ (p → r))
  : p → q ∧ r :=
begin
  cases H with Hpq Hpr,
  intro Hp,
  exact ⟨Hpq Hp, Hpr Hp⟩,
end

-- 4ª demostración
example
  : (p → q) ∧ (p → r) → (p → q ∧ r) :=
begin
  rintros ⟨Hpq, Hpr⟩ Hp,
  exact ⟨Hpq Hp, Hpr Hp⟩,
end

-- 5ª demostración
example
  : (p → q) ∧ (p → r) → (p → q ∧ r) :=
λ ⟨Hpq, Hpr⟩ Hp, ⟨Hpq Hp, Hpr Hp⟩

-- 6ª demostración
example
  (H : (p → q) ∧ (p → r))
  : p → q ∧ r :=
have Hpq : p → q,
  from and.left H,
have Hpr : p → r,
  from and.right H,
assume Hp : p,
have Hq : q,
  from Hpq Hp,
have Hr : r,
  from Hpr Hp,
show q ∧ r,
  from and.intro Hq Hr

-- 7ª demostración
example
  (H : (p → q) ∧ (p → r))
  : p → q ∧ r :=
-- by library_search
imp_and_distrib.mpr H

-- 8ª demostración
example
  (H : (p → q) ∧ (p → r))
  : p → q ∧ r :=
-- by hint
by tauto

-- 9ª demostración
example
  (H : (p → q) ∧ (p → r))
  : p → q ∧ r :=
by finish
