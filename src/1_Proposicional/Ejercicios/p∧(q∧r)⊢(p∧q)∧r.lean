-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    p ∧ (q ∧ r) ⊢ (p ∧ q) ∧ r
-- ----------------------------------------------------

import tactic
variables (p q r : Prop)

-- 1ª demostración
example
  (Hpqr : p ∧ (q ∧ r))
  : (p ∧ q) ∧ r :=
begin
  cases Hpqr with Hp Hqr,
  cases Hqr with Hq Hr,
  split,
  { split,
    { exact Hp, },
    { exact Hq, }},
  { exact Hr, },
end

-- 2ª demostración
example
  (Hpqr : p ∧ (q ∧ r))
  : (p ∧ q) ∧ r :=
begin
  cases Hpqr with Hp Hqr,
  cases Hqr with Hq Hr,
  split,
  { exact ⟨Hp, Hq⟩, },
  { exact Hr, },
end

-- 3ª demostración
example
  (Hpqr : p ∧ (q ∧ r))
  : (p ∧ q) ∧ r :=
begin
  cases Hpqr with Hp Hqr,
  cases Hqr with Hq Hr,
  exact ⟨⟨Hp, Hq⟩, Hr⟩,
end

-- 4ª demostración
example
  (Hpqr : p ∧ (q ∧ r))
  : (p ∧ q) ∧ r :=
begin
  rcases Hpqr with ⟨Hp, ⟨Hq, Hr⟩⟩,
  exact ⟨⟨Hp, Hq⟩, Hr⟩,
end

-- 5ª demostración
example :
  p ∧ (q ∧ r) → (p ∧ q) ∧ r :=
begin
  rintros ⟨Hp, ⟨Hq, Hr⟩⟩,
  exact ⟨⟨Hp, Hq⟩, Hr⟩,
end

-- 6ª demostración
example :
  p ∧ (q ∧ r) → (p ∧ q) ∧ r :=
λ ⟨Hp, ⟨Hq, Hr⟩⟩, ⟨⟨Hp, Hq⟩, Hr⟩

-- 7ª demostración
example
  (Hpqr : p ∧ (q ∧ r))
  : (p ∧ q) ∧ r :=
have Hp : p,
  from and.left Hpqr,
have Hqr : q ∧ r,
  from and.right Hpqr,
have Hq : q,
  from and.left Hqr,
have Hr : r,
  from and.right Hqr,
have Hpq : p ∧ q,
  from and.intro Hp Hq,
show (p ∧ q) ∧ r,
  from and.intro Hpq Hr

-- 8ª demostración
example
  (Hpqr : p ∧ (q ∧ r))
  : (p ∧ q) ∧ r :=
-- by library_search
(and_assoc p q).mpr Hpqr

-- 9ª demostración
example
  (Hpqr : p ∧ (q ∧ r))
  : (p ∧ q) ∧ r :=
-- by hint
by tauto

-- 10ª demostración
example
  (Hpqr : p ∧ (q ∧ r))
  : (p ∧ q) ∧ r :=
by finish
