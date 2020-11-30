-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    (p ∧ q) ∧ r ⊢ p ∧ (q ∧ r)
-- ----------------------------------------------------

import tactic
variables (p q r : Prop)

-- 1ª demostración
example
  (Hpqr : (p ∧ q) ∧ r)
  : p ∧ (q ∧ r) :=
begin
  rcases Hpqr with ⟨⟨Hp, Hq⟩, Hr⟩,
  exact ⟨Hp, ⟨Hq, Hr⟩⟩,
end

-- 2ª demostración
example
  : (p ∧ q) ∧ r → p ∧ (q ∧ r) :=
begin
  rintros ⟨⟨Hp, Hq⟩, Hr⟩,
  exact ⟨Hp, ⟨Hq, Hr⟩⟩,
end

-- 3ª demostración
example
  : (p ∧ q) ∧ r → p ∧ (q ∧ r) :=
λ ⟨⟨Hp, Hq⟩, Hr⟩, ⟨Hp, ⟨Hq, Hr⟩⟩

-- 4ª demostración
example
  (Hpqr : (p ∧ q) ∧ r)
  : p ∧ (q ∧ r) :=
have Hpq : p ∧ q,
  from and.left Hpqr,
have Hr : r,
  from and.right Hpqr,
have Hp : p,
  from and.left Hpq,
have Hq : q,
  from and.right Hpq,
have Hqr : q ∧ r,
  from and.intro Hq Hr,
show p ∧ (q ∧ r),
  from and.intro Hp Hqr

-- 5ª demostración
example
  (Hpqr : (p ∧ q) ∧ r)
  : p ∧ (q ∧ r) :=
-- by library_search
(and_assoc p q).mp Hpqr

-- 6ª demostración
example
  (Hpqr : (p ∧ q) ∧ r)
  : p ∧ (q ∧ r) :=
-- by hint
by tauto

-- 7ª demostración
example
  (Hpqr : (p ∧ q) ∧ r)
  : p ∧ (q ∧ r) :=
by finish
