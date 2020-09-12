-- Reglas de la conjunción
-- ================================================

-- ------------------------------------------------
-- Demostrar que
--    P ∧ Q, R ⊢ Q ∧ R
-- ------------------------------------------------

import tactic            

variables (P Q R : Prop)

-- 1ª demostración
-- ===============

example  
  (hPQ : P ∧ Q)
  (hR : R)
  : Q ∧ R :=
have hQ : Q, 
  from and.right hPQ,
show Q ∧ R,  
  from and.intro hQ hR

-- 2ª demostración
-- ===============

example  
  (hPQ : P ∧ Q)
  (hR : R)
  : Q ∧ R :=
have hQ : Q, 
  from hPQ.right,
show Q ∧ R,  
  from ⟨hQ, hR⟩

-- 3ª demostración
-- ===============

example  
  (hPQ : P ∧ Q)
  (hR : R)
  : Q ∧ R :=
have hQ : Q, 
  from hPQ.2,
show Q ∧ R,  
  from ⟨hQ, hR⟩

-- 4ª demostración
-- ===============

example  
  (hPQ : P ∧ Q)
  (hR : R)
  : Q ∧ R :=
have hQ : Q :=
  hPQ.2,
show Q ∧ R,  
  from ⟨hQ, hR⟩

-- 5ª demostración
-- ===============

example  
  (hPQ : P ∧ Q)
  (hR : R)
  : Q ∧ R :=
show Q ∧ R,  
  from ⟨hPQ.2, hR⟩

-- 6ª demostración
-- ===============

example  
  (hPQ : P ∧ Q)
  (hR : R)
  : Q ∧ R :=
⟨hPQ.2, hR⟩

-- 7ª demostración
-- ===============

example  
  (hPQ : P ∧ Q)
  (hR : R)
  : Q ∧ R :=
begin
  split,
  { cases hPQ with hP hQ,
    clear hP,
    exact hQ, },
  { exact hR, },
end

-- 8ª demostración
-- ===============

example  
  (hPQ : P ∧ Q)
  (hR : R)
  : Q ∧ R :=
begin
  split,
  { cases hPQ,
    assumption, },
  { assumption, },
end

-- 9ª demostración
-- ===============

example  
  (hPQ : P ∧ Q)
  (hR : R)
  : Q ∧ R :=
by tauto

-- 10ª demostración
-- ===============

example  
  (hPQ : P ∧ Q)
  (hR : R)
  : Q ∧ R :=
by finish
