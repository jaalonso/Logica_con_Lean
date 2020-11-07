-- Pruebas de P ∨ Q ⊢ Q ∨ P
-- ========================

import tactic

variables (P Q R : Prop)

-- Ej. 1. Demostrar
--    P ∨ Q ⊢ Q ∨ P

-- 1ª demostración
example
  (h1 : P ∨ Q)
  : Q ∨ P :=
or.elim h1 
  ( assume h2 : P,
    show Q ∨ P,
      from or.inr h2 )
  ( assume h3 : Q,
    show Q ∨ P,
      from or.inl h3 )

-- 2ª demostración
example
  (h1 : P ∨ Q)
  : Q ∨ P :=
or.elim h1 
  ( λ h, or.inr h )
  ( λ h, or.inl h )

-- 3ª demostración
example
  (h1 : P ∨ Q)
  : Q ∨ P :=
or.elim h1 or.inr or.inl

example
  (h1 : P ∨ Q)
  : Q ∨ P :=
h1.elim or.inr or.inl

-- 4ª demostración
example
  (h1 : P ∨ Q)
  : Q ∨ P :=
or.rec or.inr or.inl h1

-- 5ª demostración
example
  (h1 : P ∨ Q)
  : Q ∨ P :=
or.swap h1

-- 6ª demostración
example
  (h1 : P ∨ Q)
  : Q ∨ P :=
begin
  cases h1 with h2 h3,
  { exact or.inr h2, },
  { exact or.inl h3, },
end 

-- 7ª demostración
example
  (P ∨ Q)
  : Q ∨ P :=
begin
  cases ‹P ∨ Q›, 
  { exact or.inr ‹P›, },
  { exact or.inl ‹Q›, },
end 

-- 8ª demostración
example
  (h1 : P ∨ Q)
  : Q ∨ P :=
begin
  cases h1 with h2 h3,
  { right, 
    exact h2, },
  { left, 
    exact h3, },
end 

-- 9ª demostración
example
  (h1 : P ∨ Q)
  : Q ∨ P :=
by tauto

-- 10ª demostración
example
  (h1 : P ∨ Q)
  : Q ∨ P :=
by finish

-- ----------------------------------------------------
-- Ej. 1. Demostrar
--    P ∨ Q ⊢ Q ∨ P
-- ----------------------------------------------------

-- 1ª demostración
example
  (h1 : P ∨ Q)
  : Q ∨ P :=
or.elim h1 
  ( assume h2 : P,
    show Q ∨ P,
      from or.inr h2 )
  ( assume h3 : Q,
    show Q ∨ P,
      from or.inl h3 )

-- 2ª demostración
example
  (h1 : P ∨ Q)
  : Q ∨ P :=
or.elim h1 
  ( λ h, or.inr h )
  ( λ h, or.inl h )

-- 3ª demostración
example
  (h1 : P ∨ Q)
  : Q ∨ P :=
or.elim h1 or.inr or.inl

example
  (h1 : P ∨ Q)
  : Q ∨ P :=
h1.elim or.inr or.inl

-- 4ª demostración
example
  (h1 : P ∨ Q)
  : Q ∨ P :=
or.rec or.inr or.inl h1

-- 5ª demostración
example
  (h1 : P ∨ Q)
  : Q ∨ P :=
or.swap h1

-- 6ª demostración
example
  (h1 : P ∨ Q)
  : Q ∨ P :=
begin
  cases h1 with h2 h3,
  { exact or.inr h2, },
  { exact or.inl h3, },
end 

-- 7ª demostración
example
  (P ∨ Q)
  : Q ∨ P :=
begin
  cases ‹P ∨ Q›, 
  { exact or.inr ‹P›, },
  { exact or.inl ‹Q›, },
end 

-- 8ª demostración
example
  (h1 : P ∨ Q)
  : Q ∨ P :=
begin
  cases h1 with h2 h3,
  { right, 
    exact h2, },
  { left, 
    exact h3, },
end 

-- 9ª demostración
example
  (h1 : P ∨ Q)
  : Q ∨ P :=
by tauto

-- 10ª demostración
example
  (h1 : P ∨ Q)
  : Q ∨ P :=
by finish

-- ----------------------------------------------------
-- Ej. 1. Demostrar
--    Q → R ⊢ P ∨ Q → P ∨ R
-- ----------------------------------------------------

-- 1ª demostración
example
  (h1 : Q → R)
  : P ∨ Q → P ∨ R :=
assume h2 : P ∨ Q,
or.elim h2 
  ( assume h3 : P,
    show P ∨ R, 
      from or.inl h3 )
  ( assume h4 : Q,
    have h5 : R := h1 h4,
    show P ∨ R,
      from or.inr h5 )

-- 2ª demostración
example
  (h1 : Q → R)
  : P ∨ Q → P ∨ R :=
assume h2 : P ∨ Q,
or.elim h2 
  ( assume h3 : P, or.inl h3 )
  ( assume h4 : Q, 
    show P ∨ R,
      from or.inr (h1 h4) )

-- 3ª demostración
example
  (h1 : Q → R)
  : P ∨ Q → P ∨ R :=
assume h2 : P ∨ Q,
or.elim h2 
  ( assume h3 : P, or.inl h3 )
  ( assume h4 : Q, or.inr (h1 h4) )

-- 4ª demostración
example
  (h1 : Q → R)
  : P ∨ Q → P ∨ R :=
assume h2 : P ∨ Q,
or.elim h2 
  ( λ h3, or.inl h3 )
  ( λ h4, or.inr (h1 h4) )

-- 5ª demostración
example
  (h1 : Q → R)
  : P ∨ Q → P ∨ R :=
assume h2 : P ∨ Q,
or.elim h2 
  or.inl
  ( λ h, or.inr (h1 h) )

-- 6ª demostración
example
  (h1 : Q → R)
  : P ∨ Q → P ∨ R :=
λ h2, or.elim h2 or.inl (λ h, or.inr (h1 h))

example
  (h1 : Q → R)
  : P ∨ Q → P ∨ R :=
λ h2, h2.elim or.inl (λ h, or.inr (h1 h))

-- 7ª demostración
example
  (h1 : Q → R)
  : P ∨ Q → P ∨ R :=
or.imp_right h1

-- 8ª demostración
example
  (h1 : Q → R)
  : P ∨ Q → P ∨ R :=
begin
  intro h2,
  cases h2 with h3 h4,
  { exact or.inl h3, },
  { exact or.inr (h1 h4), },
end  

-- 9ª demostración
example
  (h1 : Q → R)
  : P ∨ Q → P ∨ R :=
begin
  intro h2,
  cases h2 with h3 h4,
  { left, 
    exact h3, },
  { right,
    exact (h1 h4), },
end  

-- 10ª demostración
example
  (h1 : Q → R)
  : P ∨ Q → P ∨ R :=
begin
  rintro (h3 | h4),
  { left, 
    exact h3, },
  { right,
    exact (h1 h4), },
end  

-- 11ª demostración
example
  (h1 : Q → R)
  : P ∨ Q → P ∨ R :=
by tauto

-- 12ª demostración
example
  (h1 : Q → R)
  : P ∨ Q → P ∨ R :=
by finish

-- ----------------------------------------------------
-- Ej. 1. Demostrar
--    ¬P ∨ Q ⊢ P → Q
-- ----------------------------------------------------

-- 1ª demostración
example 
  (h1 : ¬P ∨ Q)
  : P → Q :=
assume h2 : P,
or.elim h1 
  ( assume h3 : ¬P,
    have h4 : false,
      from h3 h2,
    show Q, 
      from false.elim h4) 
  ( assume h5 : Q,
    show Q, from h5)

-- 2ª demostración
example 
  (h1 : ¬P ∨ Q)
  : P → Q :=
assume h2 : P,
or.elim h1 
  ( assume h3 : ¬P,
    have h4 : false,
      from h3 h2,
    show Q, 
      from false.elim h4) 
  ( assume h5 : Q, h5)

-- 3ª demostración
example 
  (h1 : ¬P ∨ Q)
  : P → Q :=
assume h2 : P,
or.elim h1 
  ( assume h3 : ¬P,
    have h4 : false,
      from h3 h2,
    show Q, 
      from false.elim h4) 
  ( λ h5, h5)

-- 4ª demostración
example 
  (h1 : ¬P ∨ Q)
  : P → Q :=
assume h2 : P,
or.elim h1 
  ( assume h3 : ¬P,
    have h4 : false,
      from h3 h2,
    show Q, 
      from false.elim h4) 
  id
    
-- 5ª demostración
example 
  (h1 : ¬P ∨ Q)
  : P → Q :=
assume h2 : P,
or.elim h1 
  ( assume h3 : ¬P,
    show Q, 
      from false.elim (h3 h2)) 
  id
        
-- 6ª demostración
example 
  (h1 : ¬P ∨ Q)
  : P → Q :=
assume h2 : P,
or.elim h1 
  ( assume h3 : ¬P, false.elim (h3 h2)) 
  id
        
-- 7ª demostración
example 
  (h1 : ¬P ∨ Q)
  : P → Q :=
assume h2 : P,
or.elim h1 
  ( λ h3, false.elim (h3 h2)) 
  id
        
-- 8ª demostración
example 
  (h1 : ¬P ∨ Q)
  : P → Q :=
λ h2, or.elim h1 (λ h3, false.elim (h3 h2)) id

example 
  (h1 : ¬P ∨ Q)
  : P → Q :=
λ h2, h1.elim (λ h3, false.elim (h3 h2)) id

example 
  (h1 : ¬P ∨ Q)
  : P → Q :=
λ h2, h1.elim (λ h3, (h3 h2).elim) id

-- 9ª demostración
example 
  (h1 : ¬P ∨ Q)
  : P → Q :=
imp_iff_not_or.mpr h1

-- 10ª demostración
example 
  (h1 : ¬P ∨ Q)
  : P → Q :=
begin
  intro h2,
  cases h1 with h3 h4,
  { apply false.rec,
    exact h3 h2, },
  { exact h4, },
end

-- 11ª demostración
example 
  (h1 : ¬P ∨ Q)
  : P → Q :=
begin
  intro h2,
  cases h1 with h3 h4,
  { exact false.elim (h3 h2), },
  { exact h4, },
end

-- 12ª demostración
example 
  (h1 : ¬P ∨ Q)
  : P → Q :=
begin
  intro h2,
  cases h1 with h3 h4,
  { exfalso,
    exact h3 h2, },
  { exact h4, },
end

-- 13ª demostración
example 
  (h1 : ¬P ∨ Q)
  : P → Q :=
by tauto

-- 14ª demostración
example 
  (h1 : ¬P ∨ Q)
  : P → Q :=
by finish
