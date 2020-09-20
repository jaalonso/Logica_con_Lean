-- Pruebas de Q → R ⊢ P ∨ Q → P ∨ R 
-- ================================

-- Ej. 1. Demostrar
--    Q → R ⊢ P ∨ Q → P ∨ R

import tactic

variables (P Q R : Prop)

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
by tauto

-- 10ª demostración
example
  (h1 : Q → R)
  : P ∨ Q → P ∨ R :=
by finish