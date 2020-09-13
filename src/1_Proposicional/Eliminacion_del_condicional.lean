-- Eliminación del condicional en Lean
-- ===================================

-- Ej. 1. Demostrar que 
--    (P → Q), P ⊢ Q. 

import tactic            
variables (P Q : Prop)   

-- 1ª demostración
example  
  (h1 : P → Q) 
  (h2 : P) 
  : Q :=
begin
  apply h1,
  exact h2,
end 

-- 2ª demostración
example  
  (h1 : P → Q) 
  (h2 : P) 
  : Q :=
begin
  exact h1 h2,
end 

-- 3ª demostración
example  
  (h1 : P → Q) 
  (h2 : P) 
  : Q :=
by exact h1 h2

-- 4ª demostración
example  
  (h1 : P → Q) 
  (h2 : P) 
  : Q :=
h1 h2

-- 5ª demostración
example  
  (h1 : P → Q) 
  (h2 : P) 
  : Q :=
by tauto

-- 6ª demostración
example  
  (h1 : P → Q) 
  (h2 : P) 
  : Q :=
by finish

-- 7ª demostración
example  
  (h1 : P → Q) 
  (h2 : P) 
  : Q :=
by solve_by_elim
