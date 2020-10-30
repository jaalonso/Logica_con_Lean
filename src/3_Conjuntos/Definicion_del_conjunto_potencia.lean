-- Definición del conjunto potencia
-- ================================

variable {U : Type}

def powerset (A : set U) : set (set U) := 
  {B : set U | B ⊆ A}

example 
  (A B : set U) 
  (h : B ∈ powerset A) 
  : B ⊆ A :=
h
