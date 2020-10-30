-- Unión e intersección de familias de conjuntos
-- =============================================

-- ----------------------------------------------------
-- Ej. 1. Declarar I y U como variables de tipo.
-- ---------------------------------------------------- 

variables {I U : Type}

-- ----------------------------------------------------
-- Ej. 2. Definir la función
--    Union : (I → set U) → set U
-- tal que (Union A) es la unión de de los conjuntos de
-- la familia A.
-- ---------------------------------------------------- 

def Union (A : I → set U) : set U := 
  { x | ∃ i : I, x ∈ A i }

-- ----------------------------------------------------
-- Ej. 3. Definir la función
--    Inter : (I → set U) → set U
-- tal que (Inter A) es la intersección de de los 
-- conjuntos de la familia A.
-- ---------------------------------------------------- 

def Inter (A : I → set U) : set U := 
  { x | ∀ i : I, x ∈ A i }

-- ----------------------------------------------------
-- Ej. 4. Declarar
-- + x como una variable sobre U y
-- + A como una variable sobre familas de conjuntos de
--   U con índice en A.
-- ----------------------------------------------------

variable x : U
variable (A : I → set U)

-- ----------------------------------------------------
-- Ej. 5. Demostrar que
--    x ∈ Union A ⊢ ∃ i, x ∈ A i
-- ----------------------------------------------------

example 
  (h : x ∈ Union A)     
  : ∃ i, x ∈ A i := 
h

-- ----------------------------------------------------
-- Ej. 6. Demostrar que
--    x ∈ x ∈ Inter A ⊢ ∀ i, x ∈ A i
-- ----------------------------------------------------

example 
  (h : x ∈ Inter A) 
  : ∀ i, x ∈ A i := 
h

-- ----------------------------------------------------
-- Ej 7. Usar (⋃ i, A i) como notación para (Union A).
-- ----------------------------------------------------

notation `⋃` binders `, ` r:(scoped f, Union f) := r

-- ----------------------------------------------------
-- Ej 8. Usar (⋂ i, A i) como notación para (Inter A).
-- ----------------------------------------------------

notation `⋂` binders `, ` r:(scoped f, Inter f) := r


-- ----------------------------------------------------
-- Ej. 9. Demostrar que
--    x ∈ ⋃ i, A i ⊢ ∃ i, x ∈ A i
-- ----------------------------------------------------

example 
  (h : x ∈ ⋃ i, A i)     
  : ∃ i, x ∈ A i := 
h

-- ----------------------------------------------------
-- Ej. 10. Demostrar que
--    x ∈ x ∈ ⋂ i, A i ⊢ ∀ i, x ∈ A i
-- ----------------------------------------------------

example 
  (h : x ∈ ⋂ i, A i) 
  : ∀ i, x ∈ A i := 
h


