-- Razonamiento con tipos parametrizados: Pares
-- ============================================

import tactic

variable {α : Type}

-- ----------------------------------------------------
-- Ejercicio 1. Definir el tipo Par de elementos de
-- tipo α como abreviarura del producto cartesiano de
-- α por α.
-- ----------------------------------------------------

abbreviation Par (α : Type) : Type := α × α

-- ----------------------------------------------------
-- Ejercicio 2. Definir ejPar como el par de números
-- enteros (2,5).
-- ----------------------------------------------------

def ejPar : Par ℤ :=
(2,5)

-- ----------------------------------------------------
-- Ejercicio 3. Definir la función
--    multiplica : Par ℤ → ℤ
-- tal que (multiplica p) es el producto de las
-- componentes del par p. Por ejemplo,
--    multiplica (2,5) = 10
-- ----------------------------------------------------

-- 1ª definición
def multiplica : Par ℤ → ℤ
| (x,y) := x*y

-- 2ª definición
def multiplica_2 : Par ℤ → ℤ :=
λ ⟨x,y⟩, x*y

-- #eval multiplica (2,5)
-- Da: 10

-- ----------------------------------------------------
-- Ejercicio 4. Definir la función
--    copia : α → Par α
-- tal que (copia x) es el par formado con dos copias
-- de x. Por ejemplo,
--    copia tt      = (tt, tt)
--    copia (5 : ℤ) = (5, 5)
-- ----------------------------------------------------

-- 1ª definición
def copia : α → Par α
| x := (x,x)

-- 2ª definición
def copia_2 : α → Par α :=
λ x, (x,x)

-- #eval copia (5 : ℤ)
-- Da: (5,5)
--
-- #eval copia tt
-- Da: (tt, tt)

-- ----------------------------------------------------
-- Ejercicio . Demostrar que, para todo entero x,
--    multiplica (copia x) = x^2
-- ----------------------------------------------------

-- 1ª demostración
example
  (x : ℤ)
  : multiplica (copia x) = x^2 :=
calc multiplica (copia x)
     = multiplica (x, x)  :by rw copia
 ... = x*x                :by rw multiplica
 ... = x^2                :by rw ← pow_two

-- 2ª demostración
attribute [simp] copia multiplica pow_two

example
  (x : ℤ)
  : multiplica (copia x) = x^2 :=
calc multiplica (copia x)
     = multiplica (x, x)  :by simp
 ... = x*x                :by simp
 ... = x^2                :by simp

-- 3ª demostración
example
  (x : ℤ)
  : multiplica (copia x) = x^2 :=
by simp
