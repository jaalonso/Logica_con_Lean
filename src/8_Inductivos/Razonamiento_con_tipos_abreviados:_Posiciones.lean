-- Razonamiento con tipos abreviados: Posiciones
-- =============================================

import tactic

-- ----------------------------------------------------
-- Ejercicio 1. Definir el tipo Pos como una abreviatura
-- de pares de enteros para representar posiciones.
-- ----------------------------------------------------

-- 1ª definición
-- abbreviation Pos : Type := ℤ × ℤ

-- 2ª definición
-- notation `Pos` := ℤ × ℤ

-- 3ª definición
-- local notation `Pos` := ℤ × ℤ

-- 4ª definición
def Pos := ℤ × ℤ

-- ----------------------------------------------------
-- Ejercicio 2. Definir la posición origen.
-- ----------------------------------------------------

def origen : Pos :=
(0,0)

-- ----------------------------------------------------
-- Ejercicio 3. Definir la función
--    izquierda : Pos → Pos
-- tal que (izquierda p) esla posición que se encuentra
-- a la izquierda de p. Por ejemplo,
--    izquierda (3,5) = (2,5)
-- ----------------------------------------------------

-- 1ª definición
@[simp]
def izquierda : Pos → Pos :=
λ ⟨x,y⟩, (x-1,y)

-- 2ª definición
@[simp]
def izquierda_2 : Pos → Pos
| (x,y) := (x-1,y)

-- #eval izquierda (3,5)
-- Da: (2,5)

-- ----------------------------------------------------
-- Ejercicio 4. Definir la función
--    derecha : Pos → Pos
-- tal que (derecha p) esla posición que se encuentra
-- a la derecha de p. Por ejemplo,
--    derecha (3,5) = (4,5)
-- ----------------------------------------------------

-- 1ª definición
@[simp]
def derecha : Pos → Pos :=
λ ⟨x,y⟩, (x+1,y)

-- 2ª definición
@[simp]
def derecha_2 : Pos → Pos
| (x,y) := (x+1,y)

-- #eval derecha (3,5)
-- Da: (4, 5)

-- ----------------------------------------------------
-- Ejercicio 5. Demostrar que para cualquier posición p,
--    izquierda (derecha p) = p
-- ----------------------------------------------------

-- 1ª demostración
lemma izquierda_derecha :
  ∀ p : Pos, izquierda (derecha p) = p
| (x,y) := by calc izquierda (derecha (x, y))
                   = izquierda (x+1, y)       :by simp
               ... = (x+1-1, y)               :by simp
               ... = (x, y)                   :by simp

-- 2ª demostración
lemma izquierda_derecha_2 :
  ∀ p : Pos, izquierda (derecha p) = p :=
λ ⟨x,y⟩, by simp

-- ----------------------------------------------------
-- Ejercicio 6. Definir el tipo Movimiento para
-- representar los movimientos com funciones desde la
-- posición inicial a la final.
-- ----------------------------------------------------

def Movimiento : Type := Pos → Pos
