-- Razonamiento con tipos enumerados con constructores con parámetros
-- ==================================================================

import data.real.basic

-- ----------------------------------------------------
-- Ejercicio 1. Definir el tipo de datos Figuras con
-- tres constructores: Triangulo (con su base y altura),
-- Circulo (con su radio) y Rectangulo (con su base y
-- altura).
-- ----------------------------------------------------

inductive Figura : Type
| Triangulo  : ℚ → ℚ → Figura
| Circulo    : ℚ → Figura
| Rectangulo : ℚ → ℚ → Figura

-- ----------------------------------------------------
-- Ejercicio 2. Abrir el espacio de nombre de Figura
-- ----------------------------------------------------

namespace Figura

-- ----------------------------------------------------
-- Ejercicio 3. Definir la función
--    cuadrado : ℚ -> Figura
-- tal que (cuadrado n) es el cuadrado de lado n.
-- ----------------------------------------------------

@[simp]
def cuadrado : ℚ -> Figura
| n := Rectangulo n n

-- ----------------------------------------------------
-- Ejercicio 4. Definir pi como 3.1415927
-- ----------------------------------------------------

def pi : ℚ := 3.1415927

-- ----------------------------------------------------
-- Ejercicio 5. Definir la función
--    area : Figura → ℚ
-- tal que (area f) es el área de la figura f. Por
-- ejemplo,
--    area (Circulo 1)      = 31415927/10000000
--    area (Circulo 10)     = 31415927/100000
--    area (Triangulo 2 5)  = 5
--    area (Rectangulo 2 5) = 10
--    area (cuadrado 3)     = 9
-- ----------------------------------------------------

@[simp]
def area : Figura → ℚ
| (Triangulo b h)  := b*h/2
| (Circulo r)      := pi*r^2
| (Rectangulo x y) := x*y

-- #eval area (Circulo 1)      -- = 31415927/10000000
-- #eval area (Circulo 10)     -- = 31415927/100000
-- #eval area (Triangulo 2 5)  -- = 5
-- #eval area (Rectangulo 2 5) -- = 10
-- #eval area (cuadrado 3)     -- = 9

-- ----------------------------------------------------
-- Ejercicio 6. Declarar x como una variable sobre los
-- números racionales
-- ----------------------------------------------------

variable (x : ℚ)

-- ----------------------------------------------------
-- Ejercicio 7. Demostrar que
--    area (cuadrado x) = x^2
-- ----------------------------------------------------

-- 1ª demostración
example :
  area (cuadrado x) = x^2 :=
calc area (cuadrado x)
     = area (Rectangulo x x) :by simp [cuadrado]
 ... = x*x                   :by simp [area]
 ... = x^2                   :by simp [pow_two]

-- 2ª demostración
example :
  area (cuadrado x) = x^2 :=
calc area (cuadrado x)
     = area (Rectangulo x x) :by simp
 ... = x*x                   :by simp
 ... = x^2                   :by simp [pow_two]

-- 3ª demostración
example :
  area (cuadrado x) = x^2 :=
by simp [pow_two]

-- 4ª demostración
example :
  area (cuadrado x) = x^2 :=
by simp ; ring

-- ----------------------------------------------------
-- Ejercicio 8. Cerrar el espacio de nombre Figura.
-- ----------------------------------------------------

end Figura
