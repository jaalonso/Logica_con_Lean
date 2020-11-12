-- Definiciones por recursión sobre los naturales
-- ==============================================

-- ----------------------------------------------------
-- Ej. 1. Definir el tipo nat de los números naturales
-- con los constructores zero (para el número cero) y
-- succ (para el sucesor).
-- ----------------------------------------------------

namespace reservado

inductive nat : Type
| zero : nat
| succ : nat → nat

end reservado

-- ----------------------------------------------------
-- Ej. 2. Abrir el espacio de nombre de los números
-- naturales.
-- ----------------------------------------------------

open nat

-- ----------------------------------------------------
-- Ej. 3. Definir la función
--    factorial : ℕ → ℕ
-- tal que (factorial n) es el factorial de n. Por ejemplo,
--    factorial 3 == 6
-- ----------------------------------------------------

-- 1ª definición
def factorial : ℕ → ℕ
| 0        := 1
| (succ n) := (succ n) * factorial n

-- 2ª definición
def factorial2 : ℕ → ℕ
| 0       := 1
| (n + 1) := (n + 1) * factorial2 n

-- ----------------------------------------------------
-- Ej. 4. Calcular el factorial de 3 y de 30.
-- ----------------------------------------------------

-- El cáculo es
--    #eval factorial 3
--    #eval factorial 30

-- ----------------------------------------------------
-- Ej. 5. Demostrar que el factorial de 3 es 6.
-- ----------------------------------------------------

example : factorial 3 = 6 := rfl

-- ----------------------------------------------------
-- Ej. 6. Definir por recurión la función
--    potencia_de_dos : ℕ → ℕ
-- tal que (potencia_de_dos n) es 2^n. Por ejemplo,
-- ----------------------------------------------------

-- 1ª definición
def potencia_de_dos : ℕ → ℕ
| 0        := 1
| (succ n) := 2 * potencia_de_dos n

-- 1ª definición
def potencia_de_dos2 : ℕ → ℕ
| 0       := 1
| (n + 1) := 2 * potencia_de_dos2 n

-- ----------------------------------------------------
-- Ej. 7. Calcular (potencia_de_dos 3) y
-- (potencia_de_dos 10).
-- ----------------------------------------------------

-- El cálculo es
--    #eval potencia_de_dos 3
--    #eval potencia_de_dos 10

-- ----------------------------------------------------
-- Ej. 8. Demostrar que (potencia_de_dos 3) es 8.
-- ----------------------------------------------------

example : potencia_de_dos 3 = 8 := rfl

-- ----------------------------------------------------
-- Ej. 9. Definir la función
--    potencia : ℕ → ℕ → ℕ
-- tal que (potencia m n) es m^n. Por ejemplo,
--    potencia 2 3  =  8
--    potencia 3 2  =  9
-- ----------------------------------------------------

def potencia : ℕ → ℕ → ℕ
| m 0       := 1
| m (n + 1) := potencia m n * m

-- #eval potencia 2 3
-- #eval potencia 3 2

-- #eval pow 2 3
-- #eval pow 3 2

-- #eval 2^3
-- #eval 3^2

-- ----------------------------------------------------
-- Ej. 10. Sean m, n ∈ ℕ. Demostrar,
--    m^0 = 1
--    m^(n+1) = m^n * m
-- ----------------------------------------------------

variables m n : ℕ

-- 1ª demostración
example : m^0 = 1 := nat.pow_zero m

-- 2ª demostración
example : m^0 = 1 := rfl

-- 1ª demostración
example : m^(n+1) = m^n * m := nat.pow_succ m n

-- 2ª demostración
example : m^(n+1) = m^n * m := rfl

-- ----------------------------------------------------
-- Ej. 11. Definir la función
--    fib : ℕ → ℕ
-- tal que (fib n) es el n-ésimo número de Fibonacci.
-- Por ejemplo,
--    fib 4 = 3
--    fib 5 = 5
--    fib 6 = 8
-- ----------------------------------------------------

def fib : ℕ → ℕ
| 0       := 0
| 1       := 1
| (n + 2) := fib (n + 1) + fib n

-- #eval fib 4
-- #eval fib 5
-- #eval fib 6
