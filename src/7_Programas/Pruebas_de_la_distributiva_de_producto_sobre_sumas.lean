-- Pruebas de la distributiva del producto sobre sumas
-- ===================================================

import data.nat.basic
open nat
open list

variables {α : Type*} {β : Type*}
variable  x : α
variables (xs : list α)
variable  n : ℕ
variable  ns : list ℕ

-- ----------------------------------------------------
-- Ejercicio 1. Definir la función
--    suma : list ℕ → ℕ
-- tal que (suma xs) es la suma de los elementos de
-- xs. Por ejemplo,
--    suma [3,2,5] = 10
-- ----------------------------------------------------

def suma : list ℕ → ℕ
| []        := 0
| (n :: ns) := n + suma ns

-- #eval suma [3,2,5]

-- ----------------------------------------------------
-- Ejercicio 2. Demostrar los siguientes lemas
-- + suma_nil :
--      suma ([] : list ℕ) = 0 :=
-- + suma_cons :
--      suma (n :: ns) = n + suma ns :=
-- ----------------------------------------------------

@[simp]
lemma suma_nil :
  suma ([] : list ℕ) = 0 :=
rfl

@[simp]
lemma suma_cons :
  suma (n :: ns) = n + suma ns :=
rfl

-- ----------------------------------------------------
-- Ejercicio 3. Definir la función
--    aplica_a_todos : (α → β) → list α → 'b list
-- tal que (aplica_a_todos f xs) es la lista obtenida
-- aplicando la función f a los elementos de xs. Por
-- ejemplo,
--    aplica_a_todos (λx, 2*x) [3,2,5] = [6,4,10]
--    aplica_a_todos ((*) 2)   [3,2,5] = [6,4,10]
--    aplica_a_todos ((+) 2)   [3,2,5] = [5,4,7]
-- ----------------------------------------------------

def aplica_a_todos : (α → β) → list α → list β
| f []        := []
| f (x :: xs) := (f x) :: aplica_a_todos f xs

-- #eval aplica_a_todos (λx, 2*x) [3,2,5]
-- #eval aplica_a_todos ((*) 2) [3,2,5]
-- #eval aplica_a_todos ((+) 2) [3,2,5]

-- ----------------------------------------------------
-- Ejercicio 4. Demostrar los siguientes lemas
-- + aplica_a_todos_nil :
--      aplica_a_todos ([] : list ℕ) = 0 :=
-- + aplica_a_todos_cons :
--      aplica_a_todos (n :: ns) = n + aplica_a_todos ns :=
-- ----------------------------------------------------

@[simp]
lemma aplica_a_todos_nil
  (f : α → β)
  : aplica_a_todos f [] = [] :=
rfl

@[simp]
lemma aplica_a_todos_cons
  (f : α → β)
  : aplica_a_todos f (x :: xs) =
    (f x) :: aplica_a_todos f xs :=
rfl

-- ----------------------------------------------------
-- Ejercicio 5. (p. 45) Demostrar que
--    suma (aplica_a_todos (λ x, 2*x) ns) = 2 * (suma ns)
-- ----------------------------------------------------

-- 1ª demostración
example :
  suma (aplica_a_todos (λ x, 2*x) ns) = 2 * (suma ns) :=
begin
  induction ns with n ns HI,
  { rw aplica_a_todos_nil,
    rw suma_nil,
    rw mul_zero, },
  { rw aplica_a_todos_cons,
    rw suma_cons,
    rw HI,
    rw suma_cons,
    rw mul_add, },
end

-- 2ª demostración
example :
  suma (aplica_a_todos (λ x, 2*x) ns) = 2 * (suma ns) :=
begin
  induction ns with n ns HI,
  { calc suma (aplica_a_todos (λ (x : ℕ), 2 * x) [])
         = suma []     : by rw aplica_a_todos_nil
     ... = 0           : by rw suma_nil
     ... = 2 * 0       : by rw mul_zero
     ... = 2 * suma [] : by rw suma_nil, },
  { calc suma (aplica_a_todos (λ x, 2 * x) (n :: ns))
         = suma (2 * n :: aplica_a_todos (λ x, 2 * x) ns) : by rw aplica_a_todos_cons
     ... = 2 * n + suma (aplica_a_todos (λ x, 2 * x) ns)  : by rw suma_cons
     ... = 2 * n + 2 * suma ns                            : by rw HI
     ... = 2 * (n + suma ns)                              : by rw mul_add
     ... = 2 * suma (n :: ns)                             : by rw suma_cons, },
end

-- 3ª demostración
example :
  suma (aplica_a_todos (λ x, 2*x) ns) = 2 * (suma ns) :=
by induction ns ; simp [*, mul_add]

-- Comentarios sobre las funciones sum y map:
-- + Es equivalente a la función longitud.
-- + Para usarla hay que importar la librería
--   data.list.basic y abrir el espacio de nombre
--   list escribiendo al principio del fichero
--      import data.list.basic
--      open list
-- + Se puede evaluar. Por ejemplo,
--      #eval sum [3,2,5]
--      #eval map (λx, 2*x) [3,2,5]
--      #eval map ((*) 2) [3,2,5]
--      #eval map ((+) 2) [3,2,5]
