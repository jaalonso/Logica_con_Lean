-- Pruebas de longitud (aplica a todo f xs) = longitud xs
-- ======================================================

import data.nat.basic
open nat
open list

variables {α : Type*} {β : Type*}
variable  x : α
variables (xs : list α)

-- ----------------------------------------------------
-- Nota. Se usarán las funciones longitud, aplica_a_todos
--  y sus propiedades estudiadas anteriormente.
-- ----------------------------------------------------

def longitud : list α → nat
| []        := 0
| (x :: xs) := longitud xs + 1

@[simp]
lemma longitud_nil :
  longitud ([] : list α) = 0 :=
rfl

@[simp]
lemma longitud_cons :
  longitud (x :: xs) = longitud xs + 1 :=
rfl

def aplica_a_todos : (α → β) → list α → list β
| f []        := []
| f (x :: xs) := (f x) :: aplica_a_todos f xs


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
-- Ejercicio 1. (p. 48) Demostrar que
--    longitud (aplica_a_todos f xs) = longitud xs
-- ----------------------------------------------------

-- 1ª demostración
example
  (f : α → β)
  : longitud (aplica_a_todos f xs) = longitud xs :=
begin
  induction xs with x xs HI,
  { rw aplica_a_todos_nil,
    rw longitud_nil,
    rw longitud_nil, },
  { rw aplica_a_todos_cons,
    rw longitud_cons,
    rw HI,
    rw longitud_cons, },
end

-- 2ª demostración
example
  (f : α → β)
  : longitud (aplica_a_todos f xs) = longitud xs :=
begin
  induction xs with x xs HI,
  { calc longitud (aplica_a_todos f [])
         = longitud []                           : by rw aplica_a_todos_nil
     ... = 0                                     : by rw longitud_nil
     ... = longitud []                           : by rw longitud_nil, },
  { calc longitud (aplica_a_todos f (x :: xs))
         = longitud (f x :: aplica_a_todos f xs) : by rw aplica_a_todos_cons
     ... = longitud (aplica_a_todos f xs) + 1    : by rw longitud_cons
     ... = longitud xs + 1                       : by rw HI
     ... = longitud (x :: xs)                    : by rw longitud_cons, },
end

-- 3ª demostración
example
  (f : α → β)
  : longitud (aplica_a_todos f xs) = longitud xs :=
by induction xs ; simp [*]

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
-- + Se puede demostrar. Por ejemplo,
--      example
--        (f : α → β)
--        : length (map f xs) = length xs :=
--      by induction xs ; simp [*]
--
--      example
--        (f : α → β)
--        : length (map f xs) = length xs :=
--      -- by library_search
--      length_map f xs
