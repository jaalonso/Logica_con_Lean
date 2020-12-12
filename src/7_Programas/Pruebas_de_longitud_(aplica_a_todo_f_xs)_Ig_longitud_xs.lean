-- Pruebas de la relación entre length y map
-- =========================================

import data.nat.basic
open nat
open list

variables {α : Type*} {β : Type*}
variable  (x : α)
variables (xs : list α)

-- ----------------------------------------------------
-- Nota. Se usarán la función longitud y sus
-- propiedades estudiadas anteriormente.
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

-- ----------------------------------------------------
-- Ejercicio 3. Definir la función
--    aplica : (α → β) → list α → 'b list
-- tal que (aplica f xs) es la lista obtenida
-- aplicando la función f a los elementos de xs. Por
-- ejemplo,
--    aplica (λx, 2*x) [3,2,5] = [6,4,10]
--    aplica ((*) 2)   [3,2,5] = [6,4,10]
--    aplica ((+) 2)   [3,2,5] = [5,4,7]
-- ----------------------------------------------------

def aplica : (α → β) → list α → list β
| f []        := []
| f (x :: xs) := (f x) :: aplica f xs

-- #eval aplica (λx, 2*x) [3,2,5]
-- #eval aplica ((*) 2) [3,2,5]
-- #eval aplica ((+) 2) [3,2,5]

-- ----------------------------------------------------
-- Ejercicio 4. Demostrar los siguientes lemas
-- + aplica_nil :
--      aplica f [] = []
-- + aplica_cons :
--      aplica f (x :: xs) = (f x) :: aplica f xs
-- ----------------------------------------------------

@[simp]
lemma aplica_nil
  (f : α → β)
  : aplica f [] = [] :=
rfl

@[simp]
lemma aplica_cons
  (f : α → β)
  : aplica f (x :: xs) = (f x) :: aplica f xs :=
rfl

-- ----------------------------------------------------
-- Ejercicio 1. (p. 48) Demostrar que
--    longitud (aplica f xs) = longitud xs
-- ----------------------------------------------------

-- 1ª demostración
example
  (f : α → β)
  : longitud (aplica f xs) = longitud xs :=
begin
  induction xs with a as HI,
  { rw aplica_nil,
    rw longitud_nil,
    rw longitud_nil, },
  { rw aplica_cons,
    rw longitud_cons,
    rw HI,
    rw longitud_cons, },
end

-- 2ª demostración
example
  (f : α → β)
  : longitud (aplica f xs) = longitud xs :=
begin
  induction xs with a as HI,
  { calc longitud (aplica f [])
         = longitud []                   : by rw aplica_nil
     ... = 0                             : by rw longitud_nil
     ... = longitud []                   : by rw longitud_nil, },
  { calc longitud (aplica f (a :: as))
         = longitud (f a :: aplica f as) : by rw aplica_cons
     ... = longitud (aplica f as) + 1    : by rw longitud_cons
     ... = longitud as + 1               : by rw HI
     ... = longitud (a :: as)            : by rw longitud_cons, },
end

-- 3ª demostración
example
  (f : α → β)
  : longitud (aplica f xs) = longitud xs :=
begin
  induction xs with x xs HI,
  { simp, },
  { simp [HI], },
end

-- 4ª demostración
example
  (f : α → β)
  : longitud (aplica f xs) = longitud xs :=
by induction xs ; simp [*]

-- 5ª demostración
lemma longitud_aplica
  (f : α → β)
  : ∀ xs, longitud (aplica f xs) = longitud xs
| []        := by simp
| (a :: as) := by simp [longitud_aplica as]

-- Comentarios sobre las función map:
-- + Es equivalente a la función aplica.
-- + Para usarla hay que importar la librería
--   data.list.basic y abrir el espacio de nombre
--   list escribiendo al principio del fichero
--      import data.list.basic
--      open list
-- + Se puede evaluar. Por ejemplo,
--      #eval map (λx, 2*x) [3,2,5]
--      #eval map ((*) 2) [3,2,5]
--      #eval map ((+) 2) [3,2,5]
-- + Se puede demostrar. Por ejemplo,
example
  (f : α → β)
  : length (map f xs) = length xs :=
by induction xs ; simp [*]

example
  (f : α → β)
  : length (map f xs) = length xs :=
-- by library_search
length_map f xs

example
  (f : α → β)
  : length (map f xs) = length xs :=
by simp
