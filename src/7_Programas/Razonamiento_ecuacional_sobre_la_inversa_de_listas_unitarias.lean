-- Razonamiento ecuacional sobre la inversa de listas unitarias
-- ============================================================

import data.list.basic
open list

variable  {α : Type*}
variable  x : α
variables (xs : list α)

-- ----------------------------------------------------
-- Ejercicio 1. Definir, por recursión, la función
--    inversa :: list α → list α
-- tal que (inversa xs) es la lista obtenida
-- invirtiendo el orden de los elementos de xs.
-- Por ejemplo,
--    inversa [3,2,5] = [5,2,3]
-- ----------------------------------------------------

def inversa : list α → list α
| []        := []
| (x :: xs) := inversa xs ++ [x]

-- #eval inversa [3,2,5]

-- ----------------------------------------------------
-- Ejercicio 2. Demostrar los siguientes lemas
-- + inversa_nil :
--     inversa ([] : list α) = []
-- + inversa_cons :
--     inversa (x :: xs) = inversa xs ++ [x]
-- ----------------------------------------------------

@[simp]
lemma inversa_nil :
  inversa ([] : list α) = [] :=
rfl

@[simp]
lemma inversa_cons :
  inversa (x :: xs) = inversa xs ++ [x] :=
rfl

-- ----------------------------------------------------
-- Ejercicio 3. (p. 9) Demostrar que
--    inversa [x] = [x]
-- ----------------------------------------------------

-- 1ª demostración
example : inversa [x] = [x] :=
begin
  rw inversa_cons,
  rw inversa_nil,
  rw nil_append,
end

-- 2ª demostración
example : inversa [x] = [x] :=
by simp [inversa_cons,
         inversa_nil,
         nil_append]

-- 3ª demostración
example : inversa [x] = [x] :=
by simp

-- 4ª demostración
example : inversa [x] = [x] :=
rfl

-- 5ª demostración
example : inversa [x] = [x] :=
calc inversa [x]
         = inversa ([] : list α) ++ [x] : by rw inversa_cons
     ... = ([] : list α) ++ [x]         : by rw inversa_nil
     ... = [x]                          : by rw nil_append

-- Comentarios sobre la función reverse
-- + Es equivalente a la función inversa
-- + Para usarla hay que importar la librería
--   data.list.basic y abrir el espacio de nombre
--   list escribiendo al principio del fichero
--      import data.list.basic
--      open list
-- + Se puede evaluar. Por ejemplo,
--      #eval reverse  [3,2,5]
-- + Se puede demostrar. Por ejemplo,
--      example : reverse [x] = [x] :=
--      -- by library_search
--      reverse_singleton x
