-- Razonamiento ecuacional sobre longitudes de listas
-- ==================================================

import data.list.basic
open list

variable {α : Type}
variable x : α
variable (xs : list α)

-- ----------------------------------------------------
-- Ejercicio 1. Definir, por recursión, la función
--    longitud : list α → ℕ
-- tal que (longitud xs) es la longitud de la lista
-- xs. Por ejemplo,
--    longitud [a,c,d] = 3
-- ----------------------------------------------------

def longitud : list α → ℕ
| []        := 0
| (x :: xs) := longitud xs + 1

-- ----------------------------------------------------
-- Ejercicio 2. Calcular
--    longitud [4,2,5]
-- ----------------------------------------------------

-- #eval longitud [4,2,5]
-- da 3

-- ----------------------------------------------------
-- Ejercicio 3. Demostrar los siguientes lemas
-- + longitud_nil :
--     longitud ([] : list α) = 0
-- + longitud_cons :
--     longitud (x :: xs) = longitud xs + 1
-- ----------------------------------------------------

@[simp]
lemma longitud_nil :
  longitud ([] : list α) = 0 :=
rfl

@[simp]
lemma longitud_cons :
  longitud (x :: xs) = longitud xs + 1 :=
rfl

-- ----------------------------------------------------
-- Ejercicio 4. Demostrar que
--    longitud [4,2,5] = 3
-- ----------------------------------------------------

-- 1ª demostración
example
  (a b c : α)
  : longitud [a,b,c] = 3 :=
begin
  rw longitud_cons,
  rw longitud_cons,
  rw longitud_cons,
  rw longitud_nil,
end

-- 2ª demostración
example
  (a b c : α)
  : longitud [a,b,c] = 3 :=
by rw [longitud_cons,
       longitud_cons,
       longitud_cons,
       longitud_nil]

-- 3ª demostración
example
  (a b c : α)
  : longitud [a,b,c] = 3 :=
by simp only [longitud_cons,
              longitud_nil]

-- 4ª demostración
example
  (a b c : α)
  : longitud [a,b,c] = 3 :=
by simp

-- 5ª demostración
example
  (a b c : α)
  : longitud [a,b,c] = 3 :=
rfl

-- 6ª demostración
example
  (a b c : α)
  : longitud [a,b,c] = 3 :=
calc
  longitud [a,b,c]
      = longitud [b,c] + 1          : by rw longitud_cons
  ... = (longitud [c] + 1) + 1      : by rw longitud_cons
  ... = ((longitud [] + 1) + 1) + 1 : by rw longitud_cons
  ... = ((0 + 1) + 1) + 1           : by rw longitud_nil
  ... = 3                           : rfl

-- 7ª demostración
example
  (a b c : α)
  : longitud [a,b,c] = 3 :=
calc
  longitud [a,b,c]
      = longitud [b,c] + 1          : rfl
  ... = (longitud [c] + 1) + 1      : rfl
  ... = ((longitud [] + 1) + 1) + 1 : rfl
  ... = ((0 + 1) + 1) + 1           : rfl
  ... = 3                           : rfl

-- Comentarios sobre la función length
-- + Es equivalente a la función longitud.
-- + Para usarla hay que importar la librería
--   data.list.basic y abrir el espacio de nombre
--   list escribiendo al principio del fichero
--      import data.list.basic
--      open list
-- + Se puede evaluar. Por ejemplo,
--      #eval length [4,2,5,7,2]
-- + Se puede demostrar. Por ejemplo,
--      example
--        (a b c : α)
--        : length [a,b,c] = 3 :=
--      rfl
