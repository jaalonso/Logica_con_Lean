-- Razonamiento ecuacional sobre intercambio en pares
-- ==================================================

import data.prod
open prod

variables {α : Type*} {β : Type*}
variable  (x : α)
variable  (y : β)

-- ----------------------------------------------------
-- Ejercicio 1. Definir la función
--    intercambia :: α × β → β × α
-- tal que (intercambia p) es el par obtenido
-- intercambiando las componentes del par p. Por
-- ejemplo,
--    intercambia (5,7) = (7,5)
-- ----------------------------------------------------

def intercambia : α × β → β × α
| (x,y) := (y, x)

-- #eval intercambia (5,7)

-- ----------------------------------------------------
-- Ejercicio 2. Demostrar el lema
--    intercambia_simp : intercambia p = (p.2, p.1)
-- ----------------------------------------------------

@[simp]
lemma intercambia_simp :
  intercambia (x,y) = (y,x) :=
rfl

-- ----------------------------------------------------
-- Ejercicio 3. (p.6) Demostrar que
--    intercambia (intercambia (x,y)) = (x,y)
-- ----------------------------------------------------

-- 1ª demostración
example :
  intercambia (intercambia (x,y)) = (x,y) :=
calc intercambia (intercambia (x,y))
         = intercambia (y,x)          : by rw intercambia_simp
     ... = (x,y)                      : by rw intercambia_simp

-- 2ª demostración
example :
  intercambia (intercambia (x,y)) = (x,y) :=
calc intercambia (intercambia (x,y))
         = intercambia (y,x)          : by simp
     ... = (x,y)                      : by simp

-- 3ª demostración
example :
  intercambia (intercambia (x,y)) = (x,y) :=
by simp

-- 4ª demostración
example :
  intercambia (intercambia (x,y)) = (x,y) :=
rfl

-- 5ª demostración
example :
  intercambia (intercambia (x,y)) = (x,y) :=
begin
  rw intercambia_simp,
  rw intercambia_simp,
end

-- Comentarios sobre la función swap:
-- + Es equivalente a la función intercambia.
-- + Para usarla hay que importar la librería data.prod
--   y abrir espacio de nombre prod el escribiendo al
--   principio del fichero
--      import data.prod
--      open prod
-- + Se puede evaluar. Por ejemplo,
--      #eval swap (5,7)
-- + Se puede demostrar. Por ejemplo,
--      example :
--        swap (swap (x,y)) = (x,y) :=
--      rfl
--
--      example :
--        swap (swap (x,y)) = (x,y) :=
--      -- by library_search
--      swap_swap (x,y)
