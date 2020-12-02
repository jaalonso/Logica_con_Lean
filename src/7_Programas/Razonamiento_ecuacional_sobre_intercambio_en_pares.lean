-- Razonamiento ecuacional sobre intercambio en pares
-- ==================================================

import data.prod
open prod

variables {α : Type*} {β : Type*}

-- ----------------------------------------------------
-- Ejercicio 1. Definir la función
--    intercambia :: α × β → β × α
-- tal que (intercambia p) es el par obtenido
-- intercambiando las componentes del par p. Por
-- ejemplo,
--    intercambia (5,7) = (7,5)
-- ----------------------------------------------------

def intercambia : α × β → β × α :=
λp, (p.2, p.1)

-- #eval intercambia (5,7)

-- ----------------------------------------------------
-- Ejercicio 2. Demostrar el lema
--    intercambia_simp : intercambia p = (p.2, p.1)
-- ----------------------------------------------------

@[simp]
lemma intercambia_simp
  {p : α × β}
  : intercambia p = (p.2, p.1) :=
rfl

-- ----------------------------------------------------
-- Ejercicio 3. (p.6) Demostrar que
--    intercambia (intercambia p) = p
-- ----------------------------------------------------

-- 1ª demostración
example : ∀ p : α × β, intercambia (intercambia p) = p :=
begin
  rintro ⟨x,y⟩,
  rw intercambia_simp,
  rw intercambia_simp,
end

-- 2ª demostración
example : ∀ p : α × β, intercambia (intercambia p) = p :=
λ ⟨x,y⟩, by simp only [intercambia_simp]

-- 3ª demostración
example : ∀ p : α × β, intercambia (intercambia p) = p :=
by simp

-- 4ª demostración
example : ∀ p : α × β, intercambia (intercambia p) = p
| (x,y) := rfl

-- Comentarios sobre la función swap
-- + Es equivalente a la función intercambia.
-- + Para usarla hay que importar la librería data.prod
--   y abrir espacio de nombre prod el escribiendo al
--   principio del fichero
--      import data.prod
--      open prod
-- + Se puede evaluar. Por ejemplo,
--      #eval swap (5,7)
-- + Se puede demostrar. Por ejemplo,
--      example : ∀ p : α × β, swap (swap p) = p
--      | (x,y) := rfl
--
--      example : ∀ p : α × β, swap (swap p) = p :=
--      -- by library_search
--      swap_swap
