-- Pruebas de esVacia xs = esVacia (conc xs xs)
-- ============================================

import data.list.basic
open list

variable {α : Type}
variable  x : α
variables (xs ys zs : list α)

-- ----------------------------------------------------
-- Nota. Se usará la función conc y sus propiedades
-- estudiadas anteriormente.
-- ----------------------------------------------------

def conc : list α → list α → list α
| []        ys := ys
| (x :: xs) ys := x :: (conc xs ys)

@[simp]
lemma conc_nil :
  conc ([] : list α) ys = ys :=
rfl

@[simp]
lemma conc_cons :
  conc (x :: xs) ys = x :: (conc xs ys) :=
rfl

-- ----------------------------------------------------
-- Ejercicio 1. Definir la función
--    esVacia : list α → bool
-- tal que (esVacia xs) se verifica si xs es la lista
-- vacía. Por ejemplo,
--    esVacia []  = tt
--    esVacia [1] = ff
-- ----------------------------------------------------

def esVacia : list α → bool
| [] := tt
| _  := ff

-- #eval esVacia ([] : list ℕ)
-- #eval esVacia [1]

-- ----------------------------------------------------
-- Ejercicio 2. Demostrar los siguientes lemas
-- + esVacia_nil :
--      esVacia ([] : list α) = tt :=
-- + esVacia_cons :
--      esVacia (x :: xs) = ff :=
-- ----------------------------------------------------

@[simp]
lemma esVacia_nil :
  esVacia ([] : list α) = tt :=
rfl

@[simp]
lemma esVacia_cons :
  esVacia (x :: xs) = ff :=
rfl

-- ----------------------------------------------------
-- Ejercicio 3 (p. 39) . Demostrar que
--    esVacia xs = esVacia (conc xs xs)
-- ----------------------------------------------------

-- 1ª demostración
example : esVacia xs = esVacia (conc xs xs) :=
begin
  cases xs,
  { rw conc_nil, },
  { rw conc_cons,
    rw esVacia_cons,
    rw esVacia_cons, },
end

-- 2ª demostración
lemma esVacia_conc_1
  : ∀ xs : list α, esVacia xs = esVacia (conc xs xs)
| []        := by calc
    esVacia [] = esVacia (conc [] []) : by rw conc_nil
| (x :: xs) := by calc
    esVacia (x :: xs)
        = ff                                 : by rw esVacia_cons
    ... = esVacia (x :: conc xs (x :: xs))   : by rw esVacia_cons
    ... = esVacia (conc (x :: xs) (x :: xs)) : by rw conc_cons

-- 3ª demostración
lemma esVacia_conc_2
  : ∀ xs : list α, esVacia xs = esVacia (conc xs xs)
| []        := by simp
| (x :: xs) := by simp

-- 3ª demostración
example : esVacia xs = esVacia (conc xs xs) :=
by cases xs ; simp

-- Comentarios sobre la función is_nil.
-- + Es equivalente a la función esVacia.
-- + Para usarla hay que importar la librería
--   data.list.basic y abrir el espacio de nombre
--   list escribiendo al principio del fichero
--      import data.list.basic
--      open list
-- + Se puede evaluar. Por ejemplo,
--      #eval is_nil ([] : list ℕ)
--      #eval is_nil [1]
-- + Se puede demostrar. Por ejemplo,
--      example : is_nil xs = is_nil (xs ++ xs) :=
--      by cases xs ; finish
