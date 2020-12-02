-- Pruebas de conc (coge n xs) (elimina n xs) = xs
-- ===============================================

import tactic
import data.list.basic
import data.nat.basic
open list
open nat

variable {α : Type}
variable  x : α
variables (xs ys zs : list α)
variable  n : ℕ

-- ----------------------------------------------------
-- Nota. Se usará la definición y propiedades de la
-- función conc estudiadas anteriormente.
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
--    coge : ℕ → list α → list α
-- tal que (coge n xs) es la lista de los n primeros
-- elementos de xs. Por ejemplo,
--    coge 2 [1,4,2,7,0] =  [1,4]
-- ----------------------------------------------------

def coge : ℕ → list α → list α
| 0        xs        := []
| (succ n) []        := []
| (succ n) (x :: xs) := x :: coge n xs

-- #eval coge 2 [1,4,2,7]

-- ----------------------------------------------------
-- Ejercicio 2. Demostrar los siguientes lemas
-- + coge_cero :
--      coge 0 xs = []
-- + coge_nil :
--      coge n [] = []
-- + coge_cons :
--      coge (succ n) (x :: xs) = x :: coge n xs
-- ----------------------------------------------------

@[simp]
lemma coge_cero :
  coge 0 xs = [] :=
rfl

@[simp]
lemma coge_nil :
  ∀ n, coge n ([] : list α) = []
| 0     := rfl
| (n+1) := rfl

@[simp]
lemma coge_cons :
  coge (succ n) (x :: xs) = x :: coge n xs :=
rfl

-- ----------------------------------------------------
-- Ejercicio 3. Definir la función
--    elimina : ℕ → list α → list α
-- tal que (elimina n xs) es la lista obtenida eliminando los n primeros
-- elementos de xs. Por ejemplo,
--    elimina 2 [1,4,2,7,0] = [2,7,0]
-- ----------------------------------------------------

def elimina : ℕ → list α → list α
| 0        xs        := xs
| (succ n) []        := []
| (succ n) (x :: xs) := elimina n xs

-- #eval elimina 2 [1,4,2,7,0]

-- ----------------------------------------------------
-- Ejercicio 4. Demostrar los siguientes lemas
-- + elimina_cero :
--      elimina 0 xs = xs
-- + elimina_nil :
--      elimina n [] = []
-- + elimina_cons :
--      elimina (succ n) (x :: xs) = elimina n xs
-- ----------------------------------------------------

@[simp]
lemma elimina_cero :
  elimina 0 xs = xs :=
rfl

@[simp]
lemma elimina_nil :
  ∀ n, elimina n ([] : list α) = []
| 0     := rfl
| (n+1) := rfl

@[simp]
lemma elimina_cons :
  elimina (succ n) (x :: xs) = elimina n xs :=
rfl

-- ----------------------------------------------------
-- Ejercicio 5. (p. 35) Demostrar que
--    conc (coge n xs) (elimina n xs) = xs
-- ----------------------------------------------------

-- 1ª demostración
lemma conc_coge_elimina_1 :
  ∀ (n : ℕ) (xs : list α),
  conc (coge n xs) (elimina n xs) = xs
| 0 xs := by calc
    conc (coge 0 xs) (elimina 0 xs)
        = conc [] (elimina 0 xs)                                : by rw coge_cero
    ... = conc [] xs                                            : by rw elimina_cero
    ... = xs                                                    : by rw conc_nil
| (succ n) [] := by calc
    conc (coge (succ n) []) (elimina (succ n) [])
        = conc ([] : list α) (elimina (succ n) [])              : by rw coge_nil
    ... = conc [] []                                            : by rw elimina_nil
    ... = []
          : by rw conc_nil
| (succ n) (x :: xs) := by calc
    conc (coge (succ n) (x :: xs)) (elimina (succ n) (x :: xs))
        = conc (x :: coge n xs) (elimina (succ n) (x :: xs))    : by rw coge_cons
    ... = conc (x :: coge n xs) (elimina n xs)                  : by rw elimina_cons
    ... = x :: conc (coge n xs) (elimina n xs)                  : by rw conc_cons
    ... = x :: xs                                               : by rw conc_coge_elimina_1

-- 2ª demostración
lemma conc_coge_elimina_2 :
  ∀ (n : ℕ) (xs : list α),
  conc (coge n xs) (elimina n xs) = xs
| 0        xs        := by simp
| (succ n) []        := by simp
| (succ n) (x :: xs) := by simp [conc_coge_elimina_2]

-- 3ª demostración
lemma conc_coge_elimina_3 :
  ∀ (n : ℕ) (xs : list α),
  conc (coge n xs) (elimina n xs) = xs
| 0        xs        := rfl
| (succ n) []        := rfl
| (succ n) (x :: xs) := congr_arg (cons x) (conc_coge_elimina_3 n xs)

-- Comentarios sobre las funciones take y drop:
-- + Para usarlas hay que importar la librería
--   data.list.basic y abrir el espacio de nombre
--   list escribiendo al principio del fichero
--      import data.list.basic
--      open list
-- + Se puede calcular. Por ejemplo,
--      #eval take 2 [1,4,2,7]
--      #eval drop 2 [1,4,2,7,0]
-- + Se puede demostrar. Por ejemplo,
--      lemma take_drop :
--        ∀ (n : ℕ) (xs : list α),
--        take n xs ++ drop n xs = xs
--      | 0        xs        := by simp
--      | (succ n) []        := by simp
--      | (succ n) (x :: xs) := by simp [take_drop]
--
--      example : take n xs ++ drop n xs = xs :=
--      -- by library_search
--      take_append_drop n xs
