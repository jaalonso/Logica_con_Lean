-- Pruebas de longitud (conc xs ys) = longitud xs + longitud ys
-- ============================================================

import tactic
import data.list.basic
open list

variable {α : Type}
variable  x : α
variables (xs ys zs : list α)

-- ----------------------------------------------------
-- Nota. Se usarán las definiciones y propiedades de las
-- funciones longitud y conc estudiadas anteriormente.
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
-- Ejercicio 1. (p. 30) Demostrar que
--    longitud (conc xs ys) = longitud xs + longitud ys
-- ----------------------------------------------------

-- 1ª demostración
example :
  longitud (conc xs ys) = longitud xs + longitud ys :=
begin
  induction xs with x xs HI,
  { rw conc_nil,
    rw longitud_nil,
    rw nat.zero_add, },
  { rw conc_cons,
    rw longitud_cons,
    rw HI,
    rw longitud_cons,
    rw add_assoc,
    rw add_comm (longitud ys),
    rw add_assoc, },
end

-- 2ª demostración
example :
  longitud (conc xs ys) = longitud xs + longitud ys :=
begin
  induction xs with x xs HI,
  { rw conc_nil,
    rw longitud_nil,
    rw nat.zero_add, },
  { rw conc_cons,
    rw longitud_cons,
    rw HI,
    rw longitud_cons,
    -- library_search,
    exact add_right_comm (longitud xs) (longitud ys) 1},
end

-- 3ª demostración
example :
  longitud (conc xs ys) = longitud xs + longitud ys :=
begin
  induction xs with x xs HI,
  { rw conc_nil,
    rw longitud_nil,
    rw nat.zero_add, },
  { rw conc_cons,
    rw longitud_cons,
    rw HI,
    rw longitud_cons,
    -- by hint,
    linarith, },
end

-- 4ª demostración
example :
  longitud (conc xs ys) = longitud xs + longitud ys :=
begin
  induction xs with x xs HI,
  { simp, },
  { simp [HI],
    linarith, },
end

-- 5ª demostración
example :
  longitud (conc xs ys) = longitud xs + longitud ys :=
begin
  induction xs with x xs HI,
  { simp, },
  { finish [HI],},
end

-- 6ª demostración
example :
  longitud (conc xs ys) = longitud xs + longitud ys :=
by induction xs ; finish [*]

-- 7ª demostración
example :
  longitud (conc xs ys) = longitud xs + longitud ys :=
begin
  induction xs with x xs HI,
  { calc longitud (conc [] ys)
         = longitud ys               : by rw conc_nil
     ... = 0 + longitud ys           : by exact (zero_add (longitud ys)).symm
     ... = longitud [] + longitud ys : by rw longitud_nil },
  { calc longitud (conc (x :: xs) ys)
         = longitud (x :: conc xs ys)       : by rw conc_cons
     ... = longitud (conc xs ys) + 1        : by rw longitud_cons
     ... = (longitud xs + longitud ys) + 1  : by rw HI
     ... = (longitud xs + 1) + longitud ys  : by exact add_right_comm (longitud xs) (longitud ys) 1
     ... = longitud (x :: xs) + longitud ys : by rw longitud_cons, },
end

-- 8ª demostración
example :
  longitud (conc xs ys) = longitud xs + longitud ys :=
list.rec_on xs
  ( show longitud (conc [] ys) =
         longitud [] + longitud ys, from
      calc longitud (conc [] ys)
           = longitud ys               : by rw conc_nil
       ... = 0 + longitud ys           : by exact (zero_add (longitud ys)).symm
       ... = longitud [] + longitud ys : by rw longitud_nil )
  ( assume x xs,
    assume HI : longitud (conc xs ys) =
                longitud xs + longitud ys,
    show longitud (conc (x :: xs) ys) =
         longitud (x :: xs) + longitud ys, from
      calc longitud (conc (x :: xs) ys)
           = longitud (x :: conc xs ys)       : by rw conc_cons
       ... = longitud (conc xs ys) + 1        : by rw longitud_cons
       ... = (longitud xs + longitud ys) + 1  : by rw HI
       ... = (longitud xs + 1) + longitud ys  : by exact add_right_comm (longitud xs) (longitud ys) 1
       ... = longitud (x :: xs) + longitud ys : by rw longitud_cons)

-- 9ª demostración
example :
  longitud (conc xs ys) = longitud xs + longitud ys :=
list.rec_on xs
  ( by simp)
  ( λ x xs HI, by simp [HI, add_right_comm])

-- 10ª demostración
lemma longitud_conc_1 :
  ∀ xs, longitud (conc xs ys) = longitud xs + longitud ys
| [] := by calc
    longitud (conc [] ys)
        = longitud ys               : by rw conc_nil
    ... = 0 + longitud ys           : by rw zero_add
    ... = longitud [] + longitud ys : by rw longitud_nil
| (x :: xs) := by calc
    longitud (conc (x :: xs) ys)
        = longitud (x :: conc xs ys)       : by rw conc_cons
    ... = longitud (conc xs ys) + 1        : by rw longitud_cons
    ... = (longitud xs + longitud ys) + 1  : by rw longitud_conc_1
    ... = (longitud xs + 1) + longitud ys  : by exact add_right_comm (longitud xs) (longitud ys) 1
    ... = longitud (x :: xs) + longitud ys : by rw longitud_cons

-- 11ª demostración
lemma longitud_conc_2 :
  ∀ xs, longitud (conc xs ys) = longitud xs + longitud ys
| []        := by simp
| (x :: xs) := by simp [longitud_conc_2 xs,
                        add_right_comm]

-- Comentarios sobre las funciones length y (++)
-- + Para usarlas hay que importar la librería
--   data.list.basic y abrir el espacio de nombre
--   list escribiendo al principio del fichero
--      import data.list.basic
--      open list
-- + Se puede demostrar. Por ejemplo,
--      example :
--        length (xs ++ ys) = length xs + length ys :=
--      by induction xs ; finish [*]
--
--      example :
--        length (xs ++ ys) = length xs + length ys :=
--      -- by library_search
--      length_append xs ys
