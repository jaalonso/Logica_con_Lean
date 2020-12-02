-- Prueba del elemento neutro por la derecha de la concatenación
-- =============================================================

import tactic
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
-- Ejercicio 1. (p. 28) Demostrar que
--    conc xs [] = xs
-- ----------------------------------------------------

-- 1ª demostración
example : conc xs [] = xs :=
begin
  induction xs with x xs HI,
  { rw conc_nil, },
  { rw conc_cons,
    rw HI, },
end

-- 2ª demostración
example : conc xs [] = xs :=
begin
  induction xs with x xs HI,
  { rw [conc_nil], },
  { rw [conc_cons, HI], },
end

-- 3ª demostración
example : conc xs [] = xs :=
begin
  induction xs with x xs HI,
  { simp only [conc_nil], },
  { simp only [conc_cons, HI],
    cc, },
end

-- 4ª demostración
example : conc xs [] = xs :=
begin
  induction xs with x xs HI,
  { simp , },
  { simp [HI], },
end

-- 5ª demostración
example : conc xs [] = xs :=
by induction xs ; simp [*]

-- 6ª demostración
example : conc xs [] = xs :=
begin
  induction xs with x xs HI,
  { calc
      conc [] [] = [] : by rw conc_nil, },
  { calc
      conc (x :: xs) []
          = x :: (conc xs []) : by rw conc_cons
      ... = x :: xs           : by rw HI, },
end

-- 7ª demostración
example : conc xs [] = xs :=
list.rec_on xs
  ( show conc [] [] = [], from calc
      conc [] [] = [] : by rw conc_nil )
  ( assume x xs,
    assume HI : conc xs [] = xs,
    show conc (x :: xs) [] = x :: xs, from calc
      conc (x :: xs) []
          = x :: (conc xs []) : by rw conc_cons
      ... = x :: xs           : by rw HI)

-- 8ª demostración
example : conc xs [] = xs :=
list.rec_on xs
  ( show conc [] [] = [], by simp)
  ( assume x xs,
    assume HI : conc xs [] = xs,
    show conc (x :: xs) [] = x :: xs, by simp [HI])

-- 9ª demostración
example : conc xs [] = xs :=
list.rec_on xs
  (by simp)
  (λ x xs HI, by simp [HI])

-- 10ª demostración
lemma conc_nil_1:
  ∀ xs : list α, conc xs [] = xs
| []        := by calc
    conc [] [] = [] : by rw conc_nil
| (x :: xs) := by calc
    conc (x :: xs) []
        = x :: conc xs [] : by rw conc_cons
    ... = x :: xs         : by rw conc_nil_1

-- 11ª demostración
lemma conc_nil_2:
  ∀ xs : list α, conc xs [] = xs
| []        := by simp
| (x :: xs) := by simp [conc_nil_2 xs]

-- Comentarios sobre la función (++)
-- + Es equivalente a la función conc.
-- + Para usarla hay que importar la librería
--   data.list.basic y abrir el espacio de nombre
--   list escribiendo al principio del fichero
--      import data.list.basic
--      open list
-- + Se puede evaluar. Por ejemplo,
--      #eval [1,4] ++ [2,4,1,3]
-- + Se puede demostrar. Por ejemplo,
--      example : xs ++ [] = xs :=
--      by induction xs ; simp [*]
--
--      example : xs ++ [] = xs :=
--      -- by library_search
--      append_nil xs
