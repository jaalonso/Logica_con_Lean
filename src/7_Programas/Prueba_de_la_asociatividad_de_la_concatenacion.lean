-- Prueba de la asociatividad de la concatenación
-- ==============================================

import tactic
import data.list.basic
open list

variable {α : Type}
variable  x : α
variables (xs ys zs : list α)

-- ----------------------------------------------------
-- Ejercicio 1. Definir la función
--    conc :: list α → list α → list α
-- tal que (conc xs ys) es la concatención de las
-- listas xs e ys. Por ejemplo,
--    conc [1,4] [2,4,1,3] = [1,4,2,4,1,3]
-- ----------------------------------------------------

def conc : list α → list α → list α
| []        ys := ys
| (x :: xs) ys := x :: (conc xs ys)

-- #eval conc [1,4] [2,4,1,3]

-- ----------------------------------------------------
-- Ejercicio 2. Demostrar los siguientes lemas
-- + conc_nil :
--     conc ([] : list α) ys = ys
-- + conc_cons :
--     conc (x :: xs) ys = x :: (conc xs ys)
-- ----------------------------------------------------

@[simp]
lemma conc_nil :
  conc ([] : list α) ys = ys :=
rfl

@[simp]
lemma conc_cons :
  conc (x :: xs) ys = x :: (conc xs ys) :=
rfl

-- ----------------------------------------------------
-- Ejercicio 3. (p. 24) Demostrar que
--    conc xs (conc ys zs) = conc (conc xs ys) zs
-- ----------------------------------------------------

-- 1ª demostración
example :
  conc xs (conc ys zs) = conc (conc xs ys) zs :=
begin
  induction xs with x xs HI,
  { rw conc_nil,
    rw conc_nil, },
  { rw conc_cons,
    rw HI,
    rw conc_cons,
    rw conc_cons, },
end

-- 2ª demostración
example :
  conc xs (conc ys zs) = conc (conc xs ys) zs :=
begin
  induction xs with x xs HI,
  { calc conc [] (conc ys zs)
         = conc ys zs                  : by rw conc_nil
     ... = conc (conc [] ys) zs        : by rw conc_nil, },
  { calc conc (x :: xs) (conc ys zs)
         = x :: conc xs (conc ys zs)   : by rw conc_cons
     ... = x :: conc (conc xs ys) zs   : by rw HI
     ... = conc (x :: conc xs ys) zs   : by rw conc_cons
     ... = conc (conc (x :: xs) ys) zs : by rw ←conc_cons, },
end

-- 3ª demostración
example :
  conc xs (conc ys zs) = conc (conc xs ys) zs :=
begin
  induction xs with x xs HI,
  { simp, },
  { simp [HI], },
end

-- 4ª demostración
example :
  conc xs (conc ys zs) = conc (conc xs ys) zs :=
by induction xs ; simp [*]

-- 5ª demostración
example :
  conc xs (conc ys zs) = conc (conc xs ys) zs :=
list.rec_on xs
  ( show conc [] (conc ys zs) = conc (conc [] ys) zs,
      from calc
        conc [] (conc ys zs)
            = conc ys zs           : by rw conc_nil
        ... = conc (conc [] ys) zs : by rw conc_nil )
    ( assume x xs,
      assume HI : conc xs (conc ys zs) =
                  conc (conc xs ys) zs,
      show conc (x :: xs) (conc ys zs) =
           conc (conc (x :: xs) ys) zs,
        from calc
          conc (x :: xs) (conc ys zs)
               = x :: conc xs (conc ys zs)  : by rw conc_cons
          ... = x :: conc (conc xs ys) zs   : by rw HI
          ... = conc (x :: conc xs ys) zs   : by rw conc_cons
          ... = conc (conc (x :: xs) ys) zs : by rw ←conc_cons)

-- 6ª demostración
example :
  conc xs (conc ys zs) = conc (conc xs ys) zs :=
list.rec_on xs
  (by simp)
  (by simp [*])

-- 7ª demostración
lemma conc_asoc_1 :
  ∀ xs, conc xs (conc ys zs) = conc (conc xs ys) zs
| [] := by calc
    conc [] (conc ys zs)
        = conc ys zs           : by rw conc_nil
    ... = conc (conc [] ys) zs : by rw conc_nil
| (x :: xs) := by calc
    conc (x :: xs) (conc ys zs)
        = x :: conc xs (conc ys zs)   : by rw conc_cons
    ... = x :: conc (conc xs ys) zs   : by rw conc_asoc_1
    ... = conc (x :: conc xs ys) zs   : by rw conc_cons
    ... = conc (conc (x :: xs) ys) zs : by rw ←conc_cons

-- 8ª demostración
lemma conc_asoc_2 :
  ∀ xs, conc xs (conc ys zs) = conc (conc xs ys) zs
| []         := by simp
| (x :: xs)  := by simp [conc_asoc_2 xs]

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
--      example :
--        xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
--      by induction xs ; simp [*]
--
--      example :
--        xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
--      -- by library_search
--      (append_assoc xs ys zs).symm
