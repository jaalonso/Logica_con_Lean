-- Prueba de la asociatividad de la concatenación
-- ==============================================

import tactic
open list

variable  {α : Type}
variable  (x : α)
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
  induction xs with a as HI,
  { calc conc [] (conc ys zs)
         = conc ys zs                  : by rw conc_nil
     ... = conc (conc [] ys) zs        : by rw conc_nil, },
  { calc conc (a :: as) (conc ys zs)
         = a :: conc as (conc ys zs)   : by rw conc_cons
     ... = a :: conc (conc as ys) zs   : by rw HI
     ... = conc (a :: conc as ys) zs   : by rw conc_cons
     ... = conc (conc (a :: as) ys) zs : by rw ←conc_cons, },
end

-- 2ª demostración
example :
  conc xs (conc ys zs) = conc (conc xs ys) zs :=
begin
  induction xs with a as HI,
  { calc conc [] (conc ys zs)
         = conc ys zs                  : by simp
     ... = conc (conc [] ys) zs        : by simp, },
  { calc conc (a :: as) (conc ys zs)
         = a :: conc as (conc ys zs)   : by simp
     ... = a :: conc (conc as ys) zs   : by simp [HI]
     ... = conc (a :: conc as ys) zs   : by simp
     ... = conc (conc (a :: as) ys) zs : by simp, },
end

-- 3ª demostración
example :
  conc xs (conc ys zs) = conc (conc xs ys) zs :=
begin
  induction xs with a as HI,
  { by simp, },
  { by simp [HI], },
end

-- 4ª demostración
example :
  conc xs (conc ys zs) = conc (conc xs ys) zs :=
by induction xs ; simp [*]

-- 5ª demostración
example :
  conc xs (conc ys zs) = conc (conc xs ys) zs :=
begin
  induction xs with a as HI,
  { rw conc_nil,
    rw conc_nil, },
  { rw conc_cons,
    rw HI,
    rw conc_cons,
    rw conc_cons, },
end

-- 6ª demostración
example :
  conc xs (conc ys zs) = conc (conc xs ys) zs :=
list.rec_on xs
  ( show conc [] (conc ys zs) = conc (conc [] ys) zs,
      from calc
        conc [] (conc ys zs)
            = conc ys zs           : by rw conc_nil
        ... = conc (conc [] ys) zs : by rw conc_nil )
    ( assume a as,
      assume HI : conc as (conc ys zs) = conc (conc as ys) zs,
      show conc (a :: as) (conc ys zs) = conc (conc (a :: as) ys) zs,
        from calc
          conc (a :: as) (conc ys zs)
               = a :: conc as (conc ys zs)  : by rw conc_cons
          ... = a :: conc (conc as ys) zs   : by rw HI
          ... = conc (a :: conc as ys) zs   : by rw conc_cons
          ... = conc (conc (a :: as) ys) zs : by rw ←conc_cons)

-- 7ª demostración
example :
  conc xs (conc ys zs) = conc (conc xs ys) zs :=
list.rec_on xs
  (by simp)
  (by simp [*])

-- 8ª demostración
lemma conc_asoc_1 :
  ∀ xs, conc xs (conc ys zs) = conc (conc xs ys) zs
| [] := by calc
    conc [] (conc ys zs)
        = conc ys zs           : by rw conc_nil
    ... = conc (conc [] ys) zs : by rw conc_nil
| (a :: as) := by calc
    conc (a :: as) (conc ys zs)
        = a :: conc as (conc ys zs)   : by rw conc_cons
    ... = a :: conc (conc as ys) zs   : by rw conc_asoc_1
    ... = conc (a :: conc as ys) zs   : by rw conc_cons
    ... = conc (conc (a :: as) ys) zs : by rw ←conc_cons

-- 9ª demostración
lemma conc_asoc_2 :
  ∀ xs, conc xs (conc ys zs) = conc (conc xs ys) zs
| []         := by simp
| (a :: as)  := by simp [conc_asoc_2 as]

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
--      -- by library_search
--      (append_assoc xs ys zs).symm
--
--      example :
--        (xs ++ ys) ++ zs = xs ++ (ys ++ zs) :=
--      -- by library_search
--      append_assoc xs ys zs
--
--      example :
--        (xs ++ ys) ++ zs = xs ++ (ys ++ zs) :=
--      by induction xs ; simp [*]
