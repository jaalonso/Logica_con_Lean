-- Pruebas de la equivalencia entre las definiciones de inversa
-- ============================================================

import data.list.basic
open list

variable  {α : Type*}
variable  x : α
variables (xs ys : list α)

-- ----------------------------------------------------
-- Nota. Se usará la función inversa y sus propiedades
-- estudiadas anteriormente.
-- ----------------------------------------------------

def inversa : list α → list α
| []        := []
| (x :: xs) := inversa xs ++ [x]

@[simp]
lemma inversa_nil :
  inversa ([] : list α) = [] :=
rfl

@[simp]
lemma inversa_cons :
  inversa (x :: xs) = inversa xs ++ [x] :=
rfl

-- ----------------------------------------------------
-- Ejercicio 1. Definir la función
--    inversaAc : list α → list α
-- tal que (inversaAc xs) es a inversa de xs calculada
-- usando acumuladores. Por ejemplo,
--    inversaAc [1,3,2,5] = [5,3,2,1]
-- ----------------------------------------------------

def inversaAcAux : list α → list α → list α
| []        ys := ys
| (x :: xs) ys := inversaAcAux xs (x :: ys)

@[simp]
def inversaAc : list α → list α :=
λ xs, inversaAcAux xs []

-- #eval inversaAc [1,3,2,5]

-- ----------------------------------------------------
-- Ejercicio 2.Demostrar los siguientes lemas
-- + inversaAcAux_nil :
--      inversaAcAux [] ys = ys
-- + inversaAcAux_cons :
--      inversaAcAux (x :: xs) ys =
--      inversaAcAux xs (x :: ys)
-- ----------------------------------------------------

@[simp]
lemma inversaAcAux_nil :
  inversaAcAux [] ys = ys :=
rfl

@[simp]
lemma inversaAcAux_cons :
  inversaAcAux (x :: xs) ys =
  inversaAcAux xs (x :: ys) :=
rfl

-- ----------------------------------------------------
-- Ejercicio 3. Demostrar que
--    inversaAc [1,2,3] = inversa [1,2,3]
-- ----------------------------------------------------

example : inversaAc [1,2,3] = inversa [1,2,3] :=
rfl

-- ----------------------------------------------------
-- Ejercicio 4. (p. 44) Demostrar que
--    inversaAcAux xs ys = (inversa xs) ++ ys
-- ----------------------------------------------------

-- 1ª demostración
example :
  inversaAcAux xs ys = (inversa xs) ++ ys :=
begin
  induction xs with x xs HI generalizing ys,
  { rw inversaAcAux_nil,
    rw inversa_nil,
    rw nil_append, },
  { rw inversaAcAux_cons,
    rw (HI (x :: ys)),
    rw inversa_cons,
    rw append_assoc,
    rw singleton_append, },
end

-- 2ª demostración
example :
  inversaAcAux xs ys = (inversa xs) ++ ys :=
begin
  induction xs with x xs HI generalizing ys,
  { calc inversaAcAux [] ys
         = ys               : by rw inversaAcAux_nil
     ... = [] ++ ys         : by rw nil_append
     ... = inversa [] ++ ys : by rw inversa_nil },
  { calc inversaAcAux (x :: xs) ys
         = inversaAcAux xs (x :: ys) : by rw inversaAcAux_cons
     ... = inversa xs ++ (x :: ys)   : by rw (HI (x :: ys))
     ... = inversa xs ++ ([x] ++ ys) : by rw singleton_append
     ... = (inversa xs ++ [x]) ++ ys : by rw append_assoc
     ... = inversa (x :: xs) ++ ys   : by rw inversa_cons },
end

-- 3ª demostración
example :
  inversaAcAux xs ys = (inversa xs) ++ ys :=
begin
  induction xs with x xs HI generalizing ys,
  { simp, },
  { simp [HI (x :: ys)], },
end

-- 4ª demostración
example :
  inversaAcAux xs ys = (inversa xs) ++ ys :=
by induction xs generalizing ys ; simp [*]

-- 5ª demostración
lemma inversa_equiv :
  ∀ xs : list α, ∀ ys, inversaAcAux xs ys = (inversa xs) ++ ys
| []         := by simp
| (x :: xs)  := by simp [inversa_equiv xs]

-- ----------------------------------------------------
-- Ejercicio 5. (p. 43) Demostrar que
--    inversaAc xs = inversa xs
-- ----------------------------------------------------

-- 1ª demostración
example : inversaAc xs = inversa xs :=
calc inversaAc xs
     = inversaAcAux xs [] : rfl
 ... = inversa xs ++ []   : by rw inversa_equiv
 ... = inversa xs         : by rw append_nil

-- 2ª demostración
example : inversaAc xs = inversa xs :=
by simp [inversa_equiv]
