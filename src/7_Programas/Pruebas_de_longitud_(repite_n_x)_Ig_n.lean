-- Pruebas de longitud (repite n x) = n
-- ====================================

import data.nat.basic
open nat
open list

variable {α : Type}
variable (x : α)
variable (xs : list α)
variable (n : ℕ)

-- ----------------------------------------------------
-- Nota. Se usará la función longitud y sus propiedades
-- estudiadas anteriormente.
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

-- ----------------------------------------------------
-- Ejercicio 1. Definir la función
--    repite :: ℕ → α → list α
-- tal que (repite n x) es la lista formada por n
-- copias del elemento x. Por ejemplo,
--    repite 3 7 = [7,7,7]
-- ----------------------------------------------------

def repite : ℕ → α → list α
| 0 x        := []
| (succ n) x := x :: repite n x

-- #eval repite 3 7

-- ----------------------------------------------------
-- Ejercicio 2. Demostrar los siguientes lemas
-- + repite_cero :
--     repite 0 x = []
-- + repite_suc :
--     repite (succ n) x = x :: repite n x
-- ----------------------------------------------------

@[simp]
lemma repite_cero :
  repite 0 x = [] :=
rfl

@[simp]
lemma repite_suc :
  repite (succ n) x = x :: repite n x :=
rfl

-- ----------------------------------------------------
-- Ejercicio 3. (p. 18) Demostrar que
--    longitud (repite n x) = n
-- ----------------------------------------------------

-- 1ª demostración
example : longitud (repite n x) = n :=
begin
  induction n with n HI,
  { rw repite_cero,
    rw longitud_nil, },
  { rw repite_suc,
    rw longitud_cons,
    rw HI, },
end

-- 2ª demostración
example : longitud (repite n x) = n :=
begin
  induction n with n HI,
  { simp only [repite_cero, longitud_nil], },
  { simp only [repite_suc, longitud_cons, HI], },
end

-- 3ª demostración
example : longitud (repite n x) = n :=
begin
  induction n with n HI,
  { simp, },
  { simp [HI], },
end

-- 4ª demostración
example : longitud (repite n x) = n :=
by induction n ; simp [*]

-- 5ª demostración
example : longitud (repite n x) = n :=
begin
  induction n with n HI,
  { calc
      longitud (repite 0 x)
          = longitud [] : by rw repite_cero
      ... = 0           : by rw longitud_nil },
  { calc
      longitud (repite (succ n) x)
          = longitud (x :: repite n x) : by rw repite_suc
      ... = longitud (repite n x) + 1  : by rw longitud_cons
      ... = n + 1                      : by rw HI
      ... = succ n                     : rfl, },
end

-- 6ª demostración
example : longitud (repite n x) = n :=
nat.rec_on n
  ( show longitud (repite 0 x) = 0, from
      calc
        longitud (repite 0 x)
            = longitud [] : by rw repite_cero
        ... = 0           : by rw longitud_nil )
  ( assume n,
    assume HI : longitud (repite n x) = n,
    show longitud (repite (succ n) x) = succ n, from
      calc
      longitud (repite (succ n) x)
          = longitud (x :: repite n x) : by rw repite_suc
      ... = longitud (repite n x) + 1  : by rw longitud_cons
      ... = n + 1                      : by rw HI
      ... = succ n                     : rfl )

-- 6ª demostración
example : longitud (repite n x) = n :=
nat.rec_on n
  ( by simp )
  ( λ n HI, by simp [*])

-- 7ª demostración
lemma longitud_repite_1 :
  ∀ n, longitud (repite n x) = n
| 0 := by calc
    longitud (repite 0 x)
        = longitud ([] : list α) : by rw repite_cero
    ... = 0                      : by rw longitud_nil
| (n+1) := by calc
    longitud (repite (n + 1) x)
        = longitud (x :: repite n x) : by rw repite_suc
    ... = longitud (repite n x) + 1  : by rw longitud_cons
    ... = n + 1                      : by rw longitud_repite_1

-- 8ª demostración
lemma longitud_repite_2 :
  ∀ n, longitud (repite n x) = n
| 0     := by simp
| (n+1) := by simp [*]

-- Comentarios sobre la función (repeat x n)
-- + Es equivalente a la función (repite n x).
-- + Para usarla hay que importar la librería
--   data.list.basic y abrir el espacio de nombre
--   list escribiendo al principio del fichero
--      import data.list.basic
--      open list
-- + Se puede evaluar. Por ejemplo,
--      #eval list.repeat 7 3
-- + Se puede demostrar. Por ejemplo,
--      example : length (repeat x n) = n :=
--      by induction n ; simp [*]
--
--      example : length (repeat x n) = n :=
--      -- by library_search
--      length_repeat x n
