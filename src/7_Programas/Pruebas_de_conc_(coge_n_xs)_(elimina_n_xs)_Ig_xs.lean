-- Pruebas de conc (coge n xs) (elimina n xs) = xs
-- ===============================================

import tactic
open list
open nat

variable  {α : Type}
variable  (x : α)
variables (xs ys : list α)
variable  (n : ℕ)

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
| 0        _         := []
| (succ _) []        := []
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
example :
  ∀ xs : list α, conc (coge n xs) (elimina n xs) = xs :=
begin
  induction n with m HI1,
  { intro,
    rw coge_cero,
    rw elimina_cero,
    rw conc_nil, },
  { intro,
    induction xs with a as HI2,
    { rw coge_nil,
      rw elimina_nil,
      rw conc_nil, },
    { rw coge_cons,
      rw elimina_cons,
      rw conc_cons,
      rw (HI1 as), }, },
end

-- 2ª demostración
example :
  ∀ xs : list α, conc (coge n xs) (elimina n xs) = xs :=
begin
  induction n with m HI1,
  { intro,
    calc conc (coge 0 xs) (elimina 0 xs)
         = conc [] (elimina 0 xs) : by rw coge_cero
     ... = conc [] xs             : by rw elimina_cero
     ... = xs                     : by rw conc_nil, },
  { intro,
    induction xs with a as HI2,
    { calc conc (coge (succ m) []) (elimina (succ m) [])
           = conc ([] : list α) (elimina (succ m) []) : by rw coge_nil
       ... = conc [] []                               : by rw elimina_nil
       ... = []                                       : by rw conc_nil, },
    { calc conc (coge (succ m) (a :: as)) (elimina (succ m) (a :: as))
           = conc (a :: coge m as) (elimina (succ m) (a :: as)) :by rw coge_cons
       ... = conc (a :: coge m as) (elimina m as)               :by rw elimina_cons
       ... = a :: conc (coge m as) (elimina m as)               :by rw conc_cons
       ... = a :: as                                            :by rw (HI1 as), }, },
end

-- 3ª demostración
example :
  ∀ xs : list α, conc (coge n xs) (elimina n xs) = xs :=
begin
  induction n with m HI1,
  { intro,
    simp, },
  { intro,
    induction xs with a as HI2,
    { simp, },
    { simp [HI1 as], }, },
end

-- 4ª demostración
example :
  ∀ xs : list α, conc (coge n xs) (elimina n xs) = xs :=
nat.rec_on n
  ( assume xs,
    show conc (coge 0 xs) (elimina 0 xs) = xs, from
      calc conc (coge 0 xs) (elimina 0 xs)
           = conc ([] : list α) (elimina 0 xs) : by rw coge_cero
       ... = conc [] xs                        : by rw elimina_cero
       ... = xs                                : by rw conc_nil)
  ( assume m,
    assume HI1 : ∀ xs, conc (coge m xs) (elimina m xs) = xs,
    assume xs,
    show conc (coge (succ m) xs) (elimina (succ m) xs) = xs, from
      list.rec_on xs
      ( show conc (coge (succ m) []) (elimina (succ m) []) = [], from
          calc conc (coge (succ m) []) (elimina (succ m) [])
                     = conc ([] : list α) (elimina (succ m) []) : by rw coge_nil
                 ... = conc [] []                               : by rw elimina_nil
                 ... = []                                       : by rw conc_nil)
      ( assume a as,
        assume HI2 : conc (coge (succ m) as) (elimina (succ m) as) = as,
        show conc (coge (succ m) (a :: as)) (elimina (succ m) (a :: as)) = a :: as, from
          calc conc (coge (succ m) (a :: as)) (elimina (succ m) (a :: as))
                     = conc (a :: coge m as) (elimina (succ m) (a :: as)) :by rw coge_cons
                 ... = conc (a :: coge m as) (elimina m as)               :by rw elimina_cons
                 ... = a :: conc (coge m as) (elimina m as)               :by rw conc_cons
                 ... = a :: as                                            :by rw (HI1 as)))

-- 5ª demostración
example :
  ∀ xs : list α, conc (coge n xs) (elimina n xs) = xs :=
nat.rec_on n
  (by simp)
  (λ m HI1 xs, list.rec_on xs
    (by simp)
    (by simp [HI1]))

-- 6ª demostración
lemma conc_coge_elimina_1 :
  ∀ (n : ℕ) (xs : list α), conc (coge n xs) (elimina n xs) = xs
| 0 xs := by calc
    conc (coge 0 xs) (elimina 0 xs)
        = conc [] (elimina 0 xs)                                : by rw coge_cero
    ... = conc [] xs                                            : by rw elimina_cero
    ... = xs                                                    : by rw conc_nil
| (succ m) [] := by calc
    conc (coge (succ m) []) (elimina (succ m) [])
        = conc ([] : list α) (elimina (succ m) [])              : by rw coge_nil
    ... = conc [] []                                            : by rw elimina_nil
    ... = []                                                    : by rw conc_nil
| (succ m) (a :: as) := by calc
    conc (coge (succ m) (a :: as)) (elimina (succ m) (a :: as))
        = conc (a :: coge m as) (elimina (succ m) (a :: as))    : by rw coge_cons
    ... = conc (a :: coge m as) (elimina m as)                  : by rw elimina_cons
    ... = a :: conc (coge m as) (elimina m as)                  : by rw conc_cons
    ... = a :: as                                               : by rw conc_coge_elimina_1

-- 7ª demostración
lemma conc_coge_elimina_2 :
  ∀ (n : ℕ) (xs : list α), conc (coge n xs) (elimina n xs) = xs
| 0        xs        := by simp
| (succ m) []        := by simp
| (succ m) (a :: as) := by simp [conc_coge_elimina_2]

-- 8ª demostración
lemma conc_coge_elimina_3 :
  ∀ (n : ℕ) (xs : list α), conc (coge n xs) (elimina n xs) = xs
| 0        xs        := rfl
| (succ m) []        := rfl
| (succ m) (a :: as) := congr_arg (cons a) (conc_coge_elimina_3 m as)

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
example : take n xs ++ drop n xs = xs :=
-- by library_search
take_append_drop n xs

lemma take_drop_1 :
  ∀ (n : ℕ) (xs : list α), take n xs ++ drop n xs = xs
| 0        xs        := by simp
| (succ n) []        := by simp
| (succ n) (x :: xs) := by simp [take_drop_1]

example : take n xs ++ drop n xs = xs :=
by simp
