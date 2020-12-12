-- Pruebas de la distributiva del producto sobre sumas
-- ===================================================

import data.nat.basic
open nat
open list

variables {α : Type*} {β : Type*}
variable  (x : α)
variables (xs : list α)
variable  (n : ℕ)
variable  (ns : list ℕ)

-- ----------------------------------------------------
-- Nota. Se usará la función aplica y sus propiedades
-- estudiadas anteriormente.
-- ----------------------------------------------------

def aplica : (α → β) → list α → list β
| f []        := []
| f (x :: xs) := (f x) :: aplica f xs

@[simp]
lemma aplica_nil
  (f : α → β)
  : aplica f [] = [] :=
rfl

@[simp]
lemma aplica_cons
  (f : α → β)
  : aplica f (x :: xs) = (f x) :: aplica f xs :=
rfl

-- ----------------------------------------------------
-- Ejercicio 1. Definir la función
--    suma : list ℕ → ℕ
-- tal que (suma xs) es la suma de los elementos de
-- xs. Por ejemplo,
--    suma [3,2,5] = 10
-- ----------------------------------------------------

def suma : list ℕ → ℕ
| []        := 0
| (n :: ns) := n + suma ns

-- #eval suma [3,2,5]

-- ----------------------------------------------------
-- Ejercicio 2. Demostrar los siguientes lemas
-- + suma_nil :
--      suma ([] : list ℕ) = 0 :=
-- + suma_cons :
--      suma (n :: ns) = n + suma ns :=
-- ----------------------------------------------------

@[simp]
lemma suma_nil :
  suma ([] : list ℕ) = 0 :=
rfl

@[simp]
lemma suma_cons :
  suma (n :: ns) = n + suma ns :=
rfl

-- ----------------------------------------------------
-- Ejercicio 3. (p. 45) Demostrar que
--    suma (aplica (λ x, 2*x) ns) = 2 * (suma ns)
-- ----------------------------------------------------

-- 1ª demostración
example :
  suma (aplica (λ x, 2*x) ns) = 2 * (suma ns) :=
begin
  induction ns with m ms HI,
  { rw aplica_nil,
    rw suma_nil,
    rw mul_zero, },
  { rw aplica_cons,
    rw suma_cons,
    rw HI,
    rw suma_cons,
    rw mul_add, },
end

-- 2ª demostración
example :
  suma (aplica (λ x, 2*x) ns) = 2 * (suma ns) :=
begin
  induction ns with m ms HI,
  { calc suma (aplica (λ (x : ℕ), 2 * x) [])
         = suma []                                : by rw aplica_nil
     ... = 0                                      : by rw suma_nil
     ... = 2 * 0                                  : by rw mul_zero
     ... = 2 * suma []                            : by rw suma_nil, },
  { calc suma (aplica (λ x, 2 * x) (m :: ms))
         = suma (2 * m :: aplica (λ x, 2 * x) ms) : by rw aplica_cons
     ... = 2 * m + suma (aplica (λ x, 2 * x) ms)  : by rw suma_cons
     ... = 2 * m + 2 * suma ms                    : by rw HI
     ... = 2 * (m + suma ms)                      : by rw mul_add
     ... = 2 * suma (m :: ms)                     : by rw suma_cons, },
end

-- 3ª demostración
example :
  suma (aplica (λ x, 2*x) ns) = 2 * (suma ns) :=
begin
  induction ns with m ms HI,
  { simp, },
  { simp [HI, mul_add], },
end

-- 4ª demostración
example :
  suma (aplica (λ x, 2*x) ns) = 2 * (suma ns) :=
by induction ns ; simp [*, mul_add]

-- 4ª demostración
lemma suma_aplica :
  ∀ ns, suma (aplica (λ x, 2*x) ns) = 2 * (suma ns)
| []        := by simp
| (m :: ms) := by simp [suma_aplica ms, mul_add]

-- Comentarios sobre las funciones sum y map:
-- + Es equivalente a la función longitud.
-- + Para usarla hay que importar la librería
--   data.list.basic y abrir el espacio de nombre
--   list escribiendo al principio del fichero
--      import data.list.basic
--      open list
-- + Se puede evaluar. Por ejemplo,
--      #eval sum [3,2,5]
--      #eval map (λx, 2*x) [3,2,5]
--      #eval map ((*) 2) [3,2,5]
--      #eval map ((+) 2) [3,2,5]
