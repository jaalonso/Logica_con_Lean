-- Razonamiento sobre programas
-- ============================

-- En este tema se demuestra con Isabelle las
-- propiedades de los programas funcionales como se
-- expone en el tema 8 del curso "Informática" que
-- puede leerse en http://bit.ly/2Za6YWY

import tactic
import data.list.basic
import data.nat.basic
open list nat

universes u v w w₁ w₂
variables {α : Type u} {β : Type v} {γ : Type w}
variable  x : α
variables (xs ys zs : list α)
variable  y : β
variable  n : ℕ
variable  ns : list ℕ

-- § Razonamiento ecuacional
-- =========================

-- ----------------------------------------------------
-- Ejemplo 1.a. Definir, por recursión, la función
--    longitud : list α → ℕ
-- tal que (longitud xs) es la longitud de la listas
-- xs. Por ejemplo,
--    longitud [a,c,d] = 3
-- ----------------------------------------------------

@[simp] def longitud : list α → nat
| []        := 0
| (x :: xs) := longitud xs + 1

-- ----------------------------------------------------
-- Ejemplo 1.b. Calcular
--    longitud [4,2,5]
-- ----------------------------------------------------

-- #eval longitud [4,2,5]
-- da 3

-- ----------------------------------------------------
-- Ejermplo 1.c. Demostrar los siguientes lemas
-- + longitud_nil :
--     longitud ([] : list α) = 0
-- + longitud_cons :
--     longitud (x :: xs) = longitud xs + 1
-- ----------------------------------------------------

lemma longitud_nil :
  longitud ([] : list α) = 0 :=
rfl

lemma longitud_cons :
  longitud (x :: xs) = longitud xs + 1 :=
rfl

-- ----------------------------------------------------
-- Ejemplo 2. Demostrar que
--    longitud [4,2,5] = 3
-- ----------------------------------------------------

-- 1ª demostración
example
  (a b c : α)
  : longitud [a,b,c] = 3 :=
begin
  rw longitud_cons,
  rw longitud_cons,
  rw longitud_cons,
  rw longitud_nil,
end

-- 2ª demostración
example
  (a b c : α)
  : longitud [a,b,c] = 3 :=
by rw [longitud_cons,
       longitud_cons,
       longitud_cons,
       longitud_nil]

-- 3ª demostración
example
  (a b c : α)
  : longitud [a,b,c] = 3 :=
by simp only [longitud_cons,
              longitud_nil]

-- 4ª demostración
example
  (a b c : α)
  : longitud [a,b,c] = 3 :=
rfl

-- 5ª demostración
example
  (a b c : α)
  : longitud [a,b,c] = 3 :=
calc
  longitud [a,b,c]
      = longitud [b,c] + 1          : by rw longitud_cons
  ... = (longitud [c] + 1) + 1      : by rw longitud_cons
  ... = ((longitud [] + 1) + 1) + 1 : by rw longitud_cons
  ... = ((0 + 1) + 1) + 1           : by rw longitud_nil
  ... = 3                           : rfl

-- 6ª demostración
example
  (a b c : α)
  : longitud [a,b,c] = 3 :=
calc
  longitud [a,b,c]
      = longitud [b,c] + 1          : rfl
  ... = (longitud [c] + 1) + 1      : rfl
  ... = ((longitud [] + 1) + 1) + 1 : rfl
  ... = ((0 + 1) + 1) + 1           : rfl
  ... = 3                           : rfl

-- ----------------------------------------------------
-- Ejemplo 3.a. Definir la función
--    intercambia :: α × β → β × α
-- tal que (intercambia p) es el par obtenido
-- intercambiando las componentes del par p. Por
-- ejemplo,
--    intercambia (u,v) = (v,u)
-- ----------------------------------------------------

def intercambia : α × β → β × α :=
-- λp, (p.2, p.1)

-- ----------------------------------------------------
-- Ejemplo 3.b. Demostrar el lema
--    intercambia_simp : intercambia p = (p.2, p.1)
-- ----------------------------------------------------

lemma intercambia_simp
  {p : α × β}
  : intercambia p = (p.2, p.1) :=
rfl

-- ----------------------------------------------------
-- Ejemplo 4. (p.6) Demostrar que
--    intercambia (intercambia (x,y)) = (x,y)
-- ----------------------------------------------------

-- 1ª demostración
example : ∀ p : α × β, intercambia (intercambia p) = p :=
begin
  rintro ⟨x,y⟩,
  rw intercambia_simp,
  rw intercambia_simp,
end

-- 2ª demostración
example : ∀ p : α × β, intercambia (intercambia p) = p :=
λ ⟨x,y⟩, by simp only [intercambia_simp]

-- 3ª demostración
example : ∀ p : α × β, intercambia (intercambia p) = p
| (x,y) := rfl

-- ----------------------------------------------------
-- Ejemplo 5.a. Definir, por recursión, la función
--    inversa :: list α → list α
-- tal que (inversa xs) es la lista obtenida
-- invirtiendo el orden de los elementos de xs.
-- Por ejemplo,
--    inversa [a,d,c] = [c,d,a]
-- ----------------------------------------------------

@[simp] def inversa : list α → list α
| []        := []
| (x :: xs) := inversa xs ++ [x]

-- #eval inversa [3,2,5]

-- ----------------------------------------------------
-- Ejermplo 5.b. Demostrar los siguientes lemas
-- + inversa_nil :
--     inversa ([] : list α) = []
-- + inversa_cons :
--     inversa (x :: xs) = inversa xs ++ [x]
-- ----------------------------------------------------

lemma inversa_nil :
  inversa ([] : list α) = [] :=
rfl

lemma inversa_cons :
  inversa (x :: xs) = inversa xs ++ [x] :=
rfl

-- ----------------------------------------------------
-- Ejemplo 6. (p. 9) Demostrar que
--    inversa [x] = [x]
-- ----------------------------------------------------

-- 1ª demostración
example : inversa [x] = [x] :=
begin
  rw inversa_cons,
  rw inversa_nil,
  rw nil_append,
end

-- 2ª demostración
example : inversa [x] = [x] :=
by simp [inversa_cons,
         inversa_nil,
         nil_append]

-- 3ª demostración
example : inversa [x] = [x] :=
rfl

-- 4ª demostración
example : inversa [x] = [x] :=
calc inversa [x]
         = inversa ([] : list α) ++ [x]
           : by rw inversa_cons
     ... = ([] : list α) ++ [x]
           : by rw inversa_nil
     ... = [x]
           : by rw nil_append

-- 5ª demostración (con predefinida)
example : reverse [x] = [x] :=
-- by library_search
reverse_singleton x

-- § Razonamiento por inducción sobre los naturales
-- ================================================

-- [Principio de inducción sobre los naturales] Para
-- demostrar una propiedad P para todos los números
-- naturales basta probar que el 0 tiene la propiedad P
-- y que si n tiene la propiedad P, entonces n+1
-- también la tiene.
--
-- En Lean el principio de inducción sobre los
-- naturales está formalizado en el lema  nat.rec_on.

-- ----------------------------------------------------
-- Ejemplo 7.a. Definir la función
--    repite :: ℕ → α → list α
-- tal que (repite n x) es la lista formada por n
-- copias del elemento x. Por ejemplo,
--    repite 3 7 = [7,7,7]
-- ----------------------------------------------------

@[simp] def repite : ℕ → α → list α
| 0 x        := []
| (succ n) x := x :: repite n x

-- #eval repite 3 7

-- ----------------------------------------------------
-- Ejermplo 7.b. Demostrar los siguientes lemas
-- + repite_cero :
--     repite 0 x = []
-- + repite_suc :
--     repite (succ n) x = x :: repite n x
-- ----------------------------------------------------

lemma repite_cero :
  repite 0 x = [] :=
rfl

lemma repite_suc :
  repite (succ n) x = x :: repite n x :=
rfl

-- ----------------------------------------------------
-- Ejemplo 8. (p. 18) Demostrar que
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
          = longitud []
              : by rw repite_cero
      ... = 0
              : by rw longitud_nil },
  { calc
      longitud (repite (succ n) x)
          = longitud (x :: repite n x)
              : by rw repite_suc
      ... = longitud (repite n x) + 1
              : by rw longitud_cons
      ... = n + 1
              : by rw HI
      ... = succ n
              : rfl, },
end

-- 6ª demostración
example : longitud (repite n x) = n :=
nat.rec_on n
  ( show longitud (repite 0 x) = 0, from
      calc
        longitud (repite 0 x)
            = longitud []
                : by rw repite_cero
        ... = 0
                : by rw longitud_nil )
  ( assume n,
    assume HI : longitud (repite n x) = n,
    show longitud (repite (succ n) x) = succ n, from
      calc
      longitud (repite (succ n) x)
          = longitud (x :: repite n x)
              : by rw repite_suc
      ... = longitud (repite n x) + 1
              : by rw longitud_cons
      ... = n + 1
              : by rw HI
      ... = succ n
              : rfl )

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
        = longitud ([] : list α)
          : by rw repite_cero
    ... = 0
          : by rw longitud_nil
| (n+1) := by calc
    longitud (repite (n + 1) x)
        = longitud (x :: repite n x)
          : by rw repite_suc
    ... = longitud (repite n x) + 1
          : by rw longitud_cons
    ... = n + 1
          : by rw longitud_repite_1

-- 8ª demostración
lemma longitud_repite_2 :
  ∀ n, longitud (repite n x) = n
| 0     := by simp
| (n+1) := by simp [*]

-- 9ª demostración (con predefinidas)
example : length (repeat x n) = n :=
-- by library_search
length_repeat x n

-- § Razonamiento por inducción sobre listas
-- =========================================

-- Para demostrar una propiedad para todas las listas
-- basta demostrar que la lista vacía tiene la
-- propiedad y que al añadir un elemento a una lista
-- que tiene la propiedad se obtiene otra lista que
-- también tiene la propiedad.
--
-- En Lean el principio de inducción sobre listas está
-- formalizado mediante el teorema list.rec_on que se
-- puede ver con
--    #check list.rec_on

-- ----------------------------------------------------
-- Ejemplo 9.a. Definir la función
--    conc :: list α → list α → list α
-- tal que (conc xs ys) es la concatención de las
-- listas xs e ys. Por ejemplo,
--    conc [1,4] [2,4,1,3] = [1,4,2,4,1,3]
-- ----------------------------------------------------

@[simp] def conc : list α → list α → list α
| []        ys := ys
| (x :: xs) ys := x :: (conc xs ys)

-- #eval conc [1,4] [2,4,1,3]

-- ----------------------------------------------------
-- Ejermplo 9.b. Demostrar los siguientes lemas
-- + conc_nil :
--     conc ([] : list α) ys = ys
-- + conc_cons :
--     conc (x :: xs) ys = x :: (conc xs ys)
-- ----------------------------------------------------

lemma conc_nil :
  conc ([] : list α) ys = ys :=
rfl

lemma conc_cons :
  conc (x :: xs) ys = x :: (conc xs ys) :=
rfl

-- ----------------------------------------------------
-- Ejemplo 10. (p. 24) Demostrar que
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
  { calc conc nil (conc ys zs)
         = conc ys zs            : by rw conc_nil
     ... = conc (conc nil ys) zs : by rw conc_nil, },
  { calc conc (x :: xs) (conc ys zs)
         = x :: conc xs (conc ys zs)
           : by rw conc_cons
     ... = x :: conc (conc xs ys) zs
           : by rw HI
     ... = conc (x :: conc xs ys) zs
           : by rw conc_cons
     ... = conc (conc (x :: xs) ys) zs
           : by rw ←conc_cons, },
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
  ( show conc nil (conc ys zs) = conc (conc nil ys) zs,
      from calc conc nil (conc ys zs)
                = conc ys zs
                    : by rw conc_nil
            ... = conc (conc nil ys) zs
                    : by rw conc_nil )
    ( assume x xs,
      assume HI : conc xs (conc ys zs) =
                  conc (conc xs ys) zs,
      show conc (x :: xs) (conc ys zs) =
           conc (conc (x :: xs) ys) zs, from
        calc conc (x :: xs) (conc ys zs)
             = x :: conc xs (conc ys zs)
               : by rw conc_cons
        ... = x :: conc (conc xs ys) zs
              : by rw HI
        ... = conc (x :: conc xs ys) zs
              : by rw conc_cons
        ... = conc (conc (x :: xs) ys) zs
              : by rw ←conc_cons)

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
        = conc ys zs
          : by rw conc_nil
    ... = conc (conc [] ys) zs
          : by rw conc_nil
| (x :: xs) := by calc
    conc (x :: xs) (conc ys zs)
        = x :: conc xs (conc ys zs)
          : by rw conc_cons
    ... = x :: conc (conc xs ys) zs
          : by rw conc_asoc_1
    ... = conc (x :: conc xs ys) zs
          : by rw conc_cons
    ... = conc (conc (x :: xs) ys) zs
          : by rw ←conc_cons

-- 8ª demostración
lemma conc_asoc_2 :
  ∀ xs, conc xs (conc ys zs) = conc (conc xs ys) zs
| []         := by simp
| (x :: xs)  := by simp [conc_asoc_2 xs]

-- 9ª demostración (con predefinas)
example :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs :=
-- by library_search
(append_assoc xs ys zs).symm

-- ----------------------------------------------------
-- Ejemplo 12. (p. 28) Demostrar que
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

-- 12ª demostración (con predefinida)
example : xs ++ [] = xs :=
-- by library_search
append_nil xs

-- ----------------------------------------------------
-- Ejemplo 13. (p. 30) Demostrar que
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
         = longitud ys
           : by rw conc_nil
     ... = 0 + longitud ys
           : by exact (zero_add (longitud ys)).symm
     ... = longitud [] + longitud ys
           : by rw longitud_nil },
  { calc longitud (conc (x :: xs) ys)
         = longitud (x :: conc xs ys)
           : by rw conc_cons
     ... = longitud (conc xs ys) + 1
           : by rw longitud_cons
     ... = (longitud xs + longitud ys) + 1
           : by rw HI
     ... = (longitud xs + 1) + longitud ys
           : by exact add_right_comm (longitud xs) (longitud ys) 1
     ... = longitud (x :: xs) + longitud ys
           : by rw longitud_cons, },
end

-- 8ª demostración
example :
  longitud (conc xs ys) = longitud xs + longitud ys :=
list.rec_on xs
  ( show longitud (conc [] ys) =
         longitud [] + longitud ys, from
      calc longitud (conc [] ys)
           = longitud ys
             : by rw conc_nil
       ... = 0 + longitud ys
             : by exact (zero_add (longitud ys)).symm
       ... = longitud [] + longitud ys
             : by rw longitud_nil )
  ( assume x xs,
    assume HI : longitud (conc xs ys) =
                longitud xs + longitud ys,
    show longitud (conc (x :: xs) ys) =
         longitud (x :: xs) + longitud ys, from
      calc longitud (conc (x :: xs) ys)
           = longitud (x :: conc xs ys)
             : by rw conc_cons
       ... = longitud (conc xs ys) + 1
             : by rw longitud_cons
       ... = (longitud xs + longitud ys) + 1
             : by rw HI
       ... = (longitud xs + 1) + longitud ys
             : by exact add_right_comm (longitud xs) (longitud ys) 1
       ... = longitud (x :: xs) + longitud ys
             : by rw longitud_cons)

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
        = longitud ys
          : by rw conc_nil
    ... = 0 + longitud ys
          : by rw zero_add
    ... = longitud [] + longitud ys
          : by rw longitud_nil
| (x :: xs) := by calc
    longitud (conc (x :: xs) ys)
        = longitud (x :: conc xs ys)
          : by rw conc_cons
    ... = longitud (conc xs ys) + 1
          : by rw longitud_cons
    ... = (longitud xs + longitud ys) + 1
          : by rw longitud_conc_1
    ... = (longitud xs + 1) + longitud ys
          : by exact add_right_comm (longitud xs) (longitud ys) 1
    ... = longitud (x :: xs) + longitud ys
          : by rw longitud_cons

-- 11ª demostración
lemma longitud_conc_2 :
  ∀ xs, longitud (conc xs ys) = longitud xs + longitud ys
| []        := by simp
| (x :: xs) := by simp [longitud_conc_2 xs,
                        add_right_comm]

-- 12ª demostración /con predefinidas)
example :
  length (xs ++ ys) = length xs + length ys :=
-- by library_search
length_append xs ys

-- § Inducción correspondiente a la definición recursiva
-- =====================================================

-- ----------------------------------------------------
-- Ejemplo 14.a. Definir la función
--    coge : ℕ → list α → list α
-- tal que (coge n xs) es la lista de los n primeros
-- elementos de xs. Por ejemplo,
--    coge 2 [1,4,2,7,0] =  [1,4]
-- ----------------------------------------------------

@[simp] def coge : ℕ → list α → list α
| 0        xs        := []
| (succ n) []        := []
| (succ n) (x :: xs) := x :: coge n xs

-- #eval coge 2 [1,4,2,7]

-- ----------------------------------------------------
-- Ejermplo 14.b. Demostrar los siguientes lemas
-- + coge_cero :
--      coge 0 xs = []
-- + coge_nil :
--      coge n [] = []
-- + coge_cons :
--      coge (succ n) (x :: xs) = x :: coge n xs
-- ----------------------------------------------------

lemma coge_cero :
  coge 0 xs = [] :=
rfl

lemma coge_nil :
  ∀ n, coge n ([] : list α) = []
| 0     := rfl
| (n+1) := rfl

lemma coge_cons :
  coge (succ n) (x :: xs) = x :: coge n xs :=
rfl

-- ----------------------------------------------------
-- Ejemplo 15.a. Definir la función
--    elimina : ℕ → list α → list α
-- tal que (elimina n xs) es la lista obtenida eliminando los n primeros
-- elementos de xs. Por ejemplo,
--    elimina 2 [1,4,2,7,0] = [2,7,0]
-- ----------------------------------------------------

@[simp] def elimina : ℕ → list α → list α
| 0        xs        := xs
| (succ n) []        := []
| (succ n) (x :: xs) := elimina n xs

-- #eval elimina 2 [1,4,2,7,0]

-- ----------------------------------------------------
-- Ejermplo 15.b. Demostrar los siguientes lemas
-- + elimina_cero :
--      elimina 0 xs = xs
-- + elimina_nil :
--      elimina n [] = []
-- + elimina_cons :
--      elimina (succ n) (x :: xs) = elimina n xs
-- ----------------------------------------------------

lemma elimina_cero :
  elimina 0 xs = xs :=
rfl

lemma elimina_nil :
  ∀ n, elimina n ([] : list α) = []
| 0     := rfl
| (n+1) := rfl

lemma elimina_cons :
  elimina (succ n) (x :: xs) = elimina n xs :=
rfl

-- ----------------------------------------------------
-- Ejemplo 16. (p. 35) Demostrar que
--    conc (coge n xs) (elimina n xs) = xs
-- ----------------------------------------------------

-- 1ª demostración
lemma conc_coge_elimina_1 :
  ∀ (n : ℕ) (xs : list α),
  conc (coge n xs) (elimina n xs) = xs
| 0 xs := by calc
    conc (coge 0 xs) (elimina 0 xs)
        = conc [] (elimina 0 xs)
          : by rw coge_cero
    ... = conc [] xs
          : by rw elimina_cero
    ... = xs
          : by rw conc_nil
| (succ n) [] := by calc
    conc (coge (succ n) []) (elimina (succ n) [])
        = conc ([] : list α) (elimina (succ n) [])
          : by rw coge_nil
    ... = conc [] []
          : by rw elimina_nil
    ... = []
          : by rw conc_nil
| (succ n) (x :: xs) := by calc
    conc (coge (succ n) (x :: xs)) (elimina (succ n) (x :: xs))
        = conc (x :: coge n xs) (elimina (succ n) (x :: xs))
          : by rw coge_cons
    ... = conc (x :: coge n xs) (elimina n xs)
          : by rw elimina_cons
    ... = x :: conc (coge n xs) (elimina n xs)
          : by rw conc_cons
    ... = x :: xs
          : by rw conc_coge_elimina_1

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

-- 4ª demostración (usando predefinidas)
example : take n xs ++ drop n xs = xs :=
-- by library_search
take_append_drop n xs

-- § Razonamiento por casos
-- ========================

-- ----------------------------------------------------
-- Ejemplo 17.a. Definir la función
--    esVacia : list α → bool
-- tal que (esVacia xs) se verifica si xs es la lista vacía. Por ejemplo,
--    esVacia []  = tt
--    esVacia [1] = ff
-- ----------------------------------------------------

@[simp] def esVacia : list α → bool
| [] := tt
| _  := ff

-- #eval esVacia ([] : list ℕ)
-- #eval esVacia [1]

-- ----------------------------------------------------
-- Ejermplo 17.b. Demostrar los siguientes lemas
-- + coge_cero :
--      coge 0 xs = []
-- + coge_nil :
--      coge n [] = []
-- + coge_cons :
--      coge (succ n) (x :: xs) = x :: coge n xs
-- ----------------------------------------------------

lemma esVacia_nil :
  esVacia ([] : list α) = tt :=
rfl

lemma esVacia_cons :
  esVacia (x :: xs) = ff :=
rfl

-- ----------------------------------------------------
-- Ejemplo 18 (p. 39) . Demostrar que
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
    esVacia [] = esVacia (conc [] [])
    : by rw conc_nil
| (x :: xs) := by calc
    esVacia (x :: xs)
        = ff
          : by rw esVacia_cons
    ... = esVacia (x :: conc xs (x :: xs))
          : by rw esVacia_cons
    ... = esVacia (conc (x :: xs) (x :: xs))
          : by rw conc_cons

-- 3ª demostración
lemma esVacia_conc_2
  : ∀ xs : list α, esVacia xs = esVacia (conc xs xs)
| []        := by simp
| (x :: xs) := by simp

-- 3ª demostración
example : esVacia xs = esVacia (conc xs xs) :=
by cases xs ; simp

-- § Heurística de generalización
-- ==============================

-- ----------------------------------------------------
-- Ejemplo 19. Definir la función
--    inversaAc : list α → list α
-- tal que (inversaAc xs) es a inversa de xs calculada
-- usando acumuladores. Por ejemplo,
--    inversaAc [1,3,2,5] = [5,3,2,1]
-- ----------------------------------------------------

@[simp] def inversaAcAux : list α → list α → list α
| []        ys := ys
| (x :: xs) ys := inversaAcAux xs (x :: ys)

@[simp] def inversaAc : list α → list α :=
λ xs, inversaAcAux xs []

-- #eval inversaAc [1,3,2,5]

lemma inversaAcAux_nil :
  inversaAcAux [] ys = ys :=
rfl

lemma inversaAcAux_cons :
  inversaAcAux (x :: xs) ys =
  inversaAcAux xs (x :: ys) :=
rfl

-- [Ejemplo de equivalencia entre las definiciones]
-- La inversa de [a,b,c] es lo mismo calculada con la
-- primera definición
-- que con la segunda.

example : inversaAc [1,2,3] = inversa [1,2,3] :=
rfl

-- Nota [Ejemplo fallido de demostración por inducción]
-- El siguiente intento de demostrar que para cualquier
-- lista xs, se tiene que  "inversaAc xs = inversa xs"
-- falla.

/-
example : inversaAc xs = inversa xs :=
begin
  induction xs with x xs HI,
  { simp, },
  { simp,
    sorry, },
end
-/

-- Nota. [Heurística de generalización]
-- Cuando se use demostración estructural, cuantificar
-- universalmente las  variables libres.

-- ----------------------------------------------------
-- Ejemplo 20. (p. 44) Demostrar que
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
         = ys
           : by rw inversaAcAux_nil
     ... = [] ++ ys
           : by rw nil_append
     ... = inversa [] ++ ys
           : by rw inversa_nil },
  { calc inversaAcAux (x :: xs) ys
         = inversaAcAux xs (x :: ys)
           : by rw inversaAcAux_cons
     ... = inversa xs ++ (x :: ys)
           : by rw (HI (x :: ys))
     ... = inversa xs ++ ([x] ++ ys)
           : by rw singleton_append
     ... = (inversa xs ++ [x]) ++ ys
           : by rw append_assoc
     ... = inversa (x :: xs) ++ ys
           : by rw inversa_cons },
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
-- Ejemplo 21. (p. 43) Demostrar que
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

-- § Inducción para funciones de orden superior
-- ============================================

-- ----------------------------------------------------
-- Ejemplo 22.a. Definir la función
--    suma : list ℕ → ℕ
-- tal que (suma xs) es la suma de los elementos de
-- xs. Por ejemplo,
--    suma [3,2,5] = 10
-- ----------------------------------------------------

@[simp] def suma : list ℕ → ℕ
| []        := 0
| (n :: ns) := n + suma ns

-- #eval sum [3,2,5]

-- ----------------------------------------------------
-- Ejermplo 22.b. Demostrar los siguientes lemas
-- + suma_nil :
--      suma ([] : list ℕ) = 0 :=
-- + suma_cons :
--      suma (n :: ns) = n + suma ns :=
-- ----------------------------------------------------

lemma suma_nil :
  suma ([] : list ℕ) = 0 :=
rfl

lemma suma_cons :
  suma (n :: ns) = n + suma ns :=
rfl

-- ----------------------------------------------------
-- Ejemplo 23.a Definir la función
--    aplica_a_todos : (α → β) → list α → 'b list
-- tal que (aplica_a_todos f xs) es la lista obtenida
-- aplicando la función f a los elementos de xs. Por
-- ejemplo,
--    aplica_a_todos (λx, 2*x) [3,2,5] = [6,4,10]
--    aplica_a_todos ((*) 2)   [3,2,5] = [6,4,10]
--    aplica_a_todos ((+) 2)   [3,2,5] = [5,4,7]
-- ----------------------------------------------------

@[simp] def aplica_a_todos : (α → β) → list α → list β
| f []        := []
| f (x :: xs) := (f x) :: aplica_a_todos f xs

-- #eval aplica_a_todos (λx, 2*x) [3,2,5]
-- #eval aplica_a_todos ((*) 2) [3,2,5]
-- #eval aplica_a_todos ((+) 2) [3,2,5]

-- ----------------------------------------------------
-- Ejermplo 23.b. Demostrar los siguientes lemas
-- + aplica_a_todos_nil :
--      aplica_a_todos ([] : list ℕ) = 0 :=
-- + aplica_a_todos_cons :
--      aplica_a_todos (n :: ns) = n + aplica_a_todos ns :=
-- ----------------------------------------------------

lemma aplica_a_todos_nil
  (f : α → β)
  : aplica_a_todos f [] = [] :=
rfl

lemma aplica_a_todos_cons
  (f : α → β)
  : aplica_a_todos f (x :: xs) =
    (f x) :: aplica_a_todos f xs :=
rfl

-- ----------------------------------------------------
-- Ejemplo 24. (p. 45) Demostrar que
--    suma (aplica_a_todos (λ x, 2*x) ns) = 2 * (suma ns)
-- ----------------------------------------------------

-- 1ª demostración
example :
  suma (aplica_a_todos (λ x, 2*x) ns) = 2 * (suma ns) :=
begin
  induction ns with n ns HI,
  { rw aplica_a_todos_nil,
    rw suma_nil,
    rw mul_zero, },
  { rw aplica_a_todos_cons,
    rw suma_cons,
    rw HI,
    rw suma_cons,
    rw mul_add, },
end

-- 2ª demostración
example :
  suma (aplica_a_todos (λ x, 2*x) ns) = 2 * (suma ns) :=
begin
  induction ns with n ns HI,
  { calc suma (aplica_a_todos (λ (x : ℕ), 2 * x) [])
         = suma []
           : by rw aplica_a_todos_nil
     ... = 0
           : by rw suma_nil
     ... = 2 * 0
           : by rw mul_zero
     ... = 2 * suma []
           : by rw suma_nil, },
  { calc suma (aplica_a_todos (λ x, 2 * x) (n :: ns))
         = suma (2 * n :: aplica_a_todos (λ x, 2 * x) ns)
           : by rw aplica_a_todos_cons
     ... = 2 * n + suma (aplica_a_todos (λ x, 2 * x) ns)
           : by rw suma_cons
     ... = 2 * n + 2 * suma ns
           : by rw HI
     ... = 2 * (n + suma ns)
           : by rw mul_add
     ... = 2 * suma (n :: ns)
           : by rw suma_cons, },
end

-- 3ª demostración
example :
  suma (aplica_a_todos (λ x, 2*x) ns) = 2 * (suma ns) :=
by induction ns ; simp [*, mul_add]

-- ----------------------------------------------------
-- Ejemplo 25. (p. 48) Demostrar que
--    longitud (aplica_a_todos f xs) = longitud xs
-- ----------------------------------------------------

-- 1ª demostración
example
  (f : α → β)
  : longitud (aplica_a_todos f xs) = longitud xs :=
begin
  induction xs with x xs HI,
  { rw aplica_a_todos_nil,
    rw longitud_nil,
    rw longitud_nil, },
  { rw aplica_a_todos_cons,
    rw longitud_cons,
    rw HI,
    rw longitud_cons, },
end

-- 2ª demostración
example
  (f : α → β)
  : longitud (aplica_a_todos f xs) = longitud xs :=
begin
  induction xs with x xs HI,
  { calc longitud (aplica_a_todos f [])
         = longitud []
           : by rw aplica_a_todos_nil
     ... = 0
           : by rw longitud_nil
     ... = longitud []
           : by rw longitud_nil, },
  { calc longitud (aplica_a_todos f (x :: xs))
         = longitud (f x :: aplica_a_todos f xs)
           : by rw aplica_a_todos_cons
     ... = longitud (aplica_a_todos f xs) + 1
           : by rw longitud_cons
     ... = longitud xs + 1
           : by rw HI
     ... = longitud (x :: xs)
           : by rw longitud_cons, },
end

-- 3ª demostración
example
  (f : α → β)
  : longitud (aplica_a_todos f xs) = longitud xs :=
by induction xs ; simp [*]

-- § Referencias
-- =============

-- + J.A. Alonso. "Razonamiento sobre programas" http://goo.gl/R06O3
-- + G. Hutton. "Programming in Haskell". Cap. 13 "Reasoning about
--   programms".
-- + S. Thompson. "Haskell: the Craft of Functional Programming, 3rd
--   Edition. Cap. 8 "Reasoning about programms".
-- + L. Paulson. "ML for the Working Programmer, 2nd Edition". Cap. 6.
--   "Reasoning about functional programs".
