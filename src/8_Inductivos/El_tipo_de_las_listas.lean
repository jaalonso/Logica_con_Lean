-- El tipo de las listas
-- =====================

import tactic

variable {α : Type}

-- ----------------------------------------------------
-- Ejercicio 1. Definir el tipo Lista con elementos de
-- tipo α con los constructores NIl (para la lista
-- vacía y Cons (para añadir un elemento al principio
-- de una lista).
-- ----------------------------------------------------

inductive Lista (α : Type*)
| Nil  : Lista
| Cons : α → Lista → Lista

-- #print prefix Lista

-- ----------------------------------------------------
-- Ejercicio 2. Abrir el espacio de nombre Lista.
-- ----------------------------------------------------

namespace Lista

-- ----------------------------------------------------
-- Ejercicio 3. Definir la función
--    repr : Lista α → string
-- tal que (repr xs) es la cadena que representa a la
-- lista xs. Por ejemplo,
--     repr (Cons 3 (Cons 7 (Cons 5 Nil)))
--     Da: "(Cons 3 (Cons 7 (Cons 5 Nil)))"
-- ----------------------------------------------------

def repr [has_repr α] : Lista α → string
| Nil         := "Nil"
| (Cons x xs) := "(Cons " ++ has_repr.repr x ++ " " ++ repr xs ++ ")"

-- #eval repr (Cons 3 (Cons 7 (Cons 5 Nil)))
-- Da: "(Cons 3 (Cons 7 (Cons 5 Nil)))"

-- ----------------------------------------------------
-- Ejercicio 4. Declarar repr la función para
-- representar listas. Por ejemplo,
--    #eval Cons 3 (Cons 7 (Cons 5 Nil))
--    Da: (Cons 3 (Cons 7 (Cons 5 Nil)))
-- ----------------------------------------------------

instance [has_repr α] : has_repr (Lista α) := ⟨repr⟩

-- #eval Cons 3 (Cons 7 (Cons 5 Nil))
-- Da: (Cons 3 (Cons 7 (Cons 5 Nil)))

-- ----------------------------------------------------
-- Ejercicio 5. Declarar x como variable sobre
-- elementos de tipo α y xs e ys como variables sobre
-- listas de elementos de tipo α
-- ----------------------------------------------------

variable  (x : α)
variables (xs ys : Lista α)

-- ----------------------------------------------------
-- Ejercicio 6. Definir la función
--    longitud : Lista α → ℕ
-- tal que (longitud xs) es la longitud de la lista
-- xs. Por ejemplo,
--    longitud (Cons 2 (Cons 3 (Cons 5 Nil))) =  3
-- ----------------------------------------------------

def longitud : Lista α → ℕ
| Nil         := 0
| (Cons _ xs) := 1 + longitud xs

-- #eval longitud (Cons 2 (Cons 3 (Cons 5 Nil))) -- =  3

-- ----------------------------------------------------
-- Ejercicio 7. Demostrar los siguientes lemas
-- + longitud_nil :
--      longitud (Nil : Lista α) = 0
-- + longitud_cons :
--     longitud (Cons x xs) = 1 + longitud xs
-- ----------------------------------------------------

@[simp]
lemma longitud_nil :
  longitud (Nil : Lista α) = 0 :=
rfl

@[simp]
lemma longitud_cons :
  longitud (Cons x xs) = 1 + longitud xs :=
rfl

-- ----------------------------------------------------
-- Ejercicio 8. Definir la función
--    conc : Lista α → Lista α → Lista α
-- tal que (conc xs ys) es la concatenación de las
-- listas xs e ys. Por ejemplo,
--    conc (Cons 2 (Cons 3 Nil)) (Cons 7 (Cons 1 Nil))
--    Da: (Cons 2 (Cons 3 (Cons 7 (Cons 1 Nil))))
-- ----------------------------------------------------

def conc : Lista α → Lista α → Lista α
| Nil         ys := ys
| (Cons x xs) ys := Cons x (conc xs ys)

-- #eval conc (Cons 2 (Cons 3 Nil)) (Cons 7 (Cons 1 Nil))
-- Da: (Cons 2 (Cons 3 (Cons 7 (Cons 1 Nil))))

-- ----------------------------------------------------
-- Ejercicio 9. Demostrar los siguientes lemas
-- + conc_nil :
--      conc Nil ys = ys
-- + conc_cons :
--      conc (Cons x xs) ys = Cons x (conc xs ys)
-- ----------------------------------------------------

@[simp]
lemma  conc_nil :
  conc Nil ys = ys :=
rfl

@[simp]
lemma conc_cons :
   conc (Cons x xs) ys = Cons x (conc xs ys) :=
rfl

-- ----------------------------------------------------
-- Ejercicio 11. Demostrar que
--    longitud (conc xs ys) = longitud xs + longitud ys
-- ----------------------------------------------------

-- Para que no use la notación con puntos
set_option pp.structure_projections false

-- 1ª demostración
example :
  longitud (conc xs ys) = longitud xs + longitud ys :=
begin
  induction xs with a as HI,
  { rw conc_nil,
    rw longitud_nil,
    rw nat.zero_add, },
  { rw conc_cons,
    rw longitud_cons,
    rw HI,
    rw longitud_cons,
    rw add_assoc, },
end

-- 2ª demostración
example :
  longitud (conc xs ys) = longitud xs + longitud ys :=
begin
  induction xs with a as HI,
  { simp, },
  { simp [HI, add_assoc], },
end

-- 3ª demostración
example :
  longitud (conc xs ys) = longitud xs + longitud ys :=
begin
  induction xs with a as HI,
  { simp, },
  { finish [HI],},
end

-- 4ª demostración
example :
  longitud (conc xs ys) = longitud xs + longitud ys :=
by induction xs ; finish [*]

-- 5ª demostración
example :
  longitud (conc xs ys) = longitud xs + longitud ys :=
begin
  induction xs with a as HI,
  { calc longitud (conc Nil ys)
         = longitud ys                        : by rw conc_nil
     ... = 0 + longitud ys                    : by rw zero_add
     ... = longitud Nil + longitud ys         : by rw longitud_nil },
  { calc longitud (conc (Cons a as) ys)
         = longitud (Cons a (conc as ys))     : by rw conc_cons
     ... = 1 + longitud (conc as ys)          : by rw longitud_cons
     ... = 1 + (longitud as + longitud ys)    : by rw HI
     ... = (1 + longitud as) + longitud ys    : by rw add_assoc
     ... = longitud (Cons a as) + longitud ys : by rw longitud_cons, },
end

-- 6ª demostración
example :
  longitud (conc xs ys) = longitud xs + longitud ys :=
Lista.rec_on xs
  ( show longitud (conc Nil ys) = longitud Nil + longitud ys, from
      calc longitud (conc Nil ys)
           = longitud ys                      : by rw conc_nil
       ... = 0 + longitud ys                  : by exact (zero_add (longitud ys)).symm
       ... = longitud Nil + longitud ys       : by rw longitud_nil )
  ( assume a as,
    assume HI : longitud (conc as ys) = longitud as + longitud ys,
    show longitud (conc (Cons a as) ys) = longitud (Cons a as) + longitud ys, from
      calc longitud (conc (Cons a as) ys)
           = longitud (Cons a (conc as ys))     : by rw conc_cons
       ... = 1 + longitud (conc as ys)          : by rw longitud_cons
       ... = 1 + (longitud as + longitud ys)    : by rw HI
       ... = (1 + longitud as) + longitud ys    : by rw add_assoc
       ... = longitud (Cons a as) + longitud ys : by rw longitud_cons)

-- 7ª demostración
example :
  longitud (conc xs ys) = longitud xs + longitud ys :=
Lista.rec_on xs
  ( by simp)
  ( λ a as HI, by simp [HI, add_assoc])

-- 8ª demostración
lemma longitud_conc_1 :
  ∀ xs, longitud (conc xs ys) = longitud xs + longitud ys
| Nil := by calc
    longitud (conc Nil ys)
        = longitud ys                      : by rw conc_nil
    ... = 0 + longitud ys                  : by rw zero_add
    ... = longitud Nil + longitud ys       : by rw longitud_nil
| (Cons a as) := by calc
    longitud (conc (Cons a as) ys)
        = longitud (Cons a (conc as ys))     : by rw conc_cons
    ... = 1 + longitud (conc as ys)          : by rw longitud_cons
    ... = 1 + (longitud as + longitud ys)    : by rw longitud_conc_1
    ... = (1 + longitud as ) + longitud ys   : by rw add_assoc
    ... = longitud (Cons a as) + longitud ys : by rw longitud_cons

-- 9ª demostración
lemma longitud_conc_2 :
  ∀ xs, longitud (conc xs ys) = longitud xs + longitud ys
| Nil         := by simp
| (Cons a as) := by simp [longitud_conc_2 as, add_assoc]

-- ----------------------------------------------------
-- Ejercicio 12. Cerrar el espacio de nombre Lista.
-- ----------------------------------------------------

end Lista
