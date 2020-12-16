-- Razonamiento sobre arboles binarios: Aplanamiento e imagen especular
-- ====================================================================

import tactic
open list

variable {α : Type}

-- ----------------------------------------------------
-- Nota. Se usarán las definiciones de árboles e
-- imagen especular estudiadas anteriormente.
-- ----------------------------------------------------

inductive arbol (α : Type) : Type
| hoja : α → arbol
| nodo : α → arbol → arbol → arbol

namespace arbol

def ejArbol : arbol ℕ :=
  nodo 3 (nodo 2 (hoja 1) (hoja 5)) (hoja 4)

def repr [has_repr α] : arbol α → string
| (hoja x)     := "H " ++ has_repr.repr x
| (nodo x i d) := "N " ++ has_repr.repr x ++ " (" ++ repr i ++ ") (" ++ repr d ++ ")"

instance [has_repr α] : has_repr (arbol α) := ⟨repr⟩

def espejo : arbol α → arbol α
| (hoja x)     := hoja x
| (nodo x i d) := nodo x (espejo d) (espejo i)

variables (a i d : arbol α)
variable  (x : α)

@[simp]
lemma espejo_1 :
  espejo (hoja x) = hoja x :=
espejo.equations._eqn_1 x

@[simp]
lemma espejo_2 :
  espejo (nodo x i d) = nodo x (espejo d) (espejo i) :=
espejo.equations._eqn_2 x i d

-- ----------------------------------------------------
-- Ejercicio 1. Definir la función
--    aplana : arbol α → list α
-- tal que (aplana a) es la lista obtenida aplanando
-- el árbole a recorriéndolo en orden infijo. Por
-- ejemplo,
--    #eval aplana ejArbol
--    -- Da: [1, 2, 5, 3, 4]
-- ----------------------------------------------------

def aplana : arbol α → list α
| (hoja x)     := [x]
| (nodo x i d) := (aplana i) ++ [x] ++ (aplana d)

-- #eval aplana ejArbol
-- -- Da: [1, 2, 5, 3, 4]

-- ----------------------------------------------------
-- Ejercicio 7. Demostrar los siguientes lemas
-- + aplana_1 :
--      aplana (hoja x) = [x]
-- + aplana_2 :
--      aplana (nodo x i d) = (aplana i) ++ [x] ++ (aplana d)
-- ----------------------------------------------------

@[simp]
lemma aplana_1 :
  aplana (hoja x) = [x] :=
aplana.equations._eqn_1 x

@[simp]
lemma aplana_2 :
  aplana (nodo x i d) = (aplana i) ++ [x] ++ (aplana d) :=
aplana.equations._eqn_2 x i d

-- ----------------------------------------------------
-- Ejercicio 3. Demostrar que
--    aplana (espejo a) = rev (aplana a)
-- ----------------------------------------------------

-- 1ª demostración
example :
  aplana (espejo a) = reverse (aplana a) :=
begin
  induction a with x x i d Hi Hd,
  { rw espejo_1,
    rw aplana_1,
    rw reverse_singleton, },
  { rw espejo_2,
    rw aplana_2,
    rw [Hi, Hd],
    rw aplana_2,
    rw reverse_append,
    rw reverse_append,
    rw reverse_singleton,
    rw append_assoc, },
end

-- 2ª demostración
example :
  aplana (espejo a) = reverse (aplana a) :=
begin
  induction a with x x i d Hi Hd,
  { calc aplana (espejo (hoja x))
         = aplana (hoja x)
             :by simp only [espejo_1]
     ... = [x]
             :by rw aplana_1
     ... = reverse [x]
             :by rw reverse_singleton
     ... = reverse (aplana (hoja x))
             :by simp only [aplana_1], },
  { calc aplana (espejo (nodo x i d))
         = aplana (nodo x (espejo d) (espejo i))
             :by simp only [espejo_2]
     ... = aplana (espejo d) ++ [x] ++ aplana (espejo i)
             :by rw aplana_2
     ... = reverse (aplana d) ++ [x] ++ reverse (aplana i)
             :by rw [Hi, Hd]
     ... = reverse (aplana d) ++ reverse [x] ++ reverse (aplana i)
             :by simp only [reverse_singleton]
     ... = reverse ([x] ++ aplana d) ++ reverse (aplana i)
             :by simp only [reverse_append]
     ... = reverse (aplana i ++ ([x] ++ aplana d))
             :by simp only [reverse_append]
     ... = reverse (aplana i ++ [x] ++ aplana d)
             :by simp only [append_assoc]
     ... = reverse (aplana (nodo x i d))
             :by simp only [aplana_2], },
end

-- 3ª demostración
example :
  aplana (espejo a) = reverse (aplana a) :=
begin
  induction a with x x i d Hi Hd,
  { simp, },
  { simp [Hi, Hd], },
end

-- 4ª demostración
example :
  aplana (espejo a) = reverse (aplana a) :=
by induction a ; simp [*]

-- 5ª demostración
example :
  aplana (espejo a) = reverse (aplana a) :=
arbol.rec_on a
  ( assume x,
    calc aplana (espejo (hoja x))
         = aplana (hoja x)
             :by simp only [espejo_1]
     ... = [x]
             :by rw aplana_1
     ... = reverse [x]
             :by rw reverse_singleton
     ... = reverse (aplana (hoja x))
             :by simp only [aplana_1])
  ( assume x i d,
    assume Hi : aplana (espejo i) = reverse (aplana i),
    assume Hd : aplana (espejo d) = reverse (aplana d),
    calc aplana (espejo (nodo x i d))
         = aplana (nodo x (espejo d) (espejo i))
             :by simp only [espejo_2]
     ... = aplana (espejo d) ++ [x] ++ aplana (espejo i)
             :by rw aplana_2
     ... = reverse (aplana d) ++ [x] ++ reverse (aplana i)
             :by rw [Hi, Hd]
     ... = reverse (aplana d) ++ reverse [x] ++ reverse (aplana i)
             :by simp only [reverse_singleton]
     ... = reverse ([x] ++ aplana d) ++ reverse (aplana i)
             :by simp only [reverse_append]
     ... = reverse (aplana i ++ ([x] ++ aplana d))
             :by simp only [reverse_append]
     ... = reverse (aplana i ++ [x] ++ aplana d)
             :by simp only [append_assoc]
     ... = reverse (aplana (nodo x i d))
             :by simp only [aplana_2])

-- 6ª demostración
example :
  aplana (espejo a) = reverse (aplana a) :=
arbol.rec_on a
  (λ x, by simp)
  (λ x i d Hi Hd, by simp [Hi, Hd])

-- 7ª demostración
lemma aplana_espejo :
  ∀ a : arbol α, aplana (espejo a) = reverse (aplana a)
| (hoja x)     := by simp
| (nodo x i d) := by simp [aplana_espejo i,
                           aplana_espejo d]

-- ----------------------------------------------------
-- Ejercicio 4. Cerrar el espacio de nombres arbol.
-- ----------------------------------------------------

end arbol
