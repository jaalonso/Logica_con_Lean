-- Razonamiento sobre árboles binarios: La función espejo es involutiva
-- ====================================================================

import tactic

variable {α : Type}

-- ----------------------------------------------------
-- Ejercicio 1. Definir un tipo de dato para los
-- árboles binarios, con los constructores hoja y nodo.
-- ----------------------------------------------------

inductive arbol (α : Type) : Type
| hoja : α → arbol
| nodo : α → arbol → arbol → arbol

-- ----------------------------------------------------
-- Ejercicio 2. Abrir el espacio de nombres arbol
-- ----------------------------------------------------

namespace arbol

-- #print prefix arbol

-- ----------------------------------------------------
-- Ejercicio 3. Definir el árbol correspondiente a
--        3
--       / \
--      2   4
--     / \
--    1   5
-- ----------------------------------------------------

def ejArbol : arbol ℕ :=
  nodo 3 (nodo 2 (hoja 1) (hoja 5)) (hoja 4)

-- ----------------------------------------------------
-- Ejercicio 3. Definir la función
--    repr : arbol α → string
-- tal que (repr a) es la cadena que representa al
-- árbol a. Por ejemplo,
--     #eval repr ejArbol
--     Da: "N 3 (N 2 (H 1) (H 5)) (H 4)"
-- ----------------------------------------------------

def repr [has_repr α] : arbol α → string
| (hoja x)     := "H " ++ has_repr.repr x
| (nodo x i d) := "N " ++ has_repr.repr x ++ " (" ++ repr i ++ ") (" ++ repr d ++ ")"

-- #eval repr ejArbol

-- ----------------------------------------------------
-- Ejercicio 4. Declarar repr la función para
-- representar los árboles. Por ejemplo,
--    #eval ejArbol
--    -- Da: N 3 (N 2 (H 1) (H 5)) (H 4)
-- ----------------------------------------------------

instance [has_repr α] : has_repr (arbol α) := ⟨repr⟩

-- #eval ejArbol
-- -- Da: N 3 (N 2 (H 1) (H 5)) (H 4)

-- --------------------------------------------------------------
-- Ejercicio 5. Definir la función
--    espejo : arbol α → arbol α
-- tal que (espejo a) es la imagen especular de a. Por ejmplo,
--    #eval espejo ejArbol
--    -- Da: N 3 (H 4) (N 2 (H 5) (H 1))
-- ----------------------------------------------------

def espejo : arbol α → arbol α
| (hoja x)     := hoja x
| (nodo x i d) := nodo x (espejo d) (espejo i)

-- #eval espejo ejArbol
-- -- Da: N 3 (H 4) (N 2 (H 5) (H 1))

-- ----------------------------------------------------
-- Ejercicio 6. Declarar las siguientes variables:
-- + a i d como variables sobre árboles de tipo α.
-- + x como variable sobre elementos de tipo α.
-- ----------------------------------------------------

variables (a i d : arbol α)
variable  (x : α)

-- ----------------------------------------------------
-- Ejercicio 7. Demostrar los siguientes lemas
-- + espejo_1 :
--      espejo (hoja x) = hoja x
-- + espejo_2 :
--      espejo (nodo x i d) = nodo x (espejo d) (espejo i)
-- ----------------------------------------------------

@[simp]
lemma espejo_1 :
  espejo (hoja x) = hoja x :=
espejo.equations._eqn_1 x

@[simp]
lemma espejo_2 :
  espejo (nodo x i d) = nodo x (espejo d) (espejo i) :=
espejo.equations._eqn_2 x i d

-- ----------------------------------------------------
-- Ejercicio 8. Demostrar que
--    espejo (espejo a) = a
-- ----------------------------------------------------

-- 1ª demostración
example :
  espejo (espejo a) = a :=
begin
  induction a with x x i d Hi Hd,
  { rw espejo_1,
    rw espejo_1, },
  { rw espejo_2,
    rw espejo_2,
    rw Hi,
    rw Hd, },
end

-- 2ª demostración
example :
  espejo (espejo a) = a :=
begin
  induction a with x x i d Hi Hd,
  { calc espejo (espejo (hoja x))
         = espejo (hoja x)
             : by exact congr_arg espejo (espejo_1 x)
     ... = hoja x
             : by rw espejo_1, },
  { calc espejo (espejo (nodo x i d))
         = espejo (nodo x (espejo d) (espejo i))
             :by exact congr_arg espejo (espejo_2 i d x)
     ... = nodo x (espejo (espejo i)) (espejo (espejo d))
             :by rw espejo_2
     ... = nodo x i (espejo (espejo d))
             :by rw Hi
     ... = nodo x i d
             :by rw Hd, },
end

-- 3ª demostración
example :
  espejo (espejo a) = a :=
begin
  induction a with _ x i d Hi Hd,
  { simp, },
  { simp [Hi, Hd], },
end

-- 4ª demostración
example :
  espejo (espejo a) = a :=
by induction a ; simp [*]

-- 5ª demostración
example :
  espejo (espejo a) = a :=
arbol.rec_on a
  ( assume x,
    calc espejo (espejo (hoja x))
         = espejo (hoja x)
             : by exact congr_arg espejo (espejo_1 x)
     ... = hoja x
             : by rw espejo_1 )
  ( assume x i d,
    assume Hi : espejo (espejo i) = i,
    assume Hd : espejo (espejo d) = d,
    calc espejo (espejo (nodo x i d))
         = espejo (nodo x (espejo d) (espejo i))
             :by exact congr_arg espejo (espejo_2 i d x)
     ... = nodo x (espejo (espejo i)) (espejo (espejo d))
             :by rw espejo_2
     ... = nodo x i (espejo (espejo d))
             :by rw Hi
     ... = nodo x i d
             :by rw Hd )

-- 6ª demostración
example :
  espejo (espejo a) = a :=
arbol.rec_on a
  (λ x, by simp )
  (λ x i d Hi Hd, by simp [Hi,Hd])

-- 7ª demostración
lemma espejo_espejo :
  ∀ a : arbol α, espejo (espejo a) = a
| (hoja x)     := by simp
| (nodo x i d) := by simp [espejo_espejo i, espejo_espejo d]

-- ----------------------------------------------------
-- Ejercicio 9. Cerrar el espacio de nombres arbol.
-- ----------------------------------------------------

end arbol
