-- Razonamiento con tipos enumerados: Direcciones
-- ==============================================

import tactic

-- ----------------------------------------------------
-- Ejercicio 1. Definir el tipo Direccion cuyos
-- constructores son las cuatro direcciones
-- (Izquierda, Derecha, Arriba y Abajo).
-- ----------------------------------------------------

inductive Direccion : Type
| Izquierda : Direccion
| Derecha   : Direccion
| Arriba    : Direccion
| Abajo     : Direccion

-- ----------------------------------------------------
-- Ejercicio 2. Abrir el espacio de nombre Direccion.
-- ----------------------------------------------------

namespace Direccion

-- #print prefix Direccion

-- ----------------------------------------------------
-- Ejercicio 3. Definir la función
--    repr : Direccion → string
-- tal que (repr d) es la cadena que representa a la
-- dirección d. Por ejemplo,
--     repr Derecha = "Derecha"
-- ----------------------------------------------------

def repr : Direccion → string
| Izquierda := "Izquierda"
| Derecha   := "Derecha"
| Arriba    := "Arriba"
| Abajo     := "Abajo"

---#eval repr Derecha
-- Da: "Derecha"

-- ----------------------------------------------------
-- Ejercicio 4. Declarar repr la función para
-- representar direcciones. Por ejemplo,
--    #eval Derecha
-- da Derecha.
-- ----------------------------------------------------

instance : has_repr Direccion := ⟨repr⟩

-- #eval Derecha
-- Da: Derecha

-- ----------------------------------------------------
-- Ejercicio 5. Definir la función
--    opuesta : Direccion → Direccion
-- tal que (opuesta d) es la dirección opuesta de d. §
-- Por ejemplo,
--    opuesta Derecha = Izquierda
-- ----------------------------------------------------

@[simp]
def opuesta : Direccion → Direccion
| Izquierda := Derecha
| Derecha   := Izquierda
| Arriba    := Abajo
| Abajo     := Arriba

-- #eval opuesta Derecha
-- Da: Izquierda

-- ----------------------------------------------------
-- Ejercicio 6. Declarar d como una variable sobre
-- direcciones.
-- ----------------------------------------------------

variable (d : Direccion)

-- ----------------------------------------------------
-- Ejercicio 7. Demostrar que, para cualquier dirección
-- d, se tiene que
--    opuesta (opuesta d) = d
-- ----------------------------------------------------

-- 1ª demostración
example :
  opuesta (opuesta d) = d :=
begin
  cases d,
  { calc opuesta (opuesta Izquierda)
         = opuesta Derecha         :by simp [opuesta]
     ... = Izquierda               :by simp [opuesta], },
  { calc opuesta (opuesta Derecha)
         = opuesta Izquierda       :by simp [opuesta]
     ... = Derecha                 :by simp [opuesta], },
  { calc opuesta (opuesta Arriba)
         = opuesta Abajo           :by simp [opuesta]
     ... = Arriba                  :by simp [opuesta], },
  { calc opuesta (opuesta Abajo)
         = opuesta Arriba          :by simp [opuesta]
     ... = Abajo                   :by simp [opuesta], },
end

-- 2ª demostración
example :
  opuesta (opuesta d) = d :=
begin
  cases d,
  { calc opuesta (opuesta Izquierda)
         = opuesta Derecha         :by simp
     ... = Izquierda               :by simp, },
  { calc opuesta (opuesta Derecha)
         = opuesta Izquierda       :by simp
     ... = Derecha                 :by simp, },
  { calc opuesta (opuesta Arriba)
         = opuesta Abajo           :by simp
     ... = Arriba                  :by simp, },
  { calc opuesta (opuesta Abajo)
         = opuesta Arriba          :by simp
     ... = Abajo                   :by simp, },
end

-- 3ª demostración
example :
  opuesta (opuesta d) = d :=
begin
  cases d,
  { simp, },
  { simp, },
  { simp, },
  { simp, },
end

-- 4ª demostración
example :
  opuesta (opuesta d) = d :=
by cases d ; simp

-- 5ª demostración
example :
  opuesta (opuesta d) = d :=
Direccion.cases_on d
  (show opuesta (opuesta Izquierda) = Izquierda, from rfl)
  (show opuesta (opuesta Derecha)   = Derecha,   from rfl)
  (show opuesta (opuesta Arriba)    = Arriba,    from rfl)
  (show opuesta (opuesta Abajo)     = Abajo,     from rfl)

-- 6ª demostración
example :
  opuesta (opuesta d) = d :=
Direccion.cases_on d rfl rfl rfl rfl

-- 7ª demostración
example :
  opuesta (opuesta d) = d :=
by apply Direccion.cases_on d ; refl

-- 8ª demostración
example :
  opuesta (opuesta d) = d :=
by apply Direccion.rec_on d; refl

-- 9ª demostración
lemma opuesta_opuesta :
  ∀ d, opuesta (opuesta d) = d
| Izquierda := by simp
| Derecha   := by simp
| Arriba    := by simp
| Abajo     := by simp

-- ----------------------------------------------------
-- Ejercicio 8. Cerrar el espacio de nombre Direccion.
-- ----------------------------------------------------

end Direccion
