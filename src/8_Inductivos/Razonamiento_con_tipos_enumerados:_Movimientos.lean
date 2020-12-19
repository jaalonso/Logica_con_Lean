-- Razonamiento con tipos enumerados: Movimientos
-- ==============================================

import tactic

-- ----------------------------------------------------
-- Nota. Usaremos los tipo Pos (como una abreviatura
-- de pares de enteros para representar posiciones) y
-- Direccion (como un tipo enumerado con las cuatro
-- direcciones) y la función opuesta, definidas
-- anteriormente
-- ----------------------------------------------------

abbreviation Pos : Type := ℤ × ℤ

inductive Direccion : Type
| Izquierda : Direccion
| Derecha   : Direccion
| Arriba    : Direccion
| Abajo     : Direccion

namespace Direccion

@[simp]
def opuesta : Direccion → Direccion
| Izquierda := Derecha
| Derecha   := Izquierda
| Arriba    := Abajo
| Abajo     := Arriba

-- ----------------------------------------------------
-- Ejercicio ?. Definir la función
--    movimiento : Direccion → Pos → Pos
-- tal que (movimiento d p) es la posición alcanzada
-- al dar un paso en la dirección d a partir de la
-- posición p. Por ejemplo,
--    movimiento Arriba (2,5) = (2, 6)
-- ----------------------------------------------------

@[simp]
def movimiento : Direccion → Pos → Pos
| Izquierda (x,y) := (x-1,y)
| Derecha   (x,y) := (x+1,y)
| Arriba    (x,y) := (x,y+1)
| Abajo     (x,y) := (x,y-1)

-- #eval movimiento Arriba (2,5)
-- Da: (2, 6)

-- ----------------------------------------------------
-- Ejercicio ?. Definir la función
--    movimientos : list Direccion → Pos → Pos
-- tal que (movimientos ms p) es la posición obtenida
-- aplicando la lista de movimientos ms a la posición
-- p. Por ejemplo,
--    movimientos [Arriba, Izquierda] (2,5) = (1,6)
-- ----------------------------------------------------

def movimientos : list Direccion → Pos → Pos
| []        p := p
| (m :: ms) p := movimientos ms (movimiento m p)

-- #eval movimientos [Arriba, Izquierda] (2,5)
-- Da:  (1,6)

-- ----------------------------------------------------
-- Ejercicio ?. Demostrar que para cada dirección d
-- existe una dirección d' tal que para toda posición p,
--    movimiento d' (movimiento d p) = p
-- ----------------------------------------------------

-- 1ª demostración
example :
  ∀ d, ∃ d', ∀ p, movimiento d' (movimiento d p) = p :=
begin
  intro d,
  use opuesta d,
  rintro ⟨x,y⟩,
  cases d,
  { calc movimiento (opuesta Izquierda) (movimiento Izquierda (x,y))
         = movimiento (opuesta Izquierda) (x-1,y)       :by simp [movimiento]
     ... = movimiento Derecha (x-1,y)                   :by simp [opuesta]
     ... = (x-1+1,y)                                    :by simp [movimiento]
     ... = (x,y)                                        :by simp },
  { calc movimiento (opuesta Derecha) (movimiento Derecha (x,y))
         = movimiento (opuesta Derecha) (x+1,y)         :by simp [movimiento]
     ... = movimiento Izquierda (x+1,y)                 :by simp [opuesta]
     ... = (x+1-1,y)                                    :by simp [movimiento]
     ... = (x,y)                                        :by simp },
  { calc movimiento (opuesta Arriba) (movimiento Arriba (x,y))
         = movimiento (opuesta Arriba) (x,y+1)          :by simp [movimiento]
     ... = movimiento Abajo (x,y+1)                     :by simp [opuesta]
     ... = (x,y+1-1)                                    :by simp [movimiento]
     ... = (x,y)                                        :by simp },
  { calc movimiento (opuesta Abajo) (movimiento Abajo (x,y))
         = movimiento (opuesta Abajo) (x,y-1)           :by simp [movimiento]
     ... = movimiento Arriba (x,y-1)                    :by simp [opuesta]
     ... = (x,y-1+1)                                    :by simp [movimiento]
     ... = (x,y)                                        :by simp },
end

-- 2ª demostración
example :
  ∀ d, ∃ d', ∀ p, movimiento d' (movimiento d p) = p :=
begin
  intro d,
  use opuesta d,
  rintro ⟨x,y⟩,
  cases d,
  { calc movimiento (opuesta Izquierda) (movimiento Izquierda (x,y))
         = movimiento (opuesta Izquierda) (x-1,y)       :by simp
     ... = movimiento Derecha (x-1,y)                   :by simp
     ... = (x-1+1,y)                                    :by simp
     ... = (x,y)                                        :by simp },
  { calc movimiento (opuesta Derecha) (movimiento Derecha (x,y))
         = movimiento (opuesta Derecha) (x+1,y)         :by simp
     ... = movimiento Izquierda (x+1,y)                 :by simp
     ... = (x+1-1,y)                                    :by simp
     ... = (x,y)                                        :by simp },
  { calc movimiento (opuesta Arriba) (movimiento Arriba (x,y))
         = movimiento (opuesta Arriba) (x,y+1)          :by simp
     ... = movimiento Abajo (x,y+1)                     :by simp
     ... = (x,y+1-1)                                    :by simp
     ... = (x,y)                                        :by simp },
  { calc movimiento (opuesta Abajo) (movimiento Abajo (x,y))
         = movimiento (opuesta Abajo) (x,y-1)           :by simp
     ... = movimiento Arriba (x,y-1)                    :by simp
     ... = (x,y-1+1)                                    :by simp
     ... = (x,y)                                        :by simp },
end

-- 3ª demostración
example :
  ∀ d, ∃ d', ∀ p, movimiento d' (movimiento d p) = p :=
begin
  intro d,
  use opuesta d,
  rintro ⟨x,y⟩,
  cases d,
  { simp, },
  { simp, },
  { simp, },
  { simp, },
end

-- 4ª demostración
example :
  ∀ d, ∃ d', ∀ p, movimiento d' (movimiento d p) = p :=
begin
  intro d,
  use opuesta d,
  rintro ⟨x,y⟩,
  cases d ;
  simp,
end

-- 5ª demostración
example :
  ∀ d, ∃ d', ∀ p, movimiento d' (movimiento d p) = p :=
assume d,
exists.intro (opuesta d)
  (assume ⟨x,y⟩,
   show movimiento (opuesta d) (movimiento d (x,y)) = (x,y), from
     Direccion.cases_on d
       (calc movimiento (opuesta Izquierda) (movimiento Izquierda (x,y))
             = movimiento (opuesta Izquierda) (x-1,y)       :by simp
         ... = movimiento Derecha (x-1,y)                   :by simp
         ... = (x-1+1,y)                                    :by simp
         ... = (x,y)                                        :by simp)
       (calc movimiento (opuesta Derecha) (movimiento Derecha (x,y))
             = movimiento (opuesta Derecha) (x+1,y)         :by simp
         ... = movimiento Izquierda (x+1,y)                 :by simp
         ... = (x+1-1,y)                                    :by simp
         ... = (x,y)                                        :by simp )
       (calc movimiento (opuesta Arriba) (movimiento Arriba (x,y))
             = movimiento (opuesta Arriba) (x,y+1)          :by simp
         ... = movimiento Abajo (x,y+1)                     :by simp
         ... = (x,y+1-1)                                    :by simp
         ... = (x,y)                                        :by simp)
       (calc movimiento (opuesta Abajo) (movimiento Abajo (x,y))
             = movimiento (opuesta Abajo) (x,y-1)           :by simp
         ... = movimiento Arriba (x,y-1)                    :by simp
         ... = (x,y-1+1)                                    :by simp
         ... = (x,y)                                        :by simp))

-- 6ª demostración
example :
  ∀ d, ∃ d', ∀ p, movimiento d' (movimiento d p) = p :=
assume d,
exists.intro (opuesta d)
  (assume ⟨x,y⟩,
   show movimiento (opuesta d) (movimiento d (x,y)) = (x,y), from
     Direccion.cases_on d
       (by simp)
       (by simp)
       (by simp)
       (by simp))

-- 7ª demostración
example :
  ∀ d, ∃ d', ∀ p, movimiento d' (movimiento d p) = p :=
assume d,
exists.intro (opuesta d)
  (λ ⟨x,y⟩, Direccion.cases_on d (by simp) (by simp) (by simp) (by simp))

-- 8ª demostración
example :
  ∀ d, ∃ d', ∀ p, movimiento d' (movimiento d p) = p :=
λ d, exists.intro (opuesta d)
       (λ ⟨x,y⟩, Direccion.cases_on d (by simp) (by simp) (by simp) (by simp))

end Direccion
