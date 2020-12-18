-- Razonamiento con tipos enumerados: Movimientos
-- ==============================================

import tactic

-- ----------------------------------------------------
-- Ejercicio 1. Definir el tipo Pos como una abreviatura
-- de pares de enteros para representar posiciones.
-- ----------------------------------------------------

abbreviation Pos : Type := ℤ × ℤ

inductive Direccion : Type
| Izquierda : Direccion
| Derecha   : Direccion
| Arriba    : Direccion
| Abajo     : Direccion

namespace Direccion

def movimiento : Direccion → Pos → Pos
| Izquierda (x,y) := (x-1,y)
| Derecha   (x,y) := (x+1,y)
| Arriba    (x,y) := (x,y+1)
| Abajo     (x,y) := (x,y-1)

-- #eval movimiento Arriba (2,5)
-- Da: (2, 6)

def movimientos : list Direccion → Pos → Pos
| []        p := p
| (m :: ms) p := movimientos ms (movimiento m p)

-- #eval movimientos [Arriba, Izquierda] (2,5)
-- Da:  (1,6)

def opuesta : Direccion → Direccion
| Izquierda := Derecha
| Derecha   := Izquierda
| Arriba    := Abajo
| Abajo     := Arriba

-- #eval movimiento (opuesta Arriba) (2,5)
-- Da (2, 4)

variable (d : Direccion)

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
attribute [simp] opuesta

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
by cases d; simp

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
by apply Direccion.cases_on d; refl

-- 8ª demostración
example :
  opuesta (opuesta d) = d :=
by apply Direccion.rec_on d; refl

-- ------------------------------------------------------------------------

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
attribute [simp] movimiento

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
