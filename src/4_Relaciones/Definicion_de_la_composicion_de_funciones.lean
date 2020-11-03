-- Definición de la composición de funciones
-- =========================================

-- ----------------------------------------------------
-- Ej. 1. Definir la composición de dos funciones.
-- ----------------------------------------------------

namespace reservado

variables {X Y Z : Type}

def comp (f : Y → Z) (g : X → Y) : X → Z :=
λ x, f (g x)

infixr  ` ∘ ` := comp

end reservado

#print notation ∘
#print function.comp
