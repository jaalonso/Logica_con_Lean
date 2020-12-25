-- Operaciones aritméticas definidas
-- =================================

import data.nat.basic
open nat

variables m n : ℕ

-- Suma
-- #check @nat.add_zero m   -- : m + 0 = 0
-- #check @nat.add_succ m n -- : m + succ n = succ (m + n)

-- Producto
-- #check @nat.mul_zero m   -- : m * 0 = 0
-- #check @nat.mul_succ m n -- : m * succ n = n * n + m

-- Potencia
-- #check pow_zero m        -- : m ^ 0 = 1
-- #check pow_succ' m n     -- : m ^ succ n = m ^n * m

-- Predecesor
-- #check @pred_zero        -- : pred 0 = 0
-- #check @pred_succ n      -- : pred (succ n) = n
