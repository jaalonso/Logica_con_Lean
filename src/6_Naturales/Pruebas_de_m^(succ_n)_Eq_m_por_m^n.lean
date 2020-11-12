-- Pruebas de m^(succ n) = m * m^n
-- ===============================

import data.nat.basic
open nat

variables (m n : ℕ)

#print nat
#print pow

theorem pow_succ' : m^(succ n) = m * m^n :=
nat.rec_on n
  (show m^(succ 0) = m * m^0, from calc
    m^(succ 0) = m^0 * m : by rw nat.pow_succ
           ... = 1 * m   : by rw nat.pow_zero
           ... = m       : by rw one_mul
           ... = m * 1   : by rw mul_one
           ... = m * m^0 : by rw nat.pow_zero)
  (assume n,
    assume ih : m^(succ n) = m * m^n,
    show m^(succ (succ n)) = m * m^(succ n), from calc
      m^(succ (succ n)) = m^(succ n) * m   : by rw nat.pow_succ
                    ... = (m * m^n) * m    : by rw ih
                    ... = m * (m^n * m)    : by rw mul_assoc
                    ... = m * m^(succ n)   : by rw nat.pow_succ)
