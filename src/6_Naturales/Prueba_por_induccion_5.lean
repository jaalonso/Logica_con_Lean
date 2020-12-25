-- Prueba por inducción 5: m^(succ n) = m * m^n
-- ============================================

-- ----------------------------------------------------
-- Ej. 1. Sean m y n números naturales. Demostrar que
--    m^(succ n) = m * m^n
-- ----------------------------------------------------

import data.nat.basic
open nat

variables (m n : ℕ)

-- #check nat.pow_zero
-- #check nat.pow_succ
-- #check nat.mul_one
-- #check nat.one_mul
-- #check nat.mul_assoc
-- #check nat.mul_comm

-- 1ª demostración
example : m^(succ n) = m * m^n :=
begin
  induction n with n HI,
  { rw pow_succ',
    rw pow_zero,
    rw nat.one_mul,
    rw nat.mul_one, },
  { rw pow_succ',
    rw HI,
    rw nat.mul_assoc,
    rw nat.mul_comm (m^n), },
end

-- 2ª demostración
example : m^(succ n) = m * m^n :=
begin
  induction n with n HI,
  rw [pow_succ', pow_zero, one_mul, mul_one],
  rw [pow_succ', HI, mul_assoc, mul_comm (m^n)],
end

-- 3ª demostración
example : m^(succ n) = m * m^n :=
begin
  induction n with n HI,
  { simp only [pow_succ', pow_zero, one_mul, mul_one]},
  { simp only [pow_succ', HI, mul_assoc, mul_comm (m^n)]},
end

-- 4ª demostración
example : m^(succ n) = m * m^n :=
by induction n;
   simp only [*,
              pow_succ',
              pow_zero,
              nat.one_mul,
              nat.mul_one,
              nat.mul_assoc,
              nat.mul_comm]

-- 5ª demostración
example : m^(succ n) = m * m^n :=
by induction n;
   simp [*,
         pow_succ',
         mul_comm]

-- 6ª demostración
example : m^(succ n) = m * m^n :=
begin
  induction n with n HI,
  { simp, },
  { simp [pow_succ', HI],
    cc, },
end

-- 7ª demostración
example : m^(succ n) = m * m^n :=
begin
  induction n with n HI,
  { calc
      m^(succ 0)
          = m^0 * m : by rw pow_succ'
      ... = 1 * m   : by rw pow_zero
      ... = m       : by rw nat.one_mul
      ... = m * 1   : by rw nat.mul_one
      ... = m * m^0 : by rw pow_zero, },
  { calc
      m^(succ (succ n))
          = m^(succ n) * m   : by rw pow_succ'
      ... = (m * m^n) * m    : by rw HI
      ... = m * (m^n * m)    : by rw nat.mul_assoc
      ... = m * m^(succ n)   : by rw pow_succ', },
end

-- 8ª demostración
example : m^(succ n) = m * m^n :=
nat.rec_on n
  (show m^(succ 0) = m * m^0, from calc
    m^(succ 0) = m^0 * m : by rw pow_succ'
           ... = 1 * m   : by rw pow_zero
           ... = m       : by rw one_mul
           ... = m * 1   : by rw mul_one
           ... = m * m^0 : by rw pow_zero)
  (assume n,
    assume HI : m^(succ n) = m * m^n,
    show m^(succ (succ n)) = m * m^(succ n), from calc
      m^(succ (succ n)) = m^(succ n) * m   : by rw pow_succ'
                    ... = (m * m^n) * m    : by rw HI
                    ... = m * (m^n * m)    : by rw mul_assoc
                    ... = m * m^(succ n)   : by rw pow_succ')

-- 9ª demostración
example : m^(succ n) = m * (m^n) :=
nat.rec_on n
  (show m^(succ 0) = m * m^0,
    by rw [pow_succ', pow_zero, mul_one, one_mul])
  (assume n,
    assume HI : m^(succ n) = m * m^n,
    show m^(succ (succ n)) = m * m^(succ n),
      by rw [pow_succ', HI, mul_assoc, mul_comm (m^n)])

-- 10ª demostración
example : m^(succ n) = m * (m^n) :=
nat.rec_on n
  (show m^(succ 0) = m * m^0,
    by simp )
  (assume n,
    assume HI : m^(succ n) = m * m^n,
    show m^(succ (succ n)) = m * m^(succ n),
      by finish [pow_succ', HI] )

-- 11ª demostración
example : m^(succ n) = m * (m^n) :=
nat.rec_on n
  (by simp)
  (λ n HI, by finish [pow_succ', HI])

-- 12ª demostración
lemma aux : ∀ m n : ℕ, m^(succ n) = m * (m^n)
| m 0     := by simp
| m (n+1) := by simp [pow_succ',
                      aux m n,
                      mul_assoc,
                      mul_comm (m^n)]

-- 13ª demostración
lemma aux2 : ∀ m n : ℕ, m^(succ n) = m * (m^n)
| m 0     := by simp only [pow_succ',
                           pow_zero,
                           one_mul,
                           mul_one]
| m (n+1) := by simp only [pow_succ',
                           aux2 m n,
                           mul_assoc,
                           mul_comm (m^n)]

-- 14ª demostración
lemma aux3 : ∀ m n : ℕ, m^(succ n) = m * (m^n)
| m 0     := by simp
| m (n+1) := by simp [pow_succ', aux3 m n] ; cc
