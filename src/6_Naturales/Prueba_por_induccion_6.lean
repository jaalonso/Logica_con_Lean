-- Prueba por inducción 6: (∀ m n k ∈ ℕ) m^(n + k) = m^n * m^k
-- ===========================================================

import data.nat.basic
import tactic
open nat

variables  (m n k : ℕ)

-- 1ª demostración
example : m^(n + k) = m^n * m^k :=
begin
  induction k with k HI,
  { rw add_zero,
    rw nat.pow_zero,
    rw mul_one, },
  { rw add_succ,
    rw nat.pow_succ,
    rw HI,
    rw nat.pow_succ,
    rw mul_assoc, },
end

-- 2ª demostración
example : m^(n + k) = m^n * m^k :=
begin
  induction k with k HI,
  { calc
      m^(n + 0)
          = m^n       : by rw add_zero
      ... = m^n * 1   : by rw mul_one
      ... = m^n * m^0 : by rw nat.pow_zero, },
  { calc
      m^(n + succ k)
          = m^(succ (n + k)) : by rw nat.add_succ
      ... = m^(n + k) * m    : by rw nat.pow_succ
      ... = m^n * m^k * m    : by rw HI
      ... = m^n * (m^k * m)  : by rw mul_assoc
      ... = m^n * m^(succ k) : by rw nat.pow_succ, },
end

-- 3ª demostración
example : m^(n + k) = m^n * m^k :=
begin
  induction k with k HI,
  { rw [add_zero,
        nat.pow_zero,
        mul_one], },
  { rw [add_succ,
        nat.pow_succ,
        HI,
        nat.pow_succ,
        mul_assoc], },
end

-- 4ª demostración
example : m^(n + k) = m^n * m^k :=
begin
  induction k with k HI,
  { simp only [add_zero,
               nat.pow_zero,
               mul_one], },
  { simp only [add_succ,
               nat.pow_succ,
               HI,
               nat.pow_succ,
               mul_assoc], },
end

-- 5ª demostración
example : m^(n + k) = m^n * m^k :=
begin
  induction k with k HI,
  { simp, },
  { simp [HI,
          nat.pow_succ,
          mul_assoc], },
end

-- 6ª demostración
example : m^(n + k) = m^n * m^k :=
by induction k; simp [*, nat.pow_succ, mul_assoc]

-- 7ª demostración
example : m^(n + k) = m^n * m^k :=
nat.rec_on k
  (show m^(n + 0) = m^n * m^0, from
    calc
      m^(n + 0)
          = m^n       : by rw add_zero
      ... = m^n * 1   : by rw mul_one
      ... = m^n * m^0 : by rw nat.pow_zero)
  (assume k,
    assume HI : m^(n + k) = m^n * m^k,
    show m^(n + succ k) = m^n * m^(succ k), from
      calc
        m^(n + succ k)
            = m^(succ (n + k)) : by rw nat.add_succ
        ... = m^(n + k) * m    : by rw nat.pow_succ
        ... = m^n * m^k * m    : by rw HI
        ... = m^n * (m^k * m)  : by rw mul_assoc
        ... = m^n * m^(succ k) : by rw nat.pow_succ)

-- 8ª demostración
example : m^(n + k) = m^n * m^k :=
nat.rec_on k
  (by simp)
  (λ n HI, by simp [HI, nat.pow_succ, mul_assoc])

-- 9ª demostración
example : m^(n + k) = m^n * m^k :=
-- by library_search
pow_add m n k
