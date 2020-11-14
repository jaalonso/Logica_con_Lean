-- Pruebas por inducción 1: 0 + n = n
-- ==================================

-- ----------------------------------------------------
-- Ej. 1. Sean m y n números naturales. Demostrar que
--    m + 0 = m
-- ----------------------------------------------------

import tactic

open nat

variables (m n : ℕ)

-- 1ª demostración
example : m + 0 = m :=
nat.add_zero m

-- 2ª demostración
example : m + 0 = m :=
rfl

-- ----------------------------------------------------
-- Ej. 2. Sean m y n números naturales. Demostrar que
--    m + (n + 1) = (m + n) + 1
-- ----------------------------------------------------

-- 1ª demostración
example : m + (n + 1) = (m + n) + 1 :=
add_succ m n

-- 2ª demostración
example : m + (n + 1) = (m + n) + 1 :=
rfl

-- ----------------------------------------------------
-- Ej. 3. Sean n un número natural. Demostrar que
--    0 + n = n
-- ----------------------------------------------------

-- 1ª demostración
example : 0 + n = n :=
begin
  induction n with n HI,
  { rw nat.add_zero, },
  { rw add_succ,
    rw HI, },
end

-- 2ª demostración
example : 0 + n = n :=
begin
  induction n with n HI,
  { rw nat.add_zero, },
  { rw [add_succ, HI], },
end

-- 3ª demostración
example : 0 + n = n :=
begin
  induction n with n HI,
  { simp, },
  { simp [add_succ, HI], },
end

-- 4ª demostración
example : 0 + n = n :=
begin
  induction n with n HI,
  { simp only [nat.add_zero], },
  { simp only [add_succ, HI], },
end

-- 5ª demostración
example : 0 + n = n :=
by induction n;
   simp only [*,
              nat.add_zero,
              add_succ]

-- 6ª demostración
example : 0 + n = n :=
by induction n;
   simp

-- 7ª demostración
example : 0 + n = n :=
nat.rec_on n
  ( show 0 + 0 = 0, from nat.add_zero 0)
  ( assume n,
    assume HI : 0 + n = n,
    show 0 + succ n = succ n, from
      calc
        0 + succ n = succ (0 + n) : by rw add_succ
               ... = succ n       : by rw HI)

-- 8ª demostración
example : 0 + n = n :=
nat.rec_on n
  ( show 0 + 0 = 0, from rfl)
  ( assume n,
    assume HI : 0 + n = n,
    show 0 + succ n = succ n, from
      calc
        0 + succ n = succ (0 + n) : rfl
               ... = succ n       : by rw HI)

-- 9ª demostración
example : 0 + n = n :=
nat.rec_on n rfl (λ n HI, by rw [add_succ, HI])

-- 10ª demostración
example : 0 + n = n :=
nat.rec_on n rfl (λ n HI, by simp only [add_succ, HI])

-- 11ª demostración
example : 0 + n = n :=
-- by library_search
zero_add n

-- 12ª demostración
example : 0 + n = n :=
-- by hint
by simp

-- 13ª demostración
example : 0 + n = n :=
by finish

-- 14ª demostración
example : 0 + n = n :=
by linarith

-- 15ª demostración
example : 0 + n = n :=
by nlinarith

-- 16ª demostración
example : 0 + n = n :=
by norm_num

-- 17ª demostración
example : 0 + n = n :=
by ring

-- 18ª demostración
example : 0 + n = n :=
by omega

-- 19ª demostración
example : 0 + n = n :=
by tidy

-- 20ª demostración
example : 0 + n = n :=
-- by tidy ?
by simp at *

-- 21ª demostración
lemma cero_mas : ∀ n : ℕ, 0 + n = n
| 0     := rfl
| (n+1) := congr_arg succ (cero_mas n)

-- 22ª demostración
lemma cero_mas2 : ∀ n : ℕ, 0 + n = n
| 0     := by simp
| (n+1) := by simp

-- 23ª demostración
lemma cero_mas3 : ∀ n : ℕ, 0 + n = n
| 0     := by simp only [add_zero]
| (n+1) := by simp only [add_zero, add_succ, cero_mas3 n]

-- 24ª demostración
lemma cero_mas4 : ∀ n : ℕ, 0 + n = n
| 0     := by rw [add_zero]
| (n+1) := by rw [add_succ, cero_mas4 n]
