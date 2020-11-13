-- Prueba por inducción 4: ∀ m n : ℕ, m + n = n + m
-- ================================================

-- ----------------------------------------------------
-- Ej. 1. Sean m y n números naturales. Demostrar que
--    m + n = n + m
-- ----------------------------------------------------

import tactic

open nat

variables (m n : ℕ)

-- 1ª demostración
example : m + n = n + m :=
begin
  induction n with n HI,
  { rw add_zero,
    rw nat.zero_add, },
  { rw add_succ,
    rw HI,
    rw succ_add, },
end

-- 2ª demostración
example : m + n = n + m :=
begin
  induction n with n HI,
  { simp only [add_zero, zero_add] },
  { simp only [add_succ, HI, succ_add] },
end

-- 3ª demostración
example : m + n = n + m :=
by induction n;
   simp only [*, add_zero, add_succ, succ_add, zero_add]

-- 4ª demostración
example : m + n = n + m :=
by induction n;
   simp [*, add_succ, succ_add]

-- 5ª demostración
example : m + n = n + m :=
nat.rec_on n
  (show m + 0 = 0 + m, from
    calc m + 0
             = m     : by rw add_zero
         ... = 0 + m : by rw nat.zero_add )
  (assume n,
   assume HI : m + n = n + m,
   calc
     m + succ n
         = succ (m + n) : by rw add_succ
     ... = succ (n + m) : by rw HI
     ... = succ n + m   : by rw succ_add)

-- 6ª demostración
example : m + n = n + m :=
nat.rec_on n
  (show m + 0 = 0 + m, by rw [nat.zero_add, add_zero])
  (assume n,
   assume HI : m + n = n + m,
   calc
     m + succ n = succ (m + n) : rfl
       ... = succ (n + m)      : by rw HI
       ... = succ n + m        : by rw succ_add)

-- 7ª demostración
example : m + n = n + m :=
nat.rec_on n
  (by simp only [nat.zero_add, add_zero])
  (λ n HI, by simp only [add_succ, HI, succ_add])

-- 8ª demostración
example : m + n = n + m :=
nat.rec_on n
  (by simp)
  (λ n HI, by simp [add_succ, HI, succ_add])

-- 9ª demostración
example : m + n = n + m :=
-- by library_search
add_comm m n

-- 10ª demostración
example : m + n = n + m :=
-- by hint
by finish

-- 11ª demostración
example : m + n = n + m :=
by linarith

-- 12ª demostración
example : m + n = n + m :=
by nlinarith

-- 13ª demostración
example : m + n = n + m :=
by ring

-- 14ª demostración
example : m + n = n + m :=
by omega

-- 15ª demostración
lemma conmutativa : ∀ m n : ℕ, m + n = n + m
| m 0     := by simp
| m (n+1) := by simp [add_succ, conmutativa m n, succ_add]

-- 16ª demostración
lemma conmutativa2 : ∀ m n : ℕ, m + n = n + m
| m 0     := by simp only [add_zero, zero_add]
| m (n+1) := by simp only [add_zero, add_succ, conmutativa2 m n, succ_add]
