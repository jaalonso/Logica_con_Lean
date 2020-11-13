-- Prueba por inducción 3: ∀ m n : ℕ, succ m + n = succ (m + n)
-- ============================================================

-- ----------------------------------------------------
-- Ej. 1. Sean m y n números naturales. Demostrar que
--    succ m + n = succ (m + n)
-- ----------------------------------------------------

import tactic

open nat

variables (m n : ℕ)

-- 1ª demostración
example : succ m + n = succ (m + n) :=
begin
  induction n with n HI,
  { rw nat.add_zero,
    rw nat.add_zero, },
  { rw add_succ,
    rw HI, },
end

-- 2ª demostración
example : succ m + n = succ (m + n) :=
begin
  induction n with n HI,
  { simp only [add_zero] },
  { simp only [add_succ, HI] },
end

-- 3ª demostración
example : succ m + n = succ (m + n) :=
by induction n; simp only [*, add_zero, add_succ]

-- 4ª demostración
example : succ m + n = succ (m + n) :=
by induction n; simp [*, add_succ]

-- 5ª demostración
example : succ m + n = succ (m + n) :=
nat.rec_on n
  (show succ m + 0 = succ (m + 0), from
    calc
      succ m + 0
          = succ m       : by rw nat.add_zero
      ... = succ (m + 0) : by rw nat.add_zero)
  (assume n,
    assume HI : succ m + n = succ (m + n),
    show succ m + succ n = succ (m + succ n), from
      calc
        succ m + succ n
            = succ (succ m + n)   : by rw add_succ
        ... = succ (succ (m + n)) : by rw HI
        ... = succ (m + succ n)   : by rw add_succ)

-- 6ª demostración
example : succ m + n = succ (m + n) :=
nat.rec_on n
  (show succ m + 0 = succ (m + 0), from rfl)
  (assume n,
    assume HI : succ m + n = succ (m + n),
    show succ m + succ n = succ (m + succ n), from
      calc
        succ m + succ n
            = succ (succ m + n)   : rfl
        ... = succ (succ (m + n)) : by rw HI
        ... = succ (m + succ n)   : rfl)

-- 7ª demostración
example : succ m + n = succ (m + n) :=
nat.rec_on n rfl (λ n HI, by simp only [add_succ, HI])

-- 8ª demostración
example : succ m + n = succ (m + n) :=
-- by library_search
succ_add m n

-- 9ª demostración
example : succ m + n = succ (m + n) :=
-- by hint
by omega

-- 10ª demostración
lemma suc_suma : ∀ n m : ℕ, (succ n) + m = succ (n + m)
| n 0     := rfl
| n (m+1) := congr_arg succ (suc_suma n m)

-- 11ª demostración
lemma suc_suma2 : ∀ n m : ℕ, (succ n) + m = succ (n + m)
| n 0     := by simp
| n (m+1) := by simp [add_succ, suc_suma2 n m]

-- 12ª demostración
lemma suc_suma3 : ∀ n m : ℕ, (succ n) + m = succ (n + m)
| n 0     := by simp only [add_zero]
| n (m+1) := by simp only [add_zero, add_succ, suc_suma3 n m]
