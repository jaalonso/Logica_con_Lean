-- Prueba por inducción 2: ∀ m n k : ℕ, (m + n) + k = m + (n + k)
-- ==============================================================

-- ----------------------------------------------------
-- Ej. 1. Sean m, n y k números naturales. Demostrar que
--    (m + n) + k = m + (n + k)
-- ----------------------------------------------------

import tactic

open nat

variables (m n k : ℕ)

-- 1ª demostración
example : (m + n) + k = m + (n + k) :=
begin
  induction k with k' HI,
  { rw nat.add_zero,
    rw nat.add_zero, },
  { rw add_succ,
    rw HI,
    rw add_succ, },
end

-- 2ª demostración
example : (m + n) + k = m + (n + k) :=
begin
  induction k with k' HI,
  { rw [nat.add_zero, nat.add_zero], },
  { rw [add_succ, HI, add_succ], },
end

-- 3ª demostración
example : (m + n) + k = m + (n + k) :=
begin
  induction k with k HI,
  { simp, },
  { simp [add_succ, HI], },
end

-- 4ª demostración
example : (m + n) + k = m + (n + k) :=
begin
  induction k with k HI,
  { simp only [add_zero], },
  { simp only [add_succ, HI], },
end

-- 5ª demostración
example : (m + n) + k = m + (n + k) :=
by induction k;
   simp only [*, add_zero, add_succ]

-- 6ª demostración
example : (m + n) + k = m + (n + k) :=
by induction k;
   simp [*, add_succ]

-- 7ª demostración
example : (m + n) + k = m + (n + k) :=
begin
  induction k with k HI,
  { calc
      (m + n) + 0
          = m + n       : by rw nat.add_zero
      ... = m + (n + 0) : by rw nat.add_zero, },
  { calc
      (m + n) + succ k
          = succ ((m + n) + k) : by rw add_succ
      ... = succ (m + (n + k)) : by rw HI
      ... = m + succ (n + k)   : by rw add_succ
      ... = m + (n + succ k)   : by rw add_succ, },
end

-- 8ª demostración
example : (m + n) + k = m + (n + k) :=
begin
  induction k with k HI,
  { calc
      (m + n) + 0 = m + (n + 0) : rfl, },
  { calc
      (m + n) + succ k
          = succ ((m + n) + k) : rfl
      ... = succ (m + (n + k)) : by rw HI
      ... = m + succ (n + k)   : rfl
      ... = m + (n + succ k)   : rfl, },
end

-- 9ª demostración
example : (m + n) + k = m + (n + k) :=
nat.rec_on k
  ( show (m + n) + 0 = m + (n + 0), from rfl )
  ( assume k,
    assume HI : (m + n) + k = m + (n + k),
    show (m + n) + succ k = m + (n + succ k), from
      calc
        (m + n) + succ k
            = succ ((m + n) + k) : rfl
        ... = succ (m + (n + k)) : by rw HI
        ... = m + succ (n + k)   : rfl
        ... = m + (n + succ k)   : rfl )

-- 10ª demostración
example : (m + n) + k = m + (n + k) :=
nat.rec_on k rfl (λ k HI, by simp only [add_succ, HI])

-- 11ª demostración
example : (m + n) + k = m + (n + k) :=
-- by library_search
add_assoc m n k

-- 12ª demostración
example : (m + n) + k = m + (n + k) :=
-- by hint
by finish

-- 13ª demostración
example : (m + n) + k = m + (n + k) :=
by linarith

-- 14ª demostración
example : (m + n) + k = m + (n + k) :=
by nlinarith

-- 15ª demostración
example : (m + n) + k = m + (n + k) :=
by omega

-- 16ª demostración
example : (m + n) + k = m + (n + k) :=
by ring

-- 17ª demostración
lemma asociativa_suma :
  ∀ k : ℕ, (m + n) + k = m + (n + k)
| 0       := rfl
| (k + 1) := congr_arg succ (asociativa_suma k)

-- 18ª demostración
lemma asociativa_suma2 :
  ∀ k : ℕ, (m + n) + k = m + (n + k)
| 0       := by simp
| (k + 1) := by simp [add_succ, asociativa_suma2 k]

-- 19ª demostración
lemma asociativa_suma3 :
  ∀ k : ℕ, (m + n) + k = m + (n + k)
| 0       := by simp only [nat.add_zero]
| (k + 1) := by simp only [nat.add_zero, add_succ, asociativa_suma3 k]
