-- Prueba por induccion 7: (∀ n ∈ ℕ) n ≠ 0 → succ (pred n) = n
-- ===========================================================

import data.nat.basic
open nat

variable (n : ℕ)

-- ?ª demostración
example : n ≠ 0 → succ (pred n) = n :=
begin
  cases n,
  { intro h,
    contradiction, },
  { intro h,
    rw pred_succ, },
end

-- ?ª demostración
example : n ≠ 0 → succ (pred n) = n :=
by cases n; simp

-- ?ª demostración
example : n ≠ 0 → succ (pred n) = n :=
nat.cases_on n
  (assume h : 0 ≠ 0,
    show succ (pred 0) = 0,
      from absurd rfl h)
  (assume n,
    assume h : succ n ≠ 0,
    show succ (pred (succ n)) = succ n,
      by rw pred_succ)

-- ?ª demostración
example : n ≠ 0 → succ (pred n) = n :=
nat.cases_on n
  (λ h, absurd rfl h)
  (λ n h, by rw pred_succ)
