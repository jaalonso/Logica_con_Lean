-- ----------------------------------------------------
-- Ejercicio. Demostrar o refutar
--    x = f x, triple (f x) (f x) x ⊢ triple x x x
-- ----------------------------------------------------

variable (U : Type)
variable (x : U)
variable (triple : U → U → U → Prop)
variable (f : U → U)

-- 1ª demostración
example
  (h1 : x = f x)
  (h2 : triple (f x) (f x) x)
  : triple x x x :=
begin
  rw ← h1 at h2,
  exact h2,
end

-- 2ª demostración
example
  (h1 : x = f x)
  (h2 : triple (f x) (f x) x)
  : triple x x x :=
begin
  rwa ← h1 at h2,
end

-- 3ª demostración
example
  (h1 : x = f x)
  (h2 : triple (f x) (f x) x)
  : triple x x x :=
by rwa ← h1 at h2
