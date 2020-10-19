-- Pruebas de y = x → y = z → x = z
-- ================================

-- ----------------------------------------------------
-- Ej. 1. Demostrar
--    y = x → y = z → x = z
-- ----------------------------------------------------

import tactic

variables (U : Type) 
variables (x y z : U)

-- 1ª demostración
example : y = x → y = z → x = z :=
assume h1 : y = x,
assume h2 : y = z,
have h3 : x = y, from eq.symm h1,
show x = z,      from eq.trans h3 h2

-- 2ª demostración
example : y = x → y = z → x = z :=
assume h1 : y = x,
assume h2 : y = z,
have h3 : x = y, from eq.symm h1,
eq.trans h3 h2

-- 3ª demostración
example : y = x → y = z → x = z :=
assume h1 : y = x,
assume h2 : y = z,
eq.trans (eq.symm h1) h2

-- 4ª demostración
example : y = x → y = z → x = z :=
λ h1 h2, eq.trans (eq.symm h1) h2

-- 5ª demostración
example : y = x → y = z → x = z :=
λ h1 h2, eq.trans h1.symm h2

-- 6ª demostración
example : y = x → y = z → x = z :=
-- by library_search
λ h, h.congr_left.mp

-- 7ª demostración
example : y = x → y = z → x = z :=
begin
  intros h1 h2,
  rwa ←h1,
end

-- 8ª demostración
example : y = x → y = z → x = z :=
begin
  intros h1 h2,
  rw h1 at h2,
  assumption,
end

-- 9ª demostración
example : y = x → y = z → x = z :=
begin
  intros h1 h2,
  rwa h1 at h2,
end

-- 10ª demostración
example : y = x → y = z → x = z :=
begin
  intros h1 h2,
  calc x = y : h1.symm
     ... = z : h2,
end

-- 11ª demostración
example : y = x → y = z → x = z :=
-- by hint
by finish

-- 12ª demostración
example : y = x → y = z → x = z :=
assume h1 : y = x,
assume h2 : y = z,
show x = z,
  begin
    rw ←h1,
    rw h2
  end

-- 13ª demostración
example : y = x → y = z → x = z :=
assume h1 : y = x,
assume h2 : y = z,
show x = z,
  begin
    rw [←h1, h2]
  end

-- 14ª demostración
example : y = x → y = z → x = z :=
assume h1 : y = x,
assume h2 : y = z,
show x = z, by rw [←h1, h2]
