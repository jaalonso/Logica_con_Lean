-- ----------------------------------------------------
-- Ejercicio. Demostrar
--    p → (q → (r → s)) ⊢ r → (q → (p → s))
-- ----------------------------------------------------

import tactic
variables (p q r s : Prop)

-- 1ª demostración
example
  (H : p → (q → (r → s)))
  : r → (q → (p → s)) :=
begin
  intros Hr Hq Hp,
  apply H,
  { exact Hp, },
  { exact Hq, },
  { exact Hr, },
end

-- 2ª demostración
example
  (H : p → (q → (r → s)))
  : r → (q → (p → s)) :=
begin
  intros Hr Hq Hp,
  exact H Hp Hq Hr,
end

-- 3ª demostración
example
  (H : p → (q → (r → s)))
  : r → (q → (p → s)) :=
λ Hr Hq Hp, H Hp Hq Hr

-- 4ª demostración
example
  (H : p → (q → (r → s)))
  : r → (q → (p → s)) :=
assume Hr : r,
assume Hq : q,
assume Hp : p,
have H1 : q → (r → s),
  from H Hp,
have H2 : r → s,
  from H1 Hq,
show s,
  from H2 Hr

-- 5ª demostración
example
  (H : p → (q → (r → s)))
  : r → (q → (p → s)) :=
assume Hr : r,
assume Hq : q,
assume Hp : p,
have H1 : q → (r → s),
  from H Hp,
have H2 : r → s,
  from H1 Hq,
H2 Hr

-- 6ª demostración
example
  (H : p → (q → (r → s)))
  : r → (q → (p → s)) :=
assume Hr : r,
assume Hq : q,
assume Hp : p,
have H1 : q → (r → s),
  from H Hp,
(H1 Hq) Hr

-- 7ª demostración
example
  (H : p → (q → (r → s)))
  : r → (q → (p → s)) :=
assume Hr : r,
assume Hq : q,
assume Hp : p,
((H Hp) Hq) Hr

-- 8ª demostración
example
  (H : p → (q → (r → s)))
  : r → (q → (p → s)) :=
λ Hr Hq Hp, ((H Hp) Hq) Hr

-- 9ª demostración
example
  (H : p → (q → (r → s)))
  : r → (q → (p → s)) :=
-- by hint
by finish
