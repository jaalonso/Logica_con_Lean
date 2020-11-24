-- Ejercicios de lógica proposicional
-- ==================================

import tactic
variables (p q r s : Prop)

-- § Implicaciones
-- ================

-- ----------------------------------------------------
-- Ejercicio 1. Demostrar
--      p ⟶ q, p ⊢ q
-- ----------------------------------------------------

-- 1ª demostración
example
  (Hpq : p → q)
  (Hp  : p)
  : q :=
Hpq Hp

-- 2ª demostración
example
  (Hpq : p → q)
  (Hp  : p)
  : q :=
by tauto

-- ----------------------------------------------------
-- Ejercicio 2. Demostrar
--    p → q, q → r, p ⊢ r
-- ----------------------------------------------------

-- 1ª demostracióm
example
  (Hpq : p → q)
  (Hqr : q → r)
  (Hp : p)
  : r :=
begin
  apply Hqr,
  apply Hpq,
  exact Hp,
end

-- 2ª demostracióm
example
  (Hpq : p → q)
  (Hqr : q → r)
  (Hp : p)
  : r :=
begin
  apply Hqr,
  exact Hpq Hp,
end

-- 3ª demostracióm
example
  (Hpq : p → q)
  (Hqr : q → r)
  (Hp : p)
  : r :=
begin
  exact Hqr (Hpq Hp),
end

-- 3ª demostracióm
example
  (Hpq : p → q)
  (Hqr : q → r)
  (Hp : p)
  : r :=
Hqr (Hpq Hp)

-- 4ª demostracióm
example
  (Hpq : p → q)
  (Hqr : q → r)
  (Hp : p)
  : r :=
by tauto

-- 5ª demostracióm
example
  (Hpq : p → q)
  (Hqr : q → r)
  (Hp : p)
  : r :=
have Hq : q,
  from Hpq Hp,
show r,
  from Hqr Hq

-- ----------------------------------------------------
-- Ejercicio 3. Demostrar
--    p → (q → r), p → q, p ⊢ r
-- ----------------------------------------------------

-- 1ª demostración
example
  (Hpqr : p → (q → r))
  (Hpq  : p → q)
  (Hp   : p)
  : r :=
begin
  have Hqr : q → r, from Hpqr Hp,
  apply Hqr,
  apply Hpq,
  exact Hp,
end

-- 2ª demostración
example
  (Hpqr : p → (q → r))
  (Hpq  : p → q)
  (Hp   : p)
  : r :=
begin
  have Hqr : q → r, from Hpqr Hp,
  apply Hqr,
  exact Hpq Hp,
end

-- 3ª demostración
example
  (Hpqr : p → (q → r))
  (Hpq  : p → q)
  (Hp   : p)
  : r :=
begin
  have Hqr : q → r, from Hpqr Hp,
  exact Hqr (Hpq Hp),
end

-- 4ª demostración
example
  (Hpqr : p → (q → r))
  (Hpq  : p → q)
  (Hp   : p)
  : r :=
(Hpqr Hp) (Hpq Hp)

-- 5ª demostración
example
  (Hpqr : p → (q → r))
  (Hpq  : p → q)
  (Hp   : p)
  : r :=
-- by hint
by finish

-- ----------------------------------------------------
-- Ejercicio 4. Demostrar
--    p → q, q → r ⊢ p → r
-- ----------------------------------------------------

-- 1ª demostración
example
  (Hpq : p → q)
  (Hqr : q → r)
  : p → r :=
begin
  intro Hp,
  apply Hqr,
  apply Hpq,
  exact Hp,
end

-- 2ª demostración
example
  (Hpq : p → q)
  (Hqr : q → r)
  : p → r :=
begin
  intro Hp,
  apply Hqr,
  exact Hpq Hp,
end

-- 3ª demostración
example
  (Hpq : p → q)
  (Hqr : q → r)
  : p → r :=
begin
  intro Hp,
  exact Hqr (Hpq Hp),
end

-- 4ª demostración
example
  (Hpq : p → q)
  (Hqr : q → r)
  : p → r :=
λ Hp, Hqr (Hpq Hp)

-- 5ª demostración
example
  (Hpq : p → q)
  (Hqr : q → r)
  : p → r :=
assume Hp : p,
have Hq : q,
  from Hpq Hp,
show r,
  from Hqr Hq

-- 6ª demostración
example
  (Hpq : p → q)
  (Hqr : q → r)
  : p → r :=
assume Hp : p,
have Hq : q,
  from Hpq Hp,
Hqr Hq

-- 7ª demostración
example
  (Hpq : p → q)
  (Hqr : q → r)
  : p → r :=
assume Hp : p,
Hqr (Hpq Hp)

-- 8ª demostración
example
  (Hpq : p → q)
  (Hqr : q → r)
  : p → r :=
λ Hp, Hqr (Hpq Hp)

-- 9ª demostración
example
  (Hpq : p → q)
  (Hqr : q → r)
  : p → r :=
-- by hint
by tauto

-- 10ª demostración
example
  (Hpq : p → q)
  (Hqr : q → r)
  : p → r :=
by finish

-- ----------------------------------------------------
-- Ejercicio 5. Demostrar
--    p → (q → r) ⊢ q → (p → r)
-- ----------------------------------------------------

-- 1ª demostración
example
  (Hpqr : p → (q → r))
  : q → (p → r) :=
begin
  intro Hq,
  intro Hp,
  have Hqr : q → r,
    from Hpqr Hp,
  apply Hqr,
  exact Hq,
end

-- 2ª demostración
example
  (Hpqr : p → (q → r))
  : q → (p → r) :=
begin
  intro Hq,
  intro Hp,
  have Hqr : q → r,
    from Hpqr Hp,
  exact Hqr Hq,
end

-- 3ª demostración
example
  (Hpqr : p → (q → r))
  : q → (p → r) :=
begin
  intro Hq,
  intro Hp,
  exact (Hpqr Hp) Hq,
end

-- 4ª demostración
example
  (Hpqr : p → (q → r))
  : q → (p → r) :=
begin
  intros Hq Hp,
  exact (Hpqr Hp) Hq,
end

-- 5ª demostración
example
  (Hpqr : p → (q → r))
  : q → (p → r) :=
λ Hq Hp, (Hpqr Hp) Hq

-- 6ª demostración
example
  (Hpqr : p → (q → r))
  : q → (p → r) :=
begin
  intros Hq Hp,
  apply Hpqr,
  { exact Hp, },
  { exact Hq, },
end

-- 7ª demostración
example
  (Hpqr : p → (q → r))
  : q → (p → r) :=
assume Hq : q,
assume Hp : p,
have Hqr : q → r,
  from Hpqr Hp,
show r,
  from Hqr Hq

-- 8ª demostración
example
  (Hpqr : p → (q → r))
  : q → (p → r) :=
assume Hq : q,
assume Hp : p,
have Hqr : q → r,
  from Hpqr Hp,
Hqr Hq

-- 9ª demostración
example
  (Hpqr : p → (q → r))
  : q → (p → r) :=
assume Hq : q,
assume Hp : p,
(Hpqr Hp) Hq

-- 10ª demostración
example
  (Hpqr : p → (q → r))
  : q → (p → r) :=
λ Hq Hp, (Hpqr Hp) Hq

-- 11ª demostración
example
  (Hpqr : p → (q → r))
  : q → (p → r) :=
-- by hint
by tauto

-- 12ª demostración
example
  (Hpqr : p → (q → r))
  : q → (p → r) :=
by finish

-- ----------------------------------------------------
-- Ejercicio 6. Demostrar
--    p → (q → r) ⊢ (p → q) → (p → r)
-- ----------------------------------------------------

-- 1ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
begin
  intros Hpq Hp,
  have Hqr : q → r,
    from Hpqr Hp,
  apply Hqr,
  apply Hpq,
  exact Hp,
end

-- 2ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
begin
  intros Hpq Hp,
  have Hqr : q → r,
    from Hpqr Hp,
  apply Hqr,
  exact Hpq Hp,
end

-- 3ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
begin
  intros Hpq Hp,
  have Hqr : q → r,
    from Hpqr Hp,
  exact Hqr (Hpq Hp),
end

-- 4ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
begin
  intros Hpq Hp,
  exact (Hpqr Hp) (Hpq Hp),
end

-- 5ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
λ Hpq Hp, (Hpqr Hp) (Hpq Hp)

-- 6ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
assume Hpq : p → q,
assume Hp : p,
have Hqr : q → r,
  from Hpqr Hp,
have Hq : q,
  from Hpq Hp,
show r,
  from Hqr Hq

-- 7ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
assume Hpq : p → q,
assume Hp : p,
have Hqr : q → r,
  from Hpqr Hp,
have Hq : q,
  from Hpq Hp,
Hqr Hq

-- 8ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
assume Hpq : p → q,
assume Hp : p,
have Hqr : q → r,
  from Hpqr Hp,
Hqr (Hpq Hp)

-- 9ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
assume Hpq : p → q,
assume Hp : p,
(Hpqr Hp) (Hpq Hp)

-- 10ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
λ Hpq Hp, (Hpqr Hp) (Hpq Hp)

-- 11ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
-- by hint
by finish

-- ----------------------------------------------------
-- Ejercicio 7. Demostrar
--    p ⊢ q → p
-- ----------------------------------------------------

-- 1ª demostración
example
  (Hp : p)
  : q → p :=
begin
  intro Hq,
  exact Hp,
end

-- 2ª demostración
example
  (H : p)
  : q → p :=
λ _, H

-- 3ª demostración
example
  (Hp : p)
  : q → p :=
assume Hq : q,
show p,
  from Hp

-- 4ª demostración
example
  (Hp : p)
  : q → p :=
-- by library_search
imp_intro Hp

-- 5ª demostración
example
  (Hp : p)
  : q → p :=
-- by hint
by tauto

-- 6ª demostración
example
  (Hp : p)
  : q → p :=
by finish

-- ----------------------------------------------------
-- Ejercicio 8. Demostrar
--    ⊢ p → (q → p)
-- ----------------------------------------------------

-- 1ª demostración
example :
  p → (q → p) :=
begin
  intros Hp Hq,
  exact Hp,
end

-- 2ª demostración
example :
  p → (q → p) :=
λ Hp _, Hp

-- 3ª demostración
example :
  p → (q → p) :=
assume Hp : p,
assume Hq : q,
show p,
  from Hp

-- 4ª demostración
example :
  p → (q → p) :=
-- by library_search
imp_intro

-- 5ª demostración
example :
  p → (q → p) :=
-- by hint
by tauto

-- 6ª demostración
example :
  p → (q → p) :=
by finish

-- ----------------------------------------------------
-- Ejercicio 9. Demostrar
--    p → q ⊢ (q → r) → (p → r)
-- ----------------------------------------------------

-- 1ª demostración
example
  (Hpq : p → q)
  : (q → r) → (p → r) :=
begin
  intros Hqr Hp,
  apply Hqr,
  apply Hpq,
  exact Hp,
end

-- 2ª demostración
example
  (Hpq : p → q)
  : (q → r) → (p → r) :=
begin
  intros Hqr Hp,
  apply Hqr,
  exact Hpq Hp,
end

-- 3ª demostración
example
  (Hpq : p → q)
  : (q → r) → (p → r) :=
begin
  intros Hqr Hp,
  exact Hqr (Hpq Hp),
end

-- 4ª demostración
example
  (Hpq : p → q)
  : (q → r) → (p → r) :=
λ Hqr Hp, Hqr (Hpq Hp)

-- 5ª demostración
example
  (Hpq : p → q)
  : (q → r) → (p → r) :=
assume Hqr : q → r,
assume Hp : p,
have Hq : q,
  from Hpq Hp,
show r,
  from Hqr Hq

-- 6ª demostración
example
  (Hpq : p → q)
  : (q → r) → (p → r) :=
assume Hqr : q → r,
assume Hp : p,
have Hq : q,
  from Hpq Hp,
Hqr Hq

-- 7ª demostración
example
  (Hpq : p → q)
  : (q → r) → (p → r) :=
λ Hqr Hp, Hqr (Hpq Hp)

-- 8ª demostración
example
  (Hpq : p → q)
  : (q → r) → (p → r) :=
-- by hint
by tauto

-- 9ª demostración
example
  (Hpq : p → q)
  : (q → r) → (p → r) :=
by finish

-- ----------------------------------------------------
-- Ejercicio 10. Demostrar
--    p → (q → (r → s)) ⊢ r → (q → (p → s))
-- ----------------------------------------------------

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

-- ----------------------------------------------------
-- Ejercicio 11. Demostrar
--    ⊢ (p → (q → r)) → ((p → q) → (p → r))
-- ----------------------------------------------------

-- 1ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
begin
  intros Hpq Hp,
  apply Hpqr,
  { exact Hp, },
  { apply Hpq,
    exact Hp, },
end

-- 2ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
begin
  intros Hpq Hp,
  apply Hpqr,
  { exact Hp, },
  { exact Hpq Hp, },
end

-- 3ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
begin
  intros Hpq Hp,
  exact Hpqr Hp (Hpq Hp),
end

-- 4ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
λ Hpq Hp, Hpqr Hp (Hpq Hp)

-- 5ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
assume Hpq : p → q,
assume Hp : p,
have Hq : q,
  from Hpq Hp,
have Hqr : q → r,
  from Hpqr Hp,
show r,
  from Hqr Hq

-- 6ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
assume Hpq : p → q,
assume Hp : p,
have Hq : q,
  from Hpq Hp,
have Hqr : q → r,
  from Hpqr Hp,
Hqr Hq

-- 7ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
assume Hpq : p → q,
assume Hp : p,
have Hq : q,
  from Hpq Hp,
(Hpqr Hp) Hq

-- 8ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
assume Hpq : p → q,
assume Hp : p,
(Hpqr Hp) (Hpq Hp)

-- 9ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
λ Hpq Hp, (Hpqr Hp) (Hpq Hp)

-- 10ª demostración
example
  (Hpqr : p → (q → r))
  : (p → q) → (p → r) :=
-- by hint
by finish

-- ----------------------------------------------------
-- Ejercicio 12. Demostrar
--    (p → q) → r ⊢ p → (q → r)
-- ----------------------------------------------------

-- 1ª demostración
example
  (Hpqr : (p → q) → r)
  : p → (q → r) :=
begin
  intros Hp Hq,
  apply Hpqr,
  intro Hp,
  exact Hq,
end

-- 2ª demostración
example
  (Hpqr : (p → q) → r)
  : p → (q → r) :=
begin
  intros Hp Hq,
  apply Hpqr,
  exact (λ Hp, Hq),
end

-- 3ª demostración
example
  (Hpqr : (p → q) → r)
  : p → (q → r) :=
begin
  intros Hp Hq,
  exact Hpqr (λ Hp, Hq),
end

-- 4ª demostración
example
  (Hpqr : (p → q) → r)
  : p → (q → r) :=
λ Hp Hq, Hpqr (λ Hp, Hq)

-- 5ª demostración
example
  (Hpqr : (p → q) → r)
  : p → (q → r) :=
assume Hp : p,
assume Hq : q,
have Hpq : p → q,
  { assume p,
    show q,
      from Hq },
show r,
  from Hpqr Hpq

-- 6ª demostración
example
  (Hpqr : (p → q) → r)
  : p → (q → r) :=
assume Hp : p,
assume Hq : q,
have Hpq : p → q,
  { assume p,
    show q,
      from Hq },
Hpqr Hpq

-- 7ª demostración
example
  (Hpqr : (p → q) → r)
  : p → (q → r) :=
assume Hp : p,
assume Hq : q,
have Hpq : p → q,
  from (λ p, Hq),
Hpqr Hpq

-- 8ª demostración
example
  (Hpqr : (p → q) → r)
  : p → (q → r) :=
assume Hp : p,
assume Hq : q,
Hpqr (λ p, Hq)

-- 9ª demostración
example
  (Hpqr : (p → q) → r)
  : p → (q → r) :=
λ Hp Hq, Hpqr (λ p, Hq)

-- 10ª demostración
example
  (Hpqr : (p → q) → r)
  : p → (q → r) :=
-- by hint
by finish

-- § Conjunciones
-- ==============

-- ----------------------------------------------------
-- Ejercicio 13. Demostrar
--    p, q ⊢  p ∧ q
-- ----------------------------------------------------

-- 1ª demostración
example
  (Hp : p)
  (Hq : q)
  : p ∧ q :=
begin
  split,
  { exact Hp, },
  { exact Hq, },
end

-- 2ª demostración
example
  (Hp : p)
  (Hq : q)
  : p ∧ q :=
and.intro Hp Hq

-- 3ª demostración
example
  (Hp : p)
  (Hq : q)
  : p ∧ q :=
-- by library_search
⟨Hp, Hq⟩

-- 4ª demostración
example
  (Hp : p)
  (Hq : q)
  : p ∧ q :=
-- by hint
by tauto

-- 5ª demostración
example
  (Hp : p)
  (Hq : q)
  : p ∧ q :=
by finish

-- ----------------------------------------------------
-- Ejercicio 14. Demostrar
--    p ∧ q ⊢ p
-- ----------------------------------------------------

-- 1ª demostración
example
  (H : p ∧ q)
  : p :=
begin
  cases H with Hp Hq,
  exact Hp,
end

-- 2ª demostración
example
  (H : p ∧ q)
  : p :=
and.elim_left H

-- 3ª demostración
example
  (H : p ∧ q)
  : p :=
and.left H

-- 4ª demostración
example
  (H : p ∧ q)
  : p :=
H.left

-- 5ª demostración
example
  (H : p ∧ q)
  : p :=
H.1

-- 6ª demostración
example
  (H : p ∧ q)
  : p :=
-- by library_search
H.left

-- 7ª demostración
example
  (H : p ∧ q)
  : p :=
-- by hint
by tauto

-- 8ª demostración
example
  (H : p ∧ q)
  : p :=
by finish

-- ----------------------------------------------------
-- Ejercicio 15. Demostrar
--    p ∧ q ⊢ q
-- ----------------------------------------------------

-- 1ª demostración
example
  (H : p ∧ q)
  : q :=
begin
  cases H with Hp Hq,
  exact Hq,
end

-- 2ª demostración
example
  (H : p ∧ q)
  : q :=
and.elim_right H

-- 3ª demostración
example
  (H : p ∧ q)
  : q :=
and.right H

-- 4ª demostración
example
  (H : p ∧ q)
  : q :=
H.right

-- 5ª demostración
example
  (H : p ∧ q)
  : q :=
H.2

-- 6ª demostración
example
  (H : p ∧ q)
  : q :=
-- by library_search
H.right

-- 7ª demostración
example
  (H : p ∧ q)
  : q :=
-- by hint
by tauto

-- 8ª demostración
example
  (H : p ∧ q)
  : q :=
by finish

-- ----------------------------------------------------
-- Ejercicio 16. Demostrar
--    p ∧ (q ∧ r) ⊢ (p ∧ q) ∧ r
-- ----------------------------------------------------

-- 1ª demostración
example
  (Hpqr : p ∧ (q ∧ r))
  : (p ∧ q) ∧ r :=
begin
  cases Hpqr with Hp Hqr,
  cases Hqr with Hq Hr,
  split,
  { split,
    { exact Hp, },
    { exact Hq, }},
  { exact Hr, },
end

-- 2ª demostración
example
  (Hpqr : p ∧ (q ∧ r))
  : (p ∧ q) ∧ r :=
begin
  cases Hpqr with Hp Hqr,
  cases Hqr with Hq Hr,
  split,
  { exact ⟨Hp, Hq⟩, },
  { exact Hr, },
end

-- 3ª demostración
example
  (Hpqr : p ∧ (q ∧ r))
  : (p ∧ q) ∧ r :=
begin
  cases Hpqr with Hp Hqr,
  cases Hqr with Hq Hr,
  exact ⟨⟨Hp, Hq⟩, Hr⟩,
end

-- 4ª demostración
example
  (Hpqr : p ∧ (q ∧ r))
  : (p ∧ q) ∧ r :=
begin
  rcases Hpqr with ⟨Hp, ⟨Hq, Hr⟩⟩,
  exact ⟨⟨Hp, Hq⟩, Hr⟩,
end

-- 5ª demostración
example :
  p ∧ (q ∧ r) → (p ∧ q) ∧ r :=
begin
  rintros ⟨Hp, ⟨Hq, Hr⟩⟩,
  exact ⟨⟨Hp, Hq⟩, Hr⟩,
end

-- 6ª demostración
example :
  p ∧ (q ∧ r) → (p ∧ q) ∧ r :=
λ ⟨Hp, ⟨Hq, Hr⟩⟩, ⟨⟨Hp, Hq⟩, Hr⟩

-- 7ª demostración
example
  (Hpqr : p ∧ (q ∧ r))
  : (p ∧ q) ∧ r :=
have Hp : p,
  from and.left Hpqr,
have Hqr : q ∧ r,
  from and.right Hpqr,
have Hq : q,
  from and.left Hqr,
have Hr : r,
  from and.right Hqr,
have Hpq : p ∧ q,
  from and.intro Hp Hq,
show (p ∧ q) ∧ r,
  from and.intro Hpq Hr

-- 8ª demostración
example
  (Hpqr : p ∧ (q ∧ r))
  : (p ∧ q) ∧ r :=
-- by library_search
(and_assoc p q).mpr Hpqr

-- 9ª demostración
example
  (Hpqr : p ∧ (q ∧ r))
  : (p ∧ q) ∧ r :=
-- by hint
by tauto

-- 10ª demostración
example
  (Hpqr : p ∧ (q ∧ r))
  : (p ∧ q) ∧ r :=
by finish

-- ----------------------------------------------------
-- Ejercicio 17. Demostrar
--    (p ∧ q) ∧ r ⊢ p ∧ (q ∧ r)
-- ----------------------------------------------------

-- 1ª demostración
example
  (Hpqr : (p ∧ q) ∧ r)
  : p ∧ (q ∧ r) :=
begin
  rcases Hpqr with ⟨⟨Hp, Hq⟩, Hr⟩,
  exact ⟨Hp, ⟨Hq, Hr⟩⟩,
end

-- 2ª demostración
example
  : (p ∧ q) ∧ r → p ∧ (q ∧ r) :=
begin
  rintros ⟨⟨Hp, Hq⟩, Hr⟩,
  exact ⟨Hp, ⟨Hq, Hr⟩⟩,
end

-- 3ª demostración
example
  : (p ∧ q) ∧ r → p ∧ (q ∧ r) :=
λ ⟨⟨Hp, Hq⟩, Hr⟩, ⟨Hp, ⟨Hq, Hr⟩⟩

-- 4ª demostración
example
  (Hpqr : (p ∧ q) ∧ r)
  : p ∧ (q ∧ r) :=
have Hpq : p ∧ q,
  from and.left Hpqr,
have Hr : r,
  from and.right Hpqr,
have Hp : p,
  from and.left Hpq,
have Hq : q,
  from and.right Hpq,
have Hqr : q ∧ r,
  from and.intro Hq Hr,
show p ∧ (q ∧ r),
  from and.intro Hp Hqr

-- 5ª demostración
example
  (Hpqr : (p ∧ q) ∧ r)
  : p ∧ (q ∧ r) :=
-- by library_search
(and_assoc p q).mp Hpqr

-- 6ª demostración
example
  (Hpqr : (p ∧ q) ∧ r)
  : p ∧ (q ∧ r) :=
-- by hint
by tauto

-- 7ª demostración
example
  (Hpqr : (p ∧ q) ∧ r)
  : p ∧ (q ∧ r) :=
by finish

-- ----------------------------------------------------
-- Ejercicio 18. Demostrar
--    p ∧ q ⊢ p → q
-- ----------------------------------------------------

-- 1ª demostración
example
  (Hpq : p ∧ q)
  : p → q :=
begin
  intro p,
  exact Hpq.right,
end

-- 2ª demostración
example
  (Hpq : p ∧ q)
  : p → q :=
λ _, Hpq.2

-- 3ª demostración
example
  (Hpq : p ∧ q)
  : p → q :=
assume Hp : p,
show q,
  from and.right Hpq

-- 4ª demostración
example
  (Hpq : p ∧ q)
  : p → q :=
-- by hint
by tauto

-- 5ª demostración
example
  (Hpq : p ∧ q)
  : p → q :=
by finish

-- ----------------------------------------------------
-- Ejercicio 19. Demostrar
--    (p → q) ∧ (p → r) ⊢ p → q ∧ r
-- ----------------------------------------------------

-- 1ª demostración
example
  (H : (p → q) ∧ (p → r))
  : p → q ∧ r :=
begin
  cases H with Hpq Hpr,
  intro Hp,
  split,
  { apply Hpq,
    exact Hp, },
  { apply Hpr,
    exact Hp, },
end

-- 2ª demostración
example
  (H : (p → q) ∧ (p → r))
  : p → q ∧ r :=
begin
  cases H with Hpq Hpr,
  intro Hp,
  split,
  { exact Hpq Hp, },
  { exact Hpr Hp, },
end

-- 3ª demostración
example
  (H : (p → q) ∧ (p → r))
  : p → q ∧ r :=
begin
  cases H with Hpq Hpr,
  intro Hp,
  exact ⟨Hpq Hp, Hpr Hp⟩,
end

-- 4ª demostración
example
  : (p → q) ∧ (p → r) → (p → q ∧ r) :=
begin
  rintros ⟨Hpq, Hpr⟩ Hp,
  exact ⟨Hpq Hp, Hpr Hp⟩,
end

-- 5ª demostración
example
  : (p → q) ∧ (p → r) → (p → q ∧ r) :=
λ ⟨Hpq, Hpr⟩ Hp, ⟨Hpq Hp, Hpr Hp⟩

-- 6ª demostración
example
  (H : (p → q) ∧ (p → r))
  : p → q ∧ r :=
have Hpq : p → q,
  from and.left H,
have Hpr : p → r,
  from and.right H,
assume Hp : p,
have Hq : q,
  from Hpq Hp,
have Hr : r,
  from Hpr Hp,
show q ∧ r,
  from and.intro Hq Hr

-- 7ª demostración
example
  (H : (p → q) ∧ (p → r))
  : p → q ∧ r :=
-- by library_search
imp_and_distrib.mpr H

-- 8ª demostración
example
  (H : (p → q) ∧ (p → r))
  : p → q ∧ r :=
-- by hint
by tauto

-- 9ª demostración
example
  (H : (p → q) ∧ (p → r))
  : p → q ∧ r :=
by finish

-- ----------------------------------------------------
-- Ejercicio 20. Demostrar
--    p → q ∧ r ⊢ (p → q) ∧ (p → r)
-- ----------------------------------------------------

-- 1ª demostración
example
  (H : p → q ∧ r)
  : (p → q) ∧ (p → r) :=
begin
  split,
  { intro Hp,
    have Hqr : q ∧ r,
      from H Hp,
    exact Hqr.left, },
  { intro Hp,
    have Hqr : q ∧ r,
      from H Hp,
    exact Hqr.right, },
end

-- 2ª demostración
example
  (H : p → q ∧ r)
  : (p → q) ∧ (p → r) :=
begin
  split,
  { intro Hp,
    exact (H Hp).left, },
  { intro Hp,
    exact (H Hp).right, },
end

-- 3ª demostración
example
  (H : p → q ∧ r)
  : (p → q) ∧ (p → r) :=
⟨λ Hp, (H Hp).left,
 λ Hp, (H Hp).right⟩

-- 4ª demostración
example
  (H : p → q ∧ r)
  : (p → q) ∧ (p → r) :=
have Hpq : p → q, from
  assume Hp : p,
  have Hqr : q ∧ r,
    from H Hp,
  show q,
    from and.left Hqr,
have Hpr : p → r, from
  assume Hp : p,
  have Hqr : q ∧ r,
    from H Hp,
  show r,
    from and.right Hqr,
show (p → q) ∧ (p → r),
  from and.intro Hpq Hpr

-- 5ª demostración
example
  (H : p → q ∧ r)
  : (p → q) ∧ (p → r) :=
and.intro
  ( assume Hp : p,
    have Hqr : q ∧ r,
      from H Hp,
    show q,
      from and.left Hqr)
  ( assume Hp : p,
    have Hqr : q ∧ r,
      from H Hp,
    show r,
      from and.right Hqr)

-- 6ª demostración
example
  (H : p → q ∧ r)
  : (p → q) ∧ (p → r) :=
-- by library_search
imp_and_distrib.mp H

-- 7ª demostración
example
  (H : p → q ∧ r)
  : (p → q) ∧ (p → r) :=
-- by hint
by finish

-- ----------------------------------------------------
-- Ejercicio 21. Demostrar
--    p → (q → r) ⊢ p ∧ q → r
-- ----------------------------------------------------

-- 1ª demostración
example
  (H : p → (q → r))
  : p ∧ q → r :=
begin
  intro Hpq,
  apply H,
  { exact Hpq.left, },
  { exact Hpq.right, },
end

-- 2ª demostración
example
  (H : p → (q → r))
  : p ∧ q → r :=
begin
  intro Hpq,
  exact (H Hpq.left) Hpq.right,
end

-- 3ª demostración
example
  (H : p → (q → r))
  : p ∧ q → r :=
λ Hpq, (H Hpq.left) Hpq.right

-- 4ª demostración
example
  (H : p → (q → r))
  : p ∧ q → r :=
λ Hpq, H Hpq.1 Hpq.2

-- 5ª demostración
example
  (H : p → (q → r))
  : p ∧ q → r :=
assume Hpq : p ∧ q,
have Hp : p,
  from and.left Hpq,
have Hq : q,
  from and.right Hpq,
have Hqr : q → r,
  from H Hp,
show r,
  from Hqr Hq

-- 6ª demostración
example
  (H : p → (q → r))
  : p ∧ q → r :=
-- by library_search
and_imp.mpr H

-- 7ª demostración
example
  (H : p → (q → r))
  : p ∧ q → r :=
-- by hint
by tauto

-- 8ª demostración
example
  (H : p → (q → r))
  : p ∧ q → r :=
by finish

-- ----------------------------------------------------
-- Ejercicio 22. Demostrar
--    p ∧ q → r ⊢ p → (q → r)
-- ----------------------------------------------------

-- 1ª demostración
example
  (H : p ∧ q → r)
  : p → (q → r) :=
begin
  intros Hp Hq,
  apply H,
  split,
  { exact Hp, },
  { exact Hq, },
end

-- 2ª demostración
example
  (H : p ∧ q → r)
  : p → (q → r) :=
begin
  intros Hp Hq,
  apply H,
  exact ⟨Hp, Hq⟩,
end

-- 3ª demostración
example
  (H : p ∧ q → r)
  : p → (q → r) :=
begin
  intros Hp Hq,
  exact H ⟨Hp, Hq⟩,
end

-- 4ª demostración
example
  (H : p ∧ q → r)
  : p → (q → r) :=
λ Hp Hq, H ⟨Hp, Hq⟩

-- 5ª demostración
example
  (H : p ∧ q → r)
  : p → (q → r) :=
assume Hp : p,
show q → r, from
  assume Hq : q,
  have Hpq : p ∧ q,
    from and.intro Hp Hq,
  show r,
    from H Hpq

-- 6ª demostración
example
  (H : p ∧ q → r)
  : p → (q → r) :=
-- by library_search
and_imp.mp H

-- 7ª demostración
example
  (H : p ∧ q → r)
  : p → (q → r) :=
-- by hint
by finish

-- ----------------------------------------------------
-- Ejercicio 23. Demostrar
--    (p → q) → r ⊢ p ∧ q → r
-- ----------------------------------------------------

-- 1ª demostración
example
  (H : (p → q) → r)
  : p ∧ q → r :=
begin
  intro Hpq,
  apply H,
  intro Hp,
  exact Hpq.right,
end

-- 2ª demostración
example
  (H : (p → q) → r)
  : p ∧ q → r :=
begin
  intro Hpq,
  apply H,
  exact (λ Hp, Hpq.right),
end

-- 3ª demostración
example
  (H : (p → q) → r)
  : p ∧ q → r :=
begin
  intro Hpq,
  exact H (λ Hp, Hpq.right),
end

-- 4ª demostración
example
  (H : (p → q) → r)
  : p ∧ q → r :=
λ Hpq, H (λ _, Hpq.right)

-- 5ª demostración
example
  (H : (p → q) → r)
  : p ∧ q → r :=
assume Hpq : p ∧ q,
have H1 : p → q, from
  assume Hp : p,
  show q,
    from and.right Hpq,
show r,
  from H H1

-- 6ª demostración
example
  (H : (p → q) → r)
  : p ∧ q → r :=
-- by hint
by finish

-- ----------------------------------------------------
-- Ejercicio 24. Demostrar
--    p ∧ (q → r) ⊢ (p → q) → r
-- ----------------------------------------------------

-- 1ª demostración
example
  (H : p ∧ (q → r))
  : (p → q) → r :=
begin
  intro Hpq,
  cases H with Hp Hqr,
  apply Hqr,
  apply Hpq,
  exact Hp,
end

-- 2ª demostración
example
  (H : p ∧ (q → r))
  : (p → q) → r :=
begin
  intro Hpq,
  cases H with Hp Hqr,
  apply Hqr,
  exact Hpq Hp,
end

-- 3ª demostración
example
  (H : p ∧ (q → r))
  : (p → q) → r :=
begin
  intro Hpq,
  cases H with Hp Hqr,
  exact Hqr (Hpq Hp),
end

-- 4ª demostración
example
  (H : p ∧ (q → r))
  : (p → q) → r :=
begin
  intro Hpq,
  exact H.2 (Hpq H.1),
end

-- 5ª demostración
example
  (H : p ∧ (q → r))
  : (p → q) → r :=
λ Hpq, H.2 (Hpq H.1)

-- 6ª demostración
example
  (H : p ∧ (q → r))
  : (p → q) → r :=
assume Hpq : p → q,
have Hp : p,
  from and.left H,
have Hq : q,
  from Hpq Hp,
have Hqr : q → r,
  from H.right,
show r,
  from Hqr Hq

-- 7ª demostració
example
  (H : p ∧ (q → r))
  : (p → q) → r :=
-- by hint
by tauto

-- 8ª demostració
example
  (H : p ∧ (q → r))
  : (p → q) → r :=
-- by hint
by finish

-- § Disyunciones
-- ==============

-- ----------------------------------------------------
-- Ejercicio 25. Demostrar
--    p ⊢ p ∨ q
-- ----------------------------------------------------

-- 1ª demostración
example
  (H : p)
  : p ∨ q :=
begin
  left,
  exact H,
end

-- 2ª demostración
example
  (H : p)
  : p ∨ q :=
or.intro_left q H

-- 3ª demostración
example
  (H : p)
  : p ∨ q :=
-- by library_search
or.inl H

-- 4ª demostración
example
  (H : p)
  : p ∨ q :=
-- by hint
by tauto

-- 5ª demostración
example
  (H : p)
  : p ∨ q :=
by finish

-- ----------------------------------------------------
-- Ejercicio 26. Demostrar
--    q ⊢ p ∨ q
-- ----------------------------------------------------

-- 1ª demostración
example
  (H : q)
  : p ∨ q :=
begin
  right,
  exact H,
end

-- 2ª demostración
example
  (H : q)
  : p ∨ q :=
or.intro_right p H

-- 3ª demostración
example
  (H : q)
  : p ∨ q :=
-- by library_search
or.inr H

-- 4ª demostración
example
  (H : q)
  : p ∨ q :=
-- by hint
by tauto

-- 5ª demostración
example
  (H : q)
  : p ∨ q :=
by finish

-- ----------------------------------------------------
-- Ejercicio 27. Demostrar
--    p ∨ q ⊢ q ∨ p
-- ----------------------------------------------------

-- 1ª demostración
example
  (H : p ∨ q)
  : q ∨ p :=
begin
  cases H with Hp Hq,
  { right,
    exact Hp, },
  { left,
    exact Hq, },
end

-- 2ª demostración
example
  (H : p ∨ q)
  : q ∨ p :=
begin
  cases H with Hp Hq,
  { exact or.inr Hp, },
  { exact or.inl Hq, },
end

-- 3ª demostración
example
  (H : p ∨ q)
  : q ∨ p :=
or.elim H
  ( assume Hp : p,
    show q ∨ p,
      from or.inr Hp)
  ( assume Hq : q,
    show q ∨ p,
      from or.inl Hq)

-- 4ª demostración
example
  (H : p ∨ q)
  : q ∨ p :=
or.elim H
  ( assume Hp : p,
    or.inr Hp)
  ( assume Hq : q,
    or.inl Hq)

-- 5ª demostración
example
  (H : p ∨ q)
  : q ∨ p :=
or.elim H
  ( λ Hp, or.inr Hp)
  ( λ Hq, or.inl Hq)

-- 6ª demostración
example
  (H : p ∨ q)
  : q ∨ p :=
or.elim H or.inr or.inl

-- 7ª demostración
example
  (H : p ∨ q)
  : q ∨ p :=
-- by library_search
or.swap H

-- 8ª demostración
example
  (H : p ∨ q)
  : q ∨ p :=
-- by hint
by tauto

-- 9ª demostración
example
  (H : p ∨ q)
  : q ∨ p :=
by finish

-- ----------------------------------------------------
-- Ejercicio 28. Demostrar
--    q → r ⊢ p ∨ q → p ∨ r
-- ----------------------------------------------------

-- 1ª demostración
example
  (H : q → r)
  : p ∨ q → p ∨ r :=
begin
  intro H1,
  cases H1 with Hp Hq,
  { left,
    exact Hp, },
  { right,
    apply H,
    exact Hq, },
end

-- 2ª demostración
example
  (H : q → r)
  : p ∨ q → p ∨ r :=
begin
  rintro (Hp | Hq),
  { left,
    exact Hp, },
  { right,
    exact H Hq, },
end

-- 3ª demostración
example
  (H : q → r)
  : p ∨ q → p ∨ r :=
begin
  rintro (Hp | Hq),
  { exact or.inl Hp, },
  { exact or.inr (H Hq), },
end

-- 4ª demostración
example
  (H : q → r)
  : p ∨ q → p ∨ r :=
assume H1 : p ∨ q,
or.elim H1
  ( assume Hp : p,
    show p ∨ r,
      from or.inl Hp)
  ( assume Hq : q,
    have Hr : r,
      from H Hq,
    show p ∨ r,
      from or.inr Hr)

-- 5ª demostración
example
  (H : q → r)
  : p ∨ q → p ∨ r :=
assume H1 : p ∨ q,
or.elim H1
  ( assume Hp : p,
    or.inl Hp)
  ( assume Hq : q,
    have Hr : r,
      from H Hq,
    or.inr Hr)

-- 6ª demostración
example
  (H : q → r)
  : p ∨ q → p ∨ r :=
assume H1 : p ∨ q,
or.elim H1
  ( assume Hp : p,
    or.inl Hp)
  ( assume Hq : q,
    or.inr (H Hq))

-- 7ª demostración
example
  (H : q → r)
  : p ∨ q → p ∨ r :=
assume H1 : p ∨ q,
or.elim H1
  ( λ Hp, or.inl Hp)
  ( λ Hq, or.inr (H Hq))

-- 8ª demostración
example
  (H : q → r)
  : p ∨ q → p ∨ r :=
assume H1 : p ∨ q,
or.elim H1
  or.inl
  ( λ Hq, or.inr (H Hq))

-- 9ª demostración
example
  (H : q → r)
  : p ∨ q → p ∨ r :=
λ H1, or.elim H1 or.inl (λ Hq, or.inr (H Hq))

-- 10ª demostración
example
  (H : q → r)
  : p ∨ q → p ∨ r :=
-- by library_search
or.imp_right H

-- ----------------------------------------------------
-- Ejercicio 29. Demostrar
--    p ∨ p ⊢ p
-- ----------------------------------------------------

-- 1ª demostración
example
  (H : p ∨ p)
  : p :=
begin
  cases H with Hp Hp,
  { exact Hp, },
  { exact Hp, },
end

-- 2ª demostración
example
  (H : p ∨ p)
  : p :=
by cases H ; assumption

-- 3ª demostración
example
  (H : p ∨ p)
  : p :=
or.elim H
  ( assume Hp : p,
    show p,
      from Hp)
  ( assume Hp : p,
    show p,
      from Hp)

-- 4ª demostración
example
  (H : p ∨ p)
  : p :=
or.elim H
  ( assume Hp : p,
    Hp)
  ( assume Hp : p,
    Hp)

-- 5ª demostración
example
  (H : p ∨ p)
  : p :=
or.elim H
  ( λ Hp, Hp)
  ( λ Hp, Hp)

-- 6ª demostración
example
  (H : p ∨ p)
  : p :=
or.elim H id id

-- 7ª demostración
example
  (H : p ∨ p)
  : p :=
-- by library_search
(or_self p).mp H

-- 8ª demostración
example
  (H : p ∨ p)
  : p :=
-- by hint
by tauto

-- 9ª demostración
example
  (H : p ∨ p)
  : p :=
by finish

-- ----------------------------------------------------
-- Ejercicio 30. Demostrar
--    p ⊢ p ∨ p
-- ----------------------------------------------------

-- 1ª demostración
example
  (H : p)
  : p ∨ p :=
-- by library_search
or.inl H

-- 2ª demostración
example
  (H : p)
  : p ∨ p :=
-- by hint
by tauto

-- 3ª demostración
example
  (H : p)
  : p ∨ p :=
by finish

-- ----------------------------------------------------
-- Ejercicio 31. Demostrar
--    p ∨ (q ∨ r) ⊢ (p ∨ q) ∨ r
-- ----------------------------------------------------

-- 1ª demostración
example
  (H : p ∨ (q ∨ r))
  : (p ∨ q) ∨ r :=
begin
  cases H with Hp Hqr,
  { left,
    left,
    exact Hp, },
  { cases Hqr with Hq Hr,
    { left,
      right,
      exact Hq, },
    { right,
      exact Hr, }},
end

-- 2ª demostración
example
  (H : p ∨ (q ∨ r))
  : (p ∨ q) ∨ r :=
or.elim H
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    show (p ∨ q) ∨ r,
      from or.inl Hpq)
  ( assume Hqr : q ∨ r,
    show (p ∨ q) ∨ r, from
      or.elim Hqr
        ( assume Hq : q,
          have Hpq : p ∨ q,
            from or.inr Hq,
          show (p ∨ q) ∨ r,
            from or.inl Hpq)
        ( assume Hr : r,
          show (p ∨ q) ∨ r,
            from or.inr Hr))

-- 3ª demostración
example
  (H : p ∨ (q ∨ r))
  : (p ∨ q) ∨ r :=
or.elim H
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    show (p ∨ q) ∨ r,
      from or.inl Hpq)
  ( assume Hqr : q ∨ r,
    show (p ∨ q) ∨ r, from
      or.elim Hqr
        ( assume Hq : q,
          have Hpq : p ∨ q,
            from or.inr Hq,
          or.inl Hpq)
        ( assume Hr : r,
          or.inr Hr))

-- 4ª demostración
example
  (H : p ∨ (q ∨ r))
  : (p ∨ q) ∨ r :=
or.elim H
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    show (p ∨ q) ∨ r,
      from or.inl Hpq)
  ( assume Hqr : q ∨ r,
    show (p ∨ q) ∨ r, from
      or.elim Hqr
        ( assume Hq : q,
          have Hpq : p ∨ q,
            from or.inr Hq,
          or.inl Hpq)
        or.inr)

-- 5ª demostración
example
  (H : p ∨ (q ∨ r))
  : (p ∨ q) ∨ r :=
or.elim H
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    show (p ∨ q) ∨ r,
      from or.inl Hpq)
  ( assume Hqr : q ∨ r,
    show (p ∨ q) ∨ r, from
      or.elim Hqr
        ( λ Hq, or.inl (or.inr Hq))
        or.inr)

-- 6ª demostración
example
  (H : p ∨ (q ∨ r))
  : (p ∨ q) ∨ r :=
or.elim H
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    show (p ∨ q) ∨ r,
      from or.inl Hpq)
  ( λ Hqr, or.elim Hqr ( λ Hq, or.inl (or.inr Hq)) or.inr)

-- 7ª demostración
example
  (H : p ∨ (q ∨ r))
  : (p ∨ q) ∨ r :=
or.elim H
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    or.inl Hpq)
  (λ Hqr, or.elim Hqr ( λ Hq, or.inl (or.inr Hq)) or.inr)

-- 8ª demostración
example
  (H : p ∨ (q ∨ r))
  : (p ∨ q) ∨ r :=
or.elim H
  ( assume Hp : p,
    or.inl (or.inl Hp))
  (λ Hqr, or.elim Hqr ( λ Hq, or.inl (or.inr Hq)) or.inr)

-- 9ª demostración
example
  (H : p ∨ (q ∨ r))
  : (p ∨ q) ∨ r :=
or.elim H
  (λ Hp, or.inl (or.inl Hp))
  (λ Hqr, or.elim Hqr ( λ Hq, or.inl (or.inr Hq)) or.inr)

-- 10ª demostración
example
  (H : p ∨ (q ∨ r))
  : (p ∨ q) ∨ r :=
-- by library_search
or.assoc.mpr H

-- 11ª demostración
example
  (H : p ∨ (q ∨ r))
  : (p ∨ q) ∨ r :=
-- by hint
by tauto

-- 12ª demostración
example
  (H : p ∨ (q ∨ r))
  : (p ∨ q) ∨ r :=
by finish

-- ----------------------------------------------------
-- Ejercicio 32. Demostrar
--    (p ∨ q) ∨ r ⊢ p ∨ (q ∨ r)
-- ----------------------------------------------------

-- 1ª demostración
example
  (H : (p ∨ q) ∨ r)
  : p ∨ (q ∨ r) :=
begin
  rcases H with ((Hp | Hq) | Hr),
  { left,
    exact Hp, },
  { right,
    left,
    exact Hq, },
  { right,
    right,
    exact Hr, },
end

-- 2ª demostración
example
  (H : (p ∨ q) ∨ r)
  : p ∨ (q ∨ r) :=
or.elim H
  ( assume Hpq : p ∨ q,
    show p ∨ q ∨ r, from
      or.elim Hpq
        ( assume Hp : p,
          show p ∨ (q ∨ r),
            from or.inl Hp)
        ( assume Hq : q,
          have Hqr: q ∨ r,
            from or.inl Hq,
          show p ∨ (q ∨ r),
            from or.inr Hqr))
  ( assume Hr : r,
    have Hqr: q ∨ r,
      from or.inr Hr,
    show p ∨ (q ∨ r),
      from or.inr Hqr)

-- 3ª demostración
example
  (H : (p ∨ q) ∨ r)
  : p ∨ (q ∨ r) :=
or.elim H
  ( λ Hpq, or.elim Hpq or.inl (λ Hq, or.inr (or.inl Hq)))
  ( λ Hr, or.inr (or.inr Hr))

-- 4ª demostración
example
  (H : (p ∨ q) ∨ r)
  : p ∨ (q ∨ r) :=
-- by library_search
or.assoc.mp H

-- 5ª demostración
example
  (H : (p ∨ q) ∨ r)
  : p ∨ (q ∨ r) :=
-- by hint
by tauto

-- 6ª demostración
example
  (H : (p ∨ q) ∨ r)
  : p ∨ (q ∨ r) :=
by finish

-- ----------------------------------------------------
--   Ejercicio 33. Demostrar
--      p ∧ (q ∨ r) ⊢ (p ∧ q) ∨ (p ∧ r)
-- ----------------------------------------------------

-- 1ª demostración
example
  (H : p ∧ (q ∨ r))
  : (p ∧ q) ∨ (p ∧ r) :=
begin
  cases H with Hp Hqr,
  cases Hqr with Hq Hr,
  { left,
    split,
    { exact Hp, },
    { exact Hq, }},
  { right,
    split,
    { exact Hp, },
    { exact Hr, }},
end

-- 2ª demostración
example
  (H : p ∧ (q ∨ r))
  : (p ∧ q) ∨ (p ∧ r) :=
begin
  cases H with Hp Hqr,
  cases Hqr with Hq Hr,
  { left,
    exact ⟨Hp, Hq⟩, },
  { right,
    exact ⟨Hp, Hr⟩, },
end

-- 3ª demostración
example
  (H : p ∧ (q ∨ r))
  : (p ∧ q) ∨ (p ∧ r) :=
have Hp : p,
  from and.left H,
have Hqr : q ∨ r,
  from and.right H,
or.elim Hqr
  ( assume Hq : q,
    have Hpq : p ∧ q,
      from and.intro Hp Hq,
    show (p ∧ q) ∨ (p ∧ r),
      from or.inl Hpq)
  ( assume Hr : r,
    have Hpr : p ∧ r,
      from and.intro Hp Hr,
    show (p ∧ q) ∨ (p ∧ r),
      from or.inr Hpr)

-- 4ª demostración
example
  (H : p ∧ (q ∨ r))
  : (p ∧ q) ∨ (p ∧ r) :=
or.elim H.2
  (λ Hq, or.inl ⟨H.1, Hq⟩)
  (λ Hr, or.inr ⟨H.1, Hr⟩)

-- 5ª demostración
example
  (H : p ∧ (q ∨ r))
  : (p ∧ q) ∨ (p ∧ r) :=
-- by library_search
and_or_distrib_left.mp H

-- 6ª demostración
example
  (H : p ∧ (q ∨ r))
  : (p ∧ q) ∨ (p ∧ r) :=
-- by hint
by finish

-- ----------------------------------------------------
-- Ejercicio 34. Demostrar
--    (p ∧ q) ∨ (p ∧ r) ⊢ p ∧ (q ∨ r)
-- ----------------------------------------------------

-- 1ª demostración
example
  (H : (p ∧ q) ∨ (p ∧ r))
  : p ∧ (q ∨ r) :=
begin
  rcases H with (⟨Hp,Hq⟩ | ⟨Hp, Hr⟩),
  { exact ⟨Hp, or.inl Hq⟩, },
  { exact ⟨Hp, or.inr Hr⟩, },
end

-- 2ª demostración
example
  (H : (p ∧ q) ∨ (p ∧ r))
  : p ∧ (q ∨ r) :=
or.elim H
  ( assume Hpq : p ∧ q,
    have Hp : p,
      from and.left Hpq,
    have Hq : q,
      from and.right Hpq,
    have Hqr : q ∨ r,
      from or.inl Hq,
    show p ∧ (q ∨ r),
      from and.intro Hp Hqr)
  ( assume Hpr : p ∧ r,
    have Hp : p,
      from and.left Hpr,
    have Hr : r,
      from and.right Hpr,
    have Hqr : q ∨ r,
      from or.inr Hr,
    show p ∧ (q ∨ r),
      from and.intro Hp Hqr)

-- 3ª demostración
example
  (H : (p ∧ q) ∨ (p ∧ r))
  : p ∧ (q ∨ r) :=
or.elim H
  ( assume ⟨Hp, Hq⟩,
    have Hqr : q ∨ r,
      from or.inl Hq,
    show p ∧ (q ∨ r),
      from and.intro Hp Hqr)
  ( assume ⟨Hp, Hr⟩,
    have Hqr : q ∨ r,
      from or.inr Hr,
    show p ∧ (q ∨ r),
      from and.intro Hp Hqr)

-- 4ª demostración
example
  (H : (p ∧ q) ∨ (p ∧ r))
  : p ∧ (q ∨ r) :=
or.elim H
  (λ ⟨Hp, Hq⟩, ⟨Hp ,or.inl Hq⟩)
  (λ ⟨Hp, Hr⟩, ⟨Hp, or.inr Hr⟩)

-- 5ª demostración
example
  (H : (p ∧ q) ∨ (p ∧ r))
  : p ∧ (q ∨ r) :=
-- by library_search
and_or_distrib_left.mpr H

-- 6ª demostración
example
  (H : (p ∧ q) ∨ (p ∧ r))
  : p ∧ (q ∨ r) :=
-- by hint
by tauto

-- 7ª demostración
example
  (H : (p ∧ q) ∨ (p ∧ r))
  : p ∧ (q ∨ r) :=
by finish

-- ----------------------------------------------------
-- Ejercicio 35. Demostrar
--    p ∨ (q ∧ r) ⊢ (p ∨ q) ∧ (p ∨ r)
-- ----------------------------------------------------

-- 1ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
begin
  cases H with Hp Hqr,
  { split,
    { left,
      exact Hp, },
    { left,
      exact Hp, }},
  { split,
    { right,
      exact Hqr.left, },
    { right,
      exact Hqr.right, }},
end

-- 2ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
begin
  cases H with Hp Hqr,
  { split,
    { exact or.inl Hp, },
    { exact or.inl Hp, }},
  { split,
    { exact or.inr Hqr.left, },
    { exact or.inr Hqr.right, }},
end

-- 3ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
begin
  cases H with Hp Hqr,
  { exact ⟨or.inl Hp, or.inl Hp⟩, },
  { exact ⟨or.inr Hqr.left, or.inr Hqr.right⟩, },
end

-- 4ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
or.elim H
  (λ Hp, ⟨or.inl Hp, or.inl Hp⟩)
  (λ Hqr, ⟨or.inr Hqr.1, or.inr Hqr.2⟩)

-- 5ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
or.elim H
  (λ h, ⟨or.inl h,   or.inl h⟩)
  (λ h, ⟨or.inr h.1, or.inr h.2⟩)

-- 6ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
or.elim H
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    have Hpr : p ∨ r,
      from or.inl Hp,
    show (p ∨ q) ∧ (p ∨ r),
      from and.intro Hpq Hpr)
  ( assume Hqr : q ∧ r,
    have Hq : q,
      from and.left Hqr,
    have Hr : r,
      from and.right Hqr,
    have Hpq : p ∨ q,
      from or.inr Hq,
    have Hpr : p ∨ r,
      from or.inr Hr,
    show (p ∨ q) ∧ (p ∨ r),
      from and.intro Hpq Hpr)

-- 7ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
or.elim H
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    have Hpr : p ∨ r,
      from or.inl Hp,
    show (p ∨ q) ∧ (p ∨ r),
      from and.intro Hpq Hpr)
  ( assume Hqr : q ∧ r,
    have Hq : q,
      from and.left Hqr,
    have Hr : r,
      from and.right Hqr,
    have Hpq : p ∨ q,
      from or.inr Hq,
    have Hpr : p ∨ r,
      from or.inr Hr,
    and.intro Hpq Hpr)

-- 8ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
or.elim H
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    have Hpr : p ∨ r,
      from or.inl Hp,
    show (p ∨ q) ∧ (p ∨ r),
      from and.intro Hpq Hpr)
  ( assume Hqr : q ∧ r,
    have Hq : q,
      from and.left Hqr,
    have Hr : r,
      from and.right Hqr,
    and.intro (or.inr Hq) (or.inr Hr))

-- 9ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
or.elim H
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    have Hpr : p ∨ r,
      from or.inl Hp,
    show (p ∨ q) ∧ (p ∨ r),
      from and.intro Hpq Hpr)
  ( assume Hqr : q ∧ r,
    and.intro (or.inr (and.left Hqr)) (or.inr (and.right Hqr)))

-- 10ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
or.elim H
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    have Hpr : p ∨ r,
      from or.inl Hp,
    show (p ∨ q) ∧ (p ∨ r),
      from and.intro Hpq Hpr)
  ( assume Hqr : q ∧ r,
    and.intro (or.inr Hqr.1) (or.inr Hqr.2))

-- 11ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
or.elim H
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    have Hpr : p ∨ r,
      from or.inl Hp,
    show (p ∨ q) ∧ (p ∨ r),
      from and.intro Hpq Hpr)
  ( assume Hqr : q ∧ r,
    ⟨or.inr Hqr.1, or.inr Hqr.2⟩)

-- 12ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
or.elim H
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    have Hpr : p ∨ r,
      from or.inl Hp,
    show (p ∨ q) ∧ (p ∨ r),
      from and.intro Hpq Hpr)
  ( λ Hqr, ⟨or.inr Hqr.1, or.inr Hqr.2⟩)

-- 13ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
or.elim H
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    have Hpr : p ∨ r,
      from or.inl Hp,
    and.intro Hpq Hpr)
  ( λ Hqr, ⟨or.inr Hqr.1, or.inr Hqr.2⟩)

-- 14ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
or.elim H
  ( assume Hp : p,
    have Hpq : p ∨ q,
      from or.inl Hp,
    have Hpr : p ∨ r,
      from or.inl Hp,
    ⟨Hpq, Hpr⟩)
  ( λ Hqr, ⟨or.inr Hqr.1, or.inr Hqr.2⟩)

-- 15ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
or.elim H
  ( assume Hp : p,
    ⟨or.inl Hp, or.inl Hp⟩)
  ( λ Hqr, ⟨or.inr Hqr.1, or.inr Hqr.2⟩)

-- 16ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
or.elim H
  ( λ Hp, ⟨or.inl Hp, or.inl Hp⟩)
  ( λ Hqr, ⟨or.inr Hqr.1, or.inr Hqr.2⟩)

-- 17ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
-- by library_search
or_and_distrib_left.mp H

-- 18ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
-- by hint
by tauto

-- 19ª demostración
example
  (H : p ∨ (q ∧ r))
  : (p ∨ q) ∧ (p ∨ r) :=
by finish

/-


― ‹La demostración estructurada es›
lemma ejercicio_35_1:
  assumes "p ∨ (q ∧ r)"
  shows   "(p ∨ q) ∧ (p ∨ r)"
using assms
proof
  assume "p"
  show "(p ∨ q) ∧ (p ∨ r)"
  proof
    show "p ∨ q" using ‹p› ..
  next
    show "p ∨ r" using ‹p› ..
  qed
next
  assume "q ∧ r"
  show "(p ∨ q) ∧ (p ∨ r)"
  proof
    have "q" using ‹q ∧ r› ..
    thus "p ∨ q" ..
  next
    have "r" using ‹q ∧ r› ..
    thus "p ∨ r" ..
  qed
qed

― ‹La demostración detallada es›
lemma ejercicio_35_2:
  assumes "p ∨ (q ∧ r)"
  shows   "(p ∨ q) ∧ (p ∨ r)"
using assms
proof (rule disjE)
  assume "p"
  show "(p ∨ q) ∧ (p ∨ r)"
  proof (rule conjI)
    show "p ∨ q" using ‹p› by (rule disjI1)
  next
    show "p ∨ r" using ‹p› by (rule disjI1)
  qed
next
  assume "q ∧ r"
  show "(p ∨ q) ∧ (p ∨ r)"
  proof (rule conjI)
    have "q" using ‹q ∧ r› ..
    thus "p ∨ q" by (rule disjI2)
  next
    have "r" using ‹q ∧ r› by (rule conjunct2)
    thus "p ∨ r" by (rule disjI2)
  qed
qed

― ‹La demostración automática es›
lemma ejercicio_35_3:
  assumes "p ∨ (q ∧ r)"
  shows   "(p ∨ q) ∧ (p ∨ r)"
using assms
by auto

-- ----------------------------------------------------
  Ejercicio 36. Demostrar
     (p ∨ q) ∧ (p ∨ r) ⊢ p ∨ (q ∧ r)
-- ----------------------------------------------------

― ‹La demostración estructurada es›
lemma ejercicio_36_1:
  assumes "(p ∨ q) ∧ (p ∨ r)"
  shows   "p ∨ (q ∧ r)"
proof -
  have "p ∨ q" using assms ..
  thus "p ∨ (q ∧ r)"
  proof
    assume "p"
    thus "p ∨ (q ∧ r)" ..
  next
    assume "q"
    have "p ∨ r" using assms ..
    thus "p ∨ (q ∧ r)"
    proof
      assume "p"
      thus "p ∨ (q ∧ r)" ..
    next
      assume "r"
      with ‹q› have "q ∧ r" ..
      thus "p ∨ (q ∧ r)" ..
    qed
  qed
qed

― ‹La demostración detallada es›
lemma ejercicio_36_2:
  assumes "(p ∨ q) ∧ (p ∨ r)"
  shows   "p ∨ (q ∧ r)"
proof -
  have "p ∨ q" using assms by (rule conjunct1)
  thus "p ∨ (q ∧ r)"
  proof (rule disjE)
    assume "p"
    thus "p ∨ (q ∧ r)" by (rule disjI1)
  next
    assume "q"
    have "p ∨ r" using assms by (rule conjunct2)
    thus "p ∨ (q ∧ r)"
    proof (rule disjE)
      assume "p"
      thus "p ∨ (q ∧ r)" by (rule disjI1)
    next
      assume "r"
      have "q ∧ r" using ‹q› ‹r› by (rule conjI)
      thus "p ∨ (q ∧ r)" by (rule disjI2)
    qed
  qed
qed

― ‹La demostración automática es›
lemma ejercicio_36_3:
  assumes "(p ∨ q) ∧ (p ∨ r)"
  shows   "p ∨ (q ∧ r)"
using assms
by auto

-- ----------------------------------------------------
  Ejercicio 37. Demostrar
     (p → r) ∧ (q → r) ⊢ p ∨ q → r
-- ----------------------------------------------------

― ‹La demostración estructurada es›
lemma ejercicio_37_1:
  assumes "(p → r) ∧ (q → r)"
  shows   "p ∨ q → r"
proof
  assume "p ∨ q"
  thus "r"
  proof
    assume "p"
    have "p → r" using assms ..
    thus "r" using ‹p› ..
  next
    assume "q"
    have "q → r" using assms ..
    thus "r" using ‹q› ..
  qed
qed

― ‹La demostración detallada es›
lemma ejercicio_37_2:
  assumes "(p → r) ∧ (q → r)"
  shows   "p ∨ q → r"
proof (rule impI)
  assume "p ∨ q"
  thus "r"
  proof (rule disjE)
    assume "p"
    have "p → r" using assms by (rule conjunct1)
    thus "r" using ‹p› by (rule mp)
  next
    assume "q"
    have "q → r" using assms by (rule conjunct2)
    thus "r" using ‹q› by (rule mp)
  qed
qed

― ‹La demostración automática es›
lemma ejercicio_37_3:
  assumes "(p → r) ∧ (q → r)"
  shows   "p ∨ q → r"
using assms
by auto

-- ----------------------------------------------------
  Ejercicio 38. Demostrar
     p ∨ q → r ⊢ (p → r) ∧ (q → r)
-- ----------------------------------------------------

― ‹La demostración estructurada es›
lemma ejercicio_38_1:
  assumes "p ∨ q → r"
  shows   "(p → r) ∧ (q → r)"
proof
  show "p → r"
  proof
    assume "p"
    hence "p ∨ q" ..
    with assms show "r" ..
  qed
next
  show "q → r"
  proof
    assume "q"
    hence "p ∨ q" ..
    with assms show "r" ..
  qed
qed

― ‹La demostración detallada es›
lemma ejercicio_38_2:
  assumes "p ∨ q → r"
  shows   "(p → r) ∧ (q → r)"
proof (rule conjI)
  show "p → r"
  proof (rule impI)
    assume "p"
    hence "p ∨ q" by (rule disjI1)
    show "r" using assms ‹p ∨ q› by (rule mp)
  qed
next
  show "q → r"
  proof (rule impI)
    assume "q"
    hence "p ∨ q" by (rule disjI2)
    show "r" using assms ‹p ∨ q› by (rule mp)
  qed
qed

― ‹La demostración automática es›
lemma ejercicio_38_3:
  assumes "p ∨ q → r"
  shows   "(p → r) ∧ (q → r)"
using assms
by auto

section ‹Negación›

-- ----------------------------------------------------
  Ejercicio 39. Demostrar
     p ⊢ ¬¬p
-- ----------------------------------------------------

― ‹La demostración detallada es›
lemma ejercicio_39_1:
  assumes "p"
  shows   "¬¬p"
proof -
  show "¬¬p" using assms by (rule notnotI)
qed

― ‹La demostración automática es›
lemma ejercicio_39_2:
  assumes "p"
  shows   "¬¬p"
using assms
by auto

-- ----------------------------------------------------
  Ejercicio 40. Demostrar
     ¬p ⊢ p → q
-- ----------------------------------------------------

― ‹La demostración estructurada es›
lemma ejercicio_40_1:
  assumes "¬p"
  shows   "p → q"
proof
  assume "p"
  with assms(1) show "q" ..
qed

― ‹La demostración detallada es›
lemma ejercicio_40_2:
  assumes "¬p"
  shows   "p → q"
proof (rule impI)
  assume "p"
  show "q" using assms(1) ‹p› by (rule notE)
qed

― ‹La demostración automática es›
lemma ejercicio_40_3:
  assumes "¬p"
  shows   "p → q"
using assms
by auto

-- ----------------------------------------------------
  Ejercicio 41. Demostrar
     p → q ⊢ ¬q → ¬p
-- ----------------------------------------------------

― ‹La demostración estructurada es›
lemma ejercicio_41_1:
  assumes "p → q"
  shows   "¬q → ¬p"
proof
  assume "¬q"
  with assms(1) show "¬p" by (rule mt)
qed

― ‹La demostración detallada es›
lemma ejercicio_41_2:
  assumes "p → q"
  shows   "¬q → ¬p"
proof (rule impI)
  assume "¬q"
  show "¬p" using assms(1) ‹¬q› by (rule mt)
qed

― ‹La demostración automática es›
lemma ejercicio_41_3:
  assumes "p → q"
  shows   "¬q → ¬p"
using assms
by auto

-- ----------------------------------------------------
  Ejercicio 42. Demostrar
     p ∨ q, ¬q ⊢ p
-- ----------------------------------------------------

― ‹La demostración estructurada es›
lemma ejercicio_42_1:
  assumes "p ∨ q"
          "¬q"
  shows   "p"
using assms(1)
proof
  assume "p"
  thus "p" .
next
  assume "q"
  with assms(2) show "p" ..
qed

― ‹La demostración detallada es›
lemma ejercicio_42_2:
  assumes "p ∨ q"
          "¬q"
  shows   "p"
using assms(1)
proof (rule disjE)
  assume "p"
  thus "p" by this
next
  assume "q"
  show "p" using assms(2) ‹q› by (rule notE)
qed

― ‹La demostración automática es›
lemma ejercicio_42_3:
  assumes "p ∨ q"
          "¬q"
  shows   "p"
using assms
by auto

-- ----------------------------------------------------
  Ejercicio 42. Demostrar
     p ∨ q, ¬p ⊢ q
-- ----------------------------------------------------

― ‹La demostración estructurada es›
lemma ejercicio_43_1:
  assumes "p ∨ q"
          "¬p"
  shows   "q"
using assms(1)
proof
  assume "p"
  with assms(2) show "q" ..
next
  assume "q"
  thus "q" .
qed

― ‹La demostración detallada es›
lemma ejercicio_43_2:
  assumes "p ∨ q"
          "¬p"
  shows   "q"
using assms(1)
proof (rule disjE)
  assume "p"
  show "q" using assms(2) ‹p› by (rule notE)
next
  assume "q"
  thus "q" by this
qed

― ‹La demostración automática es›
lemma ejercicio_43_3:
  assumes "p ∨ q"
          "¬p"
  shows   "q"
using assms
by auto

-- ----------------------------------------------------
  Ejercicio 44. Demostrar
     p ∨ q ⊢ ¬(¬p ∧ ¬q)
-- ----------------------------------------------------

― ‹La demostración estructurada es›
lemma ejercicio_44_1:
  assumes "p ∨ q"
  shows   "¬(¬p ∧ ¬q)"
proof
  assume "¬p ∧ ¬q"
  note ‹p ∨ q›
  thus "False"
  proof
    assume "p"
    have "¬p" using ‹¬p ∧ ¬q› ..
    thus "False" using ‹p› ..
  next
    assume "q"
    have "¬q" using ‹¬p ∧ ¬q› ..
    thus "False" using ‹q› ..
  qed
qed

― ‹La demostración detallada es›
lemma ejercicio_44_2:
  assumes "p ∨ q"
  shows   "¬(¬p ∧ ¬q)"
proof (rule notI)
  assume "¬p ∧ ¬q"
  note ‹p ∨ q›
  thus "False"
  proof
    assume "p"
    have "¬p" using ‹¬p ∧ ¬q› by (rule conjunct1)
    thus "False" using ‹p› by (rule notE)
  next
    assume "q"
    have "¬q" using ‹¬p ∧ ¬q› by (rule conjunct2)
    thus "False" using ‹q› by (rule notE)
  qed
qed

― ‹La demostración automática es›
lemma ejercicio_44_3:
  assumes "p ∨ q"
  shows   "¬(¬p ∧ ¬q)"
using assms
by auto

-- ----------------------------------------------------
  Ejercicio 45. Demostrar
     p ∧ q ⊢ ¬(¬p ∨ ¬q)
-- ----------------------------------------------------

― ‹La demostración estructurada es›
lemma ejercicio_45_1:
  assumes "p ∧ q"
  shows   "¬(¬p ∨ ¬q)"
proof
  assume "¬p ∨ ¬q"
  thus "False"
  proof
    assume "¬p"
    have "p" using assms ..
    with ‹¬p› show "False" ..
  next
    assume "¬q"
    have "q" using assms ..
    with ‹¬q› show "False" ..
  qed
qed

― ‹La demostración detallada es›
lemma ejercicio_45_2:
  assumes "p ∧ q"
  shows   "¬(¬p ∨ ¬q)"
proof (rule notI)
  assume "¬p ∨ ¬q"
  thus "False"
  proof
    assume "¬p"
    have "p" using assms by (rule conjunct1)
    show "False" using ‹¬p› ‹p› by (rule notE)
  next
    assume "¬q"
    have "q" using assms by (rule conjunct2)
    show "False" using ‹¬q› ‹q› by (rule notE)
  qed
qed

― ‹La demostración automática es›
lemma ejercicio_45_3:
  assumes "p ∧ q"
  shows   "¬(¬p ∨ ¬q)"
using assms
by auto

-- ----------------------------------------------------
  Ejercicio 46. Demostrar
     ¬(p ∨ q) ⊢ ¬p ∧ ¬q
-- ----------------------------------------------------

― ‹La demostración estructurada es›
lemma ejercicio_46_1:
  assumes "¬(p ∨ q)"
  shows   "¬p ∧ ¬q"
proof
  show "¬p"
  proof
    assume "p"
    hence "p ∨ q" ..
    with assms show "False" ..
  qed
next
  show "¬q"
  proof
    assume "q"
    hence "p ∨ q" ..
    with assms show "False" ..
  qed
qed

― ‹La demostración detallada es›
lemma ejercicio_46_2:
  assumes "¬(p ∨ q)"
  shows   "¬p ∧ ¬q"
proof (rule conjI)
  show "¬p"
  proof (rule notI)
    assume "p"
    hence "p ∨ q" by (rule disjI1)
    show "False" using assms ‹p ∨ q› by (rule notE)
  qed
next
  show "¬q"
  proof (rule notI)
    assume "q"
    hence "p ∨ q" by (rule disjI2)
    show "False" using assms ‹p ∨ q› by (rule notE)
  qed
qed

― ‹La demostración automática es›
lemma ejercicio_46_3:
  assumes "¬(p ∨ q)"
  shows   "¬p ∧ ¬q"
using assms
by auto

-- ----------------------------------------------------
  Ejercicio 47. Demostrar
     ¬p ∧ ¬q ⊢ ¬(p ∨ q)
-- ----------------------------------------------------

― ‹La demostración estructurada es›
lemma ejercicio_47_1:
  assumes "¬p ∧ ¬q"
  shows   "¬(p ∨ q)"
proof
  assume "p ∨ q"
  thus False
  proof
    assume "p"
    have "¬p" using assms ..
    thus False using ‹p› ..
  next
    assume "q"
    have "¬q" using assms ..
    thus False using ‹q› ..
  qed
qed

― ‹La demostración detallada es›
lemma ejercicio_47_2:
  assumes "¬p ∧ ¬q"
  shows   "¬(p ∨ q)"
proof (rule notI)
  assume "p ∨ q"
  thus False
  proof (rule disjE)
    assume "p"
    have "¬p" using assms by (rule conjunct1)
    thus False using ‹p› by (rule notE)
  next
    assume "q"
    have "¬q" using assms by (rule conjunct2)
    thus False using ‹q› by (rule notE)
  qed
qed

― ‹La demostración automática es›
lemma ejercicio_47_3:
  assumes "¬p ∧ ¬q"
  shows   "¬(p ∨ q)"
using assms
by auto

-- ----------------------------------------------------
  Ejercicio 48. Demostrar
     ¬p ∨ ¬q ⊢ ¬(p ∧ q)
-- ----------------------------------------------------

― ‹La demostración estructurada es›
lemma ejercicio_48_1:
  assumes "¬p ∨ ¬q"
  shows   "¬(p ∧ q)"
proof
  assume "p ∧ q"
  note ‹¬p ∨ ¬ q›
  thus False
  proof
    assume "¬p"
    have "p" using ‹p ∧ q› ..
    with ‹¬p› show False ..
  next
    assume "¬q"
    have "q" using ‹p ∧ q› ..
    with ‹¬q› show False ..
  qed
qed

― ‹La demostración detallada es›
lemma ejercicio_48_2:
  assumes "¬p ∨ ¬q"
  shows   "¬(p ∧ q)"
proof (rule notI)
  assume "p ∧ q"
  note ‹¬p ∨ ¬ q›
  thus False
  proof (rule disjE)
    assume "¬p"
    have "p" using ‹p ∧ q› by (rule conjunct1)
    show False using ‹¬p› ‹p› by (rule notE)
  next
    assume "¬q"
    have "q" using ‹p ∧ q› by (rule conjunct2)
    show False using ‹¬q› ‹q› by (rule notE)
  qed
qed

― ‹La demostración automática es›
lemma ejercicio_48_3:
  assumes "¬p ∨ ¬q"
  shows   "¬(p ∧ q)"
using assms
by auto

-- ----------------------------------------------------
  Ejercicio 49. Demostrar
     ⊢ ¬(p ∧ ¬p)
-- ----------------------------------------------------

― ‹La demostración estructurada es›
lemma ejercicio_49_1:
  "¬(p ∧ ¬p)"
proof
  assume "p ∧ ¬p"
  hence "p" ..
  have "¬p" using ‹p ∧ ¬p› ..
  thus False using ‹p› ..
qed

― ‹La demostración detallada es›
lemma ejercicio_49_2:
  "¬(p ∧ ¬p)"
proof (rule notI)
  assume "p ∧ ¬p"
  hence "p" by (rule conjunct1)
  have "¬p" using ‹p ∧ ¬p› by (rule conjunct2)
  thus False using ‹p› by (rule notE)
qed

― ‹La demostración automática es›
lemma ejercicio_49_3:
  "¬(p ∧ ¬p)"
by auto

-- ----------------------------------------------------
  Ejercicio 50. Demostrar
     p ∧ ¬p ⊢ q
-- ----------------------------------------------------

― ‹La demostración estructurada es›
lemma ejercicio_50_1:
  assumes "p ∧ ¬p"
  shows   "q"
proof -
  have "p" using assms ..
  have "¬p" using assms ..
  thus "q" using ‹p› ..
qed

― ‹La demostración detallada es›
lemma ejercicio_50_2:
  assumes "p ∧ ¬p"
  shows   "q"
proof -
  have "p" using assms by (rule conjunct1)
  have "¬p" using assms by (rule conjunct2)
  thus "q" using ‹p› by (rule notE)
qed

― ‹La demostración automática es›
lemma ejercicio_50_3:
  assumes "p ∧ ¬p"
  shows   "q"
using assms
by auto

-- ----------------------------------------------------
  Ejercicio 51. Demostrar
     ¬¬p ⊢ p
-- ----------------------------------------------------

― ‹La demostración detallada es›
lemma ejercicio_51_1:
  assumes "¬¬p"
  shows   "p"
using assms
by (rule notnotD)

― ‹La demostración automática es›
lemma ejercicio_51_2:
  assumes "¬¬p"
  shows   "p"
using assms
by auto

-- ----------------------------------------------------
  Ejercicio 52. Demostrar
     ⊢ p ∨ ¬p
-- ----------------------------------------------------

― ‹La demostración estructurada es›
lemma ejercicio_52_1:
  "p ∨ ¬p"
proof -
  have "¬¬p ∨ ¬p" ..
  thus "p ∨ ¬p" by simp
qed

― ‹La demostración detallada es›
lemma ejercicio_52_2:
  "p ∨ ¬p"
proof -
  have "¬¬p ∨ ¬p" by (rule excluded_middle)
  thus "p ∨ ¬p" by simp
qed

― ‹La demostración automática es›
lemma ejercicio_52_3:
  "p ∨ ¬p"
by auto

-- ----------------------------------------------------
  Ejercicio 53. Demostrar
     ⊢ ((p → q) → p) → p
-- ----------------------------------------------------

― ‹La demostración estructurada es›
lemma ejercicio_53_1:
  "((p → q) → p) → p"
proof
  assume "(p → q) → p"
  show "p"
  proof (rule ccontr)
    assume "¬p"
    have "¬(p → q)" using ‹(p → q) → p› ‹¬p› by (rule mt)
    have "p → q"
    proof
      assume "p"
      with ‹¬p› show "q" ..
    qed
    show False using ‹¬(p → q)› ‹p → q› ..
  qed
qed

― ‹La demostración detallada es›
lemma ejercicio_53_2:
  "((p → q) → p) → p"
proof (rule impI)
  assume "(p → q) → p"
  show "p"
  proof (rule ccontr)
    assume "¬p"
    have "¬(p → q)" using ‹(p → q) → p› ‹¬p› by (rule mt)
    have "p → q"
    proof (rule impI)
      assume "p"
      show "q" using ‹¬p› ‹p› by (rule notE)
    qed
    show False using ‹¬(p → q)› ‹p → q› by (rule notE)
  qed
qed

― ‹La demostración automática es›
lemma ejercicio_53_3:
  "((p → q) → p) → p"
by auto

-- ----------------------------------------------------
  Ejercicio 54. Demostrar
     ¬q → ¬p ⊢ p → q
-- ----------------------------------------------------

― ‹La demostración estructurada es›
lemma ejercicio_54_1:
  assumes "¬q → ¬p"
  shows   "p → q"
proof
  assume "p"
  show "q"
  proof (rule ccontr)
    assume "¬q"
    with assms have "¬p" ..
    thus False using ‹p› ..
  qed
qed

― ‹La demostración detallada es›
lemma ejercicio_54_2:
  assumes "¬q → ¬p"
  shows   "p → q"
proof (rule impI)
  assume "p"
  show "q"
  proof (rule ccontr)
    assume "¬q"
    have "¬p" using assms ‹¬q› by (rule mp)
    thus False using ‹p› by (rule notE)
  qed
qed

― ‹La demostración automática es›
lemma ejercicio_54_3:
  assumes "¬q → ¬p"
  shows   "p → q"
using assms
by auto

-- ----------------------------------------------------
  Ejercicio 55. Demostrar
     ¬(¬p ∧ ¬q) ⊢ p ∨ q
-- ----------------------------------------------------

― ‹La demostración estructurada es›
lemma ejercicio_55_1:
  assumes "¬(¬p ∧ ¬q)"
  shows   "p ∨ q"
proof -
  have "¬p ∨ p" ..
  thus "p ∨ q"
  proof
    assume "¬p"
    have "¬q ∨ q" ..
    thus "p ∨ q"
    proof
      assume "¬q"
      with ‹¬p› have "¬p ∧ ¬q" ..
      with assms show "p ∨ q" ..
    next
      assume "q"
      thus "p ∨ q" ..
    qed
  next
    assume "p"
    thus "p ∨ q" ..
  qed
qed

― ‹La demostración detallada es›
lemma ejercicio_55_2:
  assumes "¬(¬p ∧ ¬q)"
  shows   "p ∨ q"
proof -
  have "¬p ∨ p" by (rule excluded_middle)
  thus "p ∨ q"
  proof
    assume "¬p"
    have "¬q ∨ q" by (rule excluded_middle)
    thus "p ∨ q"
    proof
      assume "¬q"
      have "¬p ∧ ¬q" using ‹¬p› ‹¬q› by (rule conjI)
      show "p ∨ q" using assms ‹¬p ∧ ¬q› by (rule notE)
    next
      assume "q"
      thus "p ∨ q" by (rule disjI2)
    qed
  next
    assume "p"
    thus "p ∨ q" by (rule disjI1)
  qed
qed

― ‹La demostración automática es›
lemma ejercicio_55_3:
  assumes "¬(¬p ∧ ¬q)"
  shows   "p ∨ q"
using assms
by auto

-- ----------------------------------------------------
  Ejercicio 56. Demostrar
     ¬(¬p ∨ ¬q) ⊢ p ∧ q
-- ----------------------------------------------------

― ‹La demostración estructurada es›
lemma ejercicio_56_1:
  assumes "¬(¬p ∨ ¬q)"
  shows   "p ∧ q"
proof
  show "p"
  proof (rule ccontr)
    assume "¬p"
    hence "¬p ∨ ¬q" ..
    with assms show False ..
  qed
next
  show "q"
  proof (rule ccontr)
    assume "¬q"
    hence "¬p ∨ ¬q" ..
    with assms show False ..
  qed
qed

― ‹La demostración detallada es›
lemma ejercicio_56_2:
  assumes "¬(¬p ∨ ¬q)"
  shows   "p ∧ q"
proof (rule conjI)
  show "p"
  proof (rule ccontr)
    assume "¬p"
    hence "¬p ∨ ¬q" by (rule disjI1)
    show False using assms ‹¬p ∨ ¬q› by (rule notE)
  qed
next
  show "q"
  proof (rule ccontr)
    assume "¬q"
    hence "¬p ∨ ¬q" by (rule disjI2)
    show False using assms ‹¬p ∨ ¬q› by (rule notE)
  qed
qed

― ‹La demostración automática es›
lemma ejercicio_56_3:
  assumes "¬(¬p ∨ ¬q)"
  shows   "p ∧ q"
using assms
by auto

-- ----------------------------------------------------
  Ejercicio 57. Demostrar
     ¬(p ∧ q) ⊢ ¬p ∨ ¬q
-- ----------------------------------------------------

― ‹La demostración estructurada es›
lemma ejercicio_57_1:
  assumes "¬(p ∧ q)"
  shows   "¬p ∨ ¬q"
proof -
  have "¬p ∨ p" ..
  thus "¬p ∨ ¬q"
  proof
    assume "¬p"
    thus "¬p ∨ ¬q" ..
  next
    assume "p"
    have "¬q ∨ q" ..
    thus "¬p ∨ ¬q"
    proof
      assume "¬q"
      thus "¬p ∨ ¬q" ..
    next
      assume "q"
      with ‹p› have "p ∧ q" ..
      with assms show "¬p ∨ ¬q" ..
    qed
  qed
qed

― ‹La demostración detallada es›
lemma ejercicio_57_2:
  assumes "¬(p ∧ q)"
  shows   "¬p ∨ ¬q"
proof -
  have "¬p ∨ p" by (rule excluded_middle)
  thus "¬p ∨ ¬q"
  proof (rule disjE)
    assume "¬p"
    thus "¬p ∨ ¬q" by (rule disjI1)
  next
    assume "p"
    have "¬q ∨ q" by (rule excluded_middle)
    thus "¬p ∨ ¬q"
    proof
      assume "¬q"
      thus "¬p ∨ ¬q" by (rule disjI2)
    next
      assume "q"
      have "p ∧ q" using ‹p› ‹q› by (rule conjI)
      show "¬p ∨ ¬q" using assms ‹p ∧ q› by (rule notE)
    qed
  qed
qed

― ‹La demostración automática es›
lemma ejercicio_57_3:
  assumes "¬(p ∧ q)"
  shows   "¬p ∨ ¬q"
using assms
by auto

-- ----------------------------------------------------
  Ejercicio 58. Demostrar
     ⊢ (p → q) ∨ (q → p)
-- ----------------------------------------------------

― ‹La demostración estructurada es›
lemma ejercicio_58_1:
  "(p → q) ∨ (q → p)"
proof -
  have "¬p ∨ p" ..
  thus "(p → q) ∨ (q → p)"
  proof
    assume "¬p"
    have "p → q"
    proof
      assume "p"
      with ‹¬p› show "q" ..
    qed
    thus "(p → q) ∨ (q → p)" ..
  next
    assume "p"
    have "q → p"
    proof
      assume "q"
      show "p" using ‹p› .
    qed
    thus "(p → q) ∨ (q → p)" ..
  qed
qed

― ‹La demostración detallada es›
lemma ejercicio_58_2:
  "(p → q) ∨ (q → p)"
proof -
  have "¬p ∨ p" by (rule excluded_middle)
  thus "(p → q) ∨ (q → p)"
  proof
    assume "¬p"
    have "p → q"
    proof (rule impI)
      assume "p"
      show "q" using ‹¬p› ‹p› by (rule notE)
    qed
    thus "(p → q) ∨ (q → p)" by (rule disjI1)
  next
    assume "p"
    have "q → p"
    proof
      assume "q"
      show "p" using ‹p› by this
    qed
    thus "(p → q) ∨ (q → p)" by (rule disjI2)
  qed
qed

― ‹La demostración automática es›
lemma ejercicio_58_3:
  "(p → q) ∨ (q → p)"
by auto

end
-/
