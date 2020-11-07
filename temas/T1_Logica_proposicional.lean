-- Tema 1: Lógica proposicional
-- ============================

import tactic            
variables (P Q R : Prop)   

-- * Reglas del condicional
-- ========================

-- ** Regla de eliminación del condicional
-- =======================================

-- ----------------------------------------------------
-- Ej. 1. Demostrar que 
--    (P → Q), P ⊢ Q. 
-- ----------------------------------------------------

-- 1ª demostración
example  
  (h1 : P → Q) 
  (h2 : P) 
  : Q :=
begin
  apply h1,
  exact h2,
end 

-- 2ª demostración
example  
  (h1 : P → Q) 
  (h2 : P) 
  : Q :=
begin
  exact h1 h2,
end 

-- 3ª demostración
example  
  (h1 : P → Q) 
  (h2 : P) 
  : Q :=
by exact h1 h2

-- 4ª demostración
example  
  (h1 : P → Q) 
  (h2 : P) 
  : Q :=
h1 h2

-- 5ª demostración
example  
  (h1 : P → Q) 
  (h2 : P) 
  : Q :=
by tauto

-- 6ª demostración
example  
  (h1 : P → Q) 
  (h2 : P) 
  : Q :=
by finish

-- 7ª demostración
example  
  (h1 : P → Q) 
  (h2 : P) 
  : Q :=
by solve_by_elim

-- ----------------------------------------------------
-- Ej. 2. Demostrar que
--    P, P → Q, P → (Q → R) ⊢ R
-- ----------------------------------------------------

-- 1ª demostración
example
  (h1 : P)
  (h2 : P → Q)
  (h3 : P → (Q → R))
  : R :=
have h4 : Q,
  from h2 h1,
have h5 : Q → R,
  from h3 h1,
show R,
  from h5 h4    

-- 2ª demostración
example
  (h1 : P)
  (h2 : P → Q)
  (h3 : P → (Q → R))
  : R :=
have h4 : Q     := h2 h1,
have h5 : Q → R := h3 h1,
show R, from h5 h4    

-- 3ª demostración
example
  (h1 : P)
  (h2 : P → Q)
  (h3 : P → (Q → R))
  : R :=
show R, from (h3 h1) (h2 h1)    

-- 4ª demostración
example
  (h1 : P)
  (h2 : P → Q)
  (h3 : P → (Q → R))
  : R :=
(h3 h1) (h2 h1)    

-- 5ª demostración
example
  (h1 : P)
  (h2 : P → Q)
  (h3 : P → (Q → R))
  : R :=
by finish

-- ** Regla de introducción del condicional
-- ========================================

-- ----------------------------------------------------
-- Ej. 3. Demostrar que
--    P → P
-- ----------------------------------------------------

-- 1ª demostración
example : P → P :=
assume h : P, 
show P, from h

-- 2ª demostración
example : P → P :=
assume : P, 
show P, from this

-- 3ª demostración
example : P → P :=
assume : P, 
show P, from ‹P›

-- 4ª demostración
example : P → P :=
assume h : P, h

-- 5ª demostración
example : P → P :=
λ h, h

-- 6ª demostración
example : P → P :=
id

-- 7ª demostración
example : P → P :=
begin
  intro h,
  exact h,
end

-- 8ª demostración
example : P → P :=
begin
  intro,
  exact ‹P›,
end

-- 9ª demostración
example : P → P :=
begin
  intro h,
  assumption,
end

-- 10ª demostración
example : P → P :=
begin
  intro,
  assumption,
end

-- 11ª demostración
example : P → P :=
by tauto

-- 12ª demostración
example : P → P :=
by finish

-- 13ª demostración
example : P → P :=
by simp

-- ----------------------------------------------------
-- Ej. 4. Demostrar
--    P → (Q → P)
-- ----------------------------------------------------

-- 1ª demostración
example : P → (Q → P) :=
assume (h1 : P),
show Q → P, from 
  ( assume h2 : Q,
    show P, from h1)

-- 2ª demostración
example : P → (Q → P) :=
assume (h1 : P),
show Q → P, from 
  ( assume h2 : Q, h1)    

-- 3ª demostración
example : P → (Q → P) :=
assume (h1 : P),
show Q → P, from 
  ( λ h2, h1)      

-- 4ª demostración
example : P → (Q → P) :=
assume (h1 : P), (λ h2, h1)        

-- 5ª demostración
example : P → (Q → P) :=
λ h1, λ h2, h1        

-- 6ª demostración
example : P → (Q → P) :=
λ h1 h2, h1        

-- 7ª demostración
example : P → (Q → P) :=
λ h _, h        

-- 8ª demostración
example : P → (Q → P) :=
imp_intro

-- 9ª demostración
example : P → (Q → P) :=
begin
  intro h1,
  intro h2,
  exact h1,
end 

-- 10ª demostración
example : P → (Q → P) :=
begin
  intros h1 h2,
  exact h1,
end 

-- 6ª demostración
example : P → (Q → P) :=
λ h1 h2, h1

-- 11ª demostración
example : P → (Q → P) :=
by tauto

-- 12ª demostración
example : P → (Q → P) :=
by finish

-- ----------------------------------------------------
-- Ej. 5. Demostrar que
--    P → Q, Q → R ⊢ P → R
-- ----------------------------------------------------

-- 1º demostración
example 
  (h1 : P → Q)
  (h2 : Q → R)
  : P → R :=
assume h : P,
have h3 : Q,
  from h1 h,
show R, 
  from h2 h3

-- 2º demostración
example 
  (h1 : P → Q)
  (h2 : Q → R)
  : P → R :=
assume h : P,
have h3 : Q := h1 h,
show R, 
  from h2 h3

-- 3º demostración
example 
  (h1 : P → Q)
  (h2 : Q → R)
  : P → R :=
assume h : P,
show R, 
  from h2 (h1 h)

-- 4º demostración
example 
  (h1 : P → Q)
  (h2 : Q → R)
  : P → R :=
assume h : P, h2 (h1 h)

-- 5º demostración
example 
  (h1 : P → Q)
  (h2 : Q → R)
  : P → R :=
λ h, h2 (h1 h)

-- 6º demostración
example 
  (h1 : P → Q)
  (h2 : Q → R)
  : P → R :=
h2 ∘ h1

-- 7º demostración
example 
  (h1 : P → Q)
  (h2 : Q → R)
  : P → R :=
begin
  intro h,
  apply h2, 
  apply h1,
  exact h,
end

-- 8º demostración
example 
  (h1 : P → Q)
  (h2 : Q → R)
  : P → R :=
begin
  intro h,
  apply h2, 
  exact h1 h,
end

-- 9º demostración
example 
  (h1 : P → Q)
  (h2 : Q → R)
  : P → R :=
begin
  intro h,
  exact h2 (h1 h),
end

-- 10º demostración
example 
  (h1 : P → Q)
  (h2 : Q → R)
  : P → R :=
λ h, h2 (h1 h)

-- 11º demostración
example 
  (h1 : P → Q)
  (h2 : Q → R)
  : P → R :=
h2 ∘ h1

-- 12º demostración
example 
  (h1 : P → Q)
  (h2 : Q → R)
  : P → R :=
by tauto

-- 13º demostración
example 
  (h1 : P → Q)
  (h2 : Q → R)
  : P → R :=
by finish

-- * Reglas de la conjunción 
-- =========================

-- ----------------------------------------------------
-- Ej. 6. Demostrar que
--    P ∧ Q, R ⊢ Q ∧ R
-- ----------------------------------------------------

-- 1ª demostración
-- ===============

example  
  (hPQ : P ∧ Q)
  (hR : R)
  : Q ∧ R :=
have hQ : Q, 
  from and.right hPQ,
show Q ∧ R,  
  from and.intro hQ hR

-- 2ª demostración
-- ===============

example  
  (hPQ : P ∧ Q)
  (hR : R)
  : Q ∧ R :=
have hQ : Q, 
  from hPQ.right,
show Q ∧ R,  
  from ⟨hQ, hR⟩

-- 3ª demostración
-- ===============

example  
  (hPQ : P ∧ Q)
  (hR : R)
  : Q ∧ R :=
have hQ : Q, 
  from hPQ.2,
show Q ∧ R,  
  from ⟨hQ, hR⟩

-- 4ª demostración
-- ===============

example  
  (hPQ : P ∧ Q)
  (hR : R)
  : Q ∧ R :=
have hQ : Q :=
  hPQ.2,
show Q ∧ R,  
  from ⟨hQ, hR⟩

-- 5ª demostración
-- ===============

example  
  (hPQ : P ∧ Q)
  (hR : R)
  : Q ∧ R :=
show Q ∧ R,  
  from ⟨hPQ.2, hR⟩

-- 6ª demostración
-- ===============

example  
  (hPQ : P ∧ Q)
  (hR : R)
  : Q ∧ R :=
⟨hPQ.2, hR⟩

-- 7ª demostración
-- ===============

example  
  (hPQ : P ∧ Q)
  (hR : R)
  : Q ∧ R :=
match hPQ with ⟨hP, hQ⟩ :=
  and.intro hQ hR
end

-- 8ª demostración
-- ===============

example  
  (hPQ : P ∧ Q)
  (hR : R)
  : Q ∧ R :=
begin
  split,
  { cases hPQ with hP hQ,
    clear hP,
    exact hQ, },
  { exact hR, },
end

-- 9ª demostración
-- ===============

example  
  (hPQ : P ∧ Q)
  (hR : R)
  : Q ∧ R :=
begin
  split,
  { cases hPQ,
    assumption, },
  { assumption, },
end

-- 10ª demostración
-- ===============

example  
  (hPQ : P ∧ Q)
  (hR : R)
  : Q ∧ R :=
begin
  constructor,
  { cases hPQ,
    assumption, },
  { assumption, },
end

-- 11ª demostración
-- ===============

example  
  (hPQ : P ∧ Q)
  (hR : R)
  : Q ∧ R :=
by tauto

-- 12ª demostración
-- ===============

example  
  (hPQ : P ∧ Q)
  (hR : R)
  : Q ∧ R :=
by finish

-- ----------------------------------------------------
-- Ej. 7. Demostrar que
--    P ∧ Q → Q ∧ P
-- ----------------------------------------------------

-- 1ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
assume h : P ∧ Q,
have hP : P, 
  from and.left h,
have hQ : Q, 
  from and.right h,
show Q ∧ P,  
  from and.intro hQ hP

-- 2ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
assume h : P ∧ Q,
have hP : P, 
  from h.left,
have hQ : Q, 
  from h.right,
show Q ∧ P,  
  from ⟨hQ, hP⟩

-- 3ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
assume h : P ∧ Q,
have hP : P, 
  from h.1,
have hQ : Q, 
  from h.2,
show Q ∧ P,  
  from ⟨hQ, hP⟩

-- 4ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
assume h : P ∧ Q,
have hP : P := h.1,
have hQ : Q := h.2,
show Q ∧ P,  
  from ⟨hQ, hP⟩

-- 5ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
assume h : P ∧ Q,
show Q ∧ P,  
  from ⟨h.2, h.1⟩

-- 6ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
assume h : P ∧ Q, ⟨h.2, h.1⟩

-- 7ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
λ h, ⟨h.2, h.1⟩

-- 8ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
and.comm.mp

-- 9ª demostración
-- =============== 

example : P ∧ Q → Q ∧ P :=
begin
  intro h,
  cases h with hP hQ,
  split,
  { exact hQ, },
  { exact hP, },
end

-- 10ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
begin
  rintro ⟨hP, hQ⟩,
  exact ⟨hQ, hP⟩,
end

-- 11ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
λ ⟨hP, hQ⟩, ⟨hQ, hP⟩

-- 12ª demostración
-- ===============

example : P ∧ Q → Q ∧ P:=
by tauto

-- 13ª demostración
-- ===============

example : P ∧ Q → Q ∧ P :=
by finish

-- * Reglas de la negación
-- =======================

-- ** Eliminación del falso
-- ========================

-- ----------------------------------------------------
-- Ej. 8. Demostrar que
--    ⊥ ⊢ P
-- ----------------------------------------------------

-- 1ª demostración
example 
  (h : false)
  : P :=
false.elim h

-- 2ª demostración
example 
  (h : false)
  : P :=
false.rec P h

-- 3ª demostración
example 
  (h : false)
  : P :=
by tauto

-- 4ª demostración
example 
  (h : false)
  : P :=
by cases h

-- 5ª demostración
example 
  (h : false)
  : P :=
by finish

-- 6ª demostración
example 
  (h : false)
  : P :=
by solve_by_elim

-- ** Definición de la negación
-- ============================

-- ¬P ≡ (P → false)  

-- #reduce ¬P 

-- ** Eliminación de la negación
-- =============================

-- ----------------------------------------------------
-- Ej. 9. Demostrar que
--    P, ¬P ⊢ ⊥
-- ----------------------------------------------------

-- 1ª demostración
example
  (h1: P)
  (h2: ¬P)
  : false :=
not.elim h2 h1

-- 2ª demostración
example
  (h1: P)
  (h2: ¬P)
  : false :=
h2 h1

-- ** Introducción de la negación
-- ==============================

-- ----------------------------------------------------
-- Ej. 10. Demostrar 
--    ¬(P ∧ ¬P)
-- ----------------------------------------------------

-- 1ª demostración
example : ¬(P ∧ ¬P) :=
not.intro 
  ( assume h : P ∧ ¬P,
    have h1 : P  := h.1,
    have h2 : ¬P := h.2,
    show false, from h2 h1 )
  
-- 2ª demostración
example : ¬(P ∧ ¬P) :=
not.intro 
  ( assume h : P ∧ ¬P,
    show false, from h.2 h.1 )
  
-- 3ª demostración
example : ¬(P ∧ ¬P) :=
not.intro 
  ( assume h : P ∧ ¬P, h.2 h.1 )
  
-- 4ª demostración
example : ¬(P ∧ ¬P) :=
not.intro (λ h, h.2 h.1)
  
-- 5ª demostración
example : ¬(P ∧ ¬P) :=
begin
  intro h,
  cases h with h1 h2,
  apply h2,
  exact h1,
end  

-- 6ª demostración
example : ¬(P ∧ ¬P) :=
begin
  rintro ⟨h1, h2⟩,
  exact h2 h1,
end  

-- 7ª demostración
example : ¬(P ∧ ¬P) :=
λ ⟨h1, h2⟩, h2 h1

-- 8ª demostración
example : ¬(P ∧ ¬P) :=
(and_not_self P).mp

-- 9ª demostración
example : ¬(P ∧ ¬P) :=
by tauto

-- 10ª demostración
example : ¬(P ∧ ¬P) :=
by finish

-- 11ª demostración
example : ¬(P ∧ ¬P) :=
by simp 

-- ----------------------------------------------------
-- Ej. 11. Demostrar
--    P → Q, P → ¬Q ⊢ ¬P
-- ----------------------------------------------------

-- 1ª demostración
example
  (h1 : P → Q)
  (h2 : P → ¬Q)
  : ¬P :=
assume h : P,
have h4 : Q,
  from h1 h,
have h5 : ¬Q,
  from h2 h,  
show false, 
  from h5 h4

-- 2ª demostración
example
  (h1 : P → Q)
  (h2 : P → ¬Q)
  : ¬P :=
assume h : P,
have h4 : Q  := h1 h,
have h5 : ¬Q := h2 h,  
show false, 
  from h5 h4

-- 3ª demostración
example
  (h1 : P → Q)
  (h2 : P → ¬Q)
  : ¬P :=
assume h : P,
show false, 
  from (h2 h) (h1 h)

-- 4ª demostración
example
  (h1 : P → Q)
  (h2 : P → ¬Q)
  : ¬P :=
assume h : P, (h2 h) (h1 h)

-- 5ª demostración
example
  (h1 : P → Q)
  (h2 : P → ¬Q)
  : ¬P :=
λ h, (h2 h) (h1 h)

-- 6ª demostración
example
  (h1 : P → Q)
  (h2 : P → ¬Q)
  : ¬P :=
begin
  intro h,
  have h3 : ¬Q := h2 h,
  apply h3,
  apply h1,
  exact h,
end

-- 7ª demostración
example
  (h1 : P → Q)
  (h2 : P → ¬Q)
  : ¬P :=
begin
  intro h,
  have h3 : ¬Q := h2 h,
  apply h3,
  exact h1 h,
end

-- 8ª demostración
example
  (h1 : P → Q)
  (h2 : P → ¬Q)
  : ¬P :=
begin
  intro h,
  have h3 : ¬Q := h2 h,
  exact h3 (h1 h),
end

-- 9ª demostración
example
  (h1 : P → Q)
  (h2 : P → ¬Q)
  : ¬P :=
begin
  intro h,
  exact (h2 h) (h1 h),
end

-- 10ª demostración
example
  (h1 : P → Q)
  (h2 : P → ¬Q)
  : ¬P :=
λ h, (h2 h) (h1 h)

-- 11ª demostración
example
  (h1 : P → Q)
  (h2 : P → ¬Q)
  : ¬P :=
by finish

-- ----------------------------------------------------
-- Ej. 12. Demostrar el modus tollens
--    P → Q, ¬Q ⊢ ¬P
-- ----------------------------------------------------

-- 1ª demostración
example 
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
assume h3 : P,
have h4 : Q,
  from h1 h3,
show false, 
  from h2 h4

-- 2ª demostración
example 
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
assume h3 : P,
have h4 : Q := h1 h3,
show false, 
  from h2 h4

-- 3ª demostración
example 
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
assume h3 : P,
show false, 
  from h2 (h1 h3)

-- 4ª demostración
example 
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
assume h3 : P, h2 (h1 h3)

-- 5ª demostración
example 
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
λ h, h2 (h1 h)

-- 6ª demostración
example 
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
h2 ∘ h1

-- 7ª demostración
example 
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
mt h1 h2

-- 8ª demostración
example 
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
by tauto

-- 9ª demostración
example 
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
by finish

-- 10ª demostración
example 
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
begin
  intro h,
  apply h2,
  apply h1,
  exact h,
end

-- 11ª demostración
example 
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
begin
  intro h,
  exact h2 (h1 h),
end

-- 12ª demostración
example 
  (h1 : P → Q)
  (h2 : ¬Q)
  : ¬P :=
λ h, h2 (h1 h)

-- ----------------------------------------------------
-- Ej. 13. Demostrar
--    P → (Q → R), P, ¬R ⊢ ¬Q 
-- ----------------------------------------------------

-- 1ª demostración
example 
  (h1 : P → (Q → R)) 
  (h2 : P)
  (h3 : ¬R)
  : ¬Q :=
have h4 : Q → R,
  from h1 h2,
show ¬Q,
  from mt h4 h3  

-- 2ª demostración
example 
  (h1 : P → (Q → R)) 
  (h2 : P)
  (h3 : ¬R)
  : ¬Q :=
have h4 : Q → R := h1 h2,
show ¬Q,
  from mt h4 h3  

-- 3ª demostración
example 
  (h1 : P → (Q → R)) 
  (h2 : P)
  (h3 : ¬R)
  : ¬Q :=
show ¬Q,
  from mt (h1 h2) h3  

-- 4ª demostración
example 
  (h1 : P → (Q → R)) 
  (h2 : P)
  (h3 : ¬R)
  : ¬Q :=
mt (h1 h2) h3

-- 5ª demostración
example 
  (h1 : P → (Q → R)) 
  (h2 : P)
  (h3 : ¬R)
  : ¬Q :=
begin
  intro h4,
  apply h3,
  apply (h1 h2),
  exact h4,
end

-- 6ª demostración
example 
  (h1 : P → (Q → R)) 
  (h2 : P)
  (h3 : ¬R)
  : ¬Q :=
begin
  intro h4,
  apply h3,
  exact (h1 h2) h4,
end

-- 7ª demostración
example 
  (h1 : P → (Q → R)) 
  (h2 : P)
  (h3 : ¬R)
  : ¬Q :=
begin
  intro h4,
  exact h3 ((h1 h2) h4),
end

-- 8ª demostración
example 
  (h1 : P → (Q → R)) 
  (h2 : P)
  (h3 : ¬R)
  : ¬Q :=
λ h4, h3 ((h1 h2) h4)

-- 9ª demostración
example 
  (h1 : P → (Q → R)) 
  (h2 : P)
  (h3 : ¬R)
  : ¬Q :=
by finish

-- ----------------------------------------------------
-- Ej. 14. Demostrar
--    P → Q ⊢ ¬Q → ¬P
-- ----------------------------------------------------

-- 1ª demostración
example
  (h1 : P → Q)
  : ¬Q → ¬P :=
assume h2 : ¬Q,
show ¬P,
  from mt h1 h2

-- 2ª demostración
example
  (h1 : P → Q)
  : ¬Q → ¬P :=
assume h2 : ¬Q, mt h1 h2

-- 3ª demostración
example
  (h1 : P → Q)
  : ¬Q → ¬P :=
λ h2, mt h1 h2

-- 4ª demostración
example
  (h1 : P → Q)
  : ¬Q → ¬P :=
mt h1

-- 5ª demostración
example
  (h1 : P → Q)
  : ¬Q → ¬P :=
begin
  intro h2,
  exact mt h1 h2,
end

-- 6ª demostración
example
  (h1 : P → Q)
  : ¬Q → ¬P :=
begin
  intro h2,
  intro h3,
  apply h2,
  apply h1,
  exact h3,
end

-- 7ª demostración
example
  (h1 : P → Q)
  : ¬Q → ¬P :=
begin
  intro h2,
  intro h3,
  apply h2,
  exact h1 h3,
end

-- 8ª demostración
example
  (h1 : P → Q)
  : ¬Q → ¬P :=
begin
  intro h2,
  intro h3,
  exact h2 (h1 h3),
end

-- 9ª demostración
example
  (h1 : P → Q)
  : ¬Q → ¬P :=
begin
  intros h2 h3,
  exact h2 (h1 h3),
end

-- 10ª demostración
example
  (h1 : P → Q)
  : ¬Q → ¬P :=
λ h2 h3, h2 (h1 h3)

-- 11ª demostración
example
  (h1 : P → Q)
  : ¬Q → ¬P :=
by tauto

-- 12ª demostración
example
  (h1 : P → Q)
  : ¬Q → ¬P :=
by finish

-- * Regla de introducción de la doble negación
-- ============================================

-- ----------------------------------------------------
-- Ej. 15. Demostrar
--    P ⊢ ¬¬P
-- ----------------------------------------------------

-- 1ª demostración
example
  (h1 : P)
  : ¬¬P :=
not.intro 
  ( assume h2: ¬P,
    show false, 
      from h2 h1)
  
-- 2ª demostración
example
  (h1 : P)
  : ¬¬P :=
assume h2: ¬P,
show false,
  from h2 h1

-- 3ª demostración
example
  (h1 : P)
  : ¬¬P :=
assume h2: ¬P, h2 h1

-- 4ª demostración
example
  (h1 : P)
  : ¬¬P :=
λ h2, h2 h1

-- 5ª demostración
example
  (h1 : P)
  : ¬¬P :=
not_not.mpr h1

-- 6ª demostración
example
  (h1 : P)
  : ¬¬P :=
not_not_intro h1

-- 7ª demostración
example
  (h1 : P)
  : ¬¬P :=
begin
  intro h2,
  exact h2 h1,
end

-- 8ª demostración
example
  (h1 : P)
  : ¬¬P :=
by tauto

-- 9ª demostración
example
  (h1 : P)
  : ¬¬P :=
by finish

-- ----------------------------------------------------
-- Ej. 16. Demostrar
--    ¬Q → ¬P ⊢ P → ¬¬Q
-- ----------------------------------------------------

-- 1ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
assume h2 : P,
have h3 : ¬¬P,
  from not_not_intro h2,
show ¬¬Q, 
  from mt h1 h3

-- 2ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
assume h2 : P,
have h3 : ¬¬P := not_not_intro h2,
show ¬¬Q, 
  from mt h1 h3

-- 3ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
assume h2 : P,
show ¬¬Q, 
  from mt h1 (not_not_intro h2)

-- 4ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
assume h2 : P, mt h1 (not_not_intro h2)

-- 5ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
λ h2, mt h1 (not_not_intro h2)

-- 6ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
imp_not_comm.mp h1

-- 7ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
begin
  intro h2,
  apply mt h1,
  apply not_not_intro,
  exact h2,
end

-- 8ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
begin
  intro h2,
  apply mt h1,
  exact not_not_intro h2,
end

-- 9ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
begin
  intro h2,
  exact mt h1 (not_not_intro h2),
end

-- 10ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
λ h2, mt h1 (not_not_intro h2)

-- 11ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
begin
  intro h2,
  intro h3,
  have h4 : ¬P := h1 h3,
  exact h4 h2,
end

-- 12ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
begin
  intros h2 h3,
  exact (h1 h3) h2,
end

-- 13ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
λ h2 h3, (h1 h3) h2

-- 14ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
by tauto

-- 15ª demostración
example
  (h1 : ¬Q → ¬P)
  : P → ¬¬Q :=
by finish

-- * Reglas de la disyunción
-- =========================

-- ** Reglas de introducción de la disyunción
-- ==========================================

-- ----------------------------------------------------
-- Ej. 17. Demostrar
--    P ⊢ P ∨ Q
-- ----------------------------------------------------

-- 1ª demostración 
example 
  (h : P)
  : P ∨ Q :=
or.intro_left Q h

-- 2ª demostración 
example 
  (h : P)
  : P ∨ Q :=
or.inl h

-- 3ª demostración 
example 
  (h : P)
  : P ∨ Q :=
by tauto

-- 4ª demostración 
example 
  (h : P)
  : P ∨ Q :=
by finish

-- ----------------------------------------------------
-- Ej. 18. Demostrar
--    P ∧ Q ⊢ P ∨ R
-- ----------------------------------------------------

-- 1ª demostración
example 
  (h1 : P ∧ Q)
  : P ∨ R :=
have h2 : P,
  from and.elim_left h1,
show P ∨ R,
  from or.inl h2

-- 2ª demostración
example 
  (h1 : P ∧ Q)
  : P ∨ R :=
have h2 : P,
  from h1.1,
show P ∨ R,
  from or.inl h2

-- 3ª demostración
example 
  (h1 : P ∧ Q)
  : P ∨ R :=
have h2 : P := h1.1,
show P ∨ R,
  from or.inl h2

-- 4ª demostración
example 
  (h1 : P ∧ Q)
  : P ∨ R :=
show P ∨ R,
  from or.inl h1.1

-- 5ª demostración
example 
  (h1 : P ∧ Q)
  : P ∨ R :=
or.inl h1.1

-- 6ª demostración
example 
  (h1 : P ∧ Q)
  : P ∨ R :=
by tauto

-- 7ª demostración
example 
  (h1 : P ∧ Q)
  : P ∨ R :=
by finish

-- ----------------------------------------------------
-- Ej. 19. Demostrar
--    Q ⊢ P ∨ Q
-- ----------------------------------------------------

-- 1ª demostración 
example 
  (h : Q)
  : P ∨ Q :=
or.intro_right P h

-- 2ª demostración 
example 
  (h : Q)
  : P ∨ Q :=
or.inr h

-- 3ª demostración 
example 
  (h : Q)
  : P ∨ Q :=
by tauto

-- 4ª demostración 
example 
  (h : Q)
  : P ∨ Q :=
by finish

-- ----------------------------------------------------
-- Ej. 20. Demostrar
--    P ∧ Q ⊢ P ∨ R
-- ----------------------------------------------------

-- 1ª demostración
example 
  (h1 : P ∧ Q)
  : R ∨ Q :=
have h2 : Q,
  from and.elim_right h1,
show R ∨ Q,
  from or.inr h2

-- 2ª demostración
example 
  (h1 : P ∧ Q)
  : R ∨ Q :=
have h2 : Q,
  from h1.2,
show R ∨ Q,
  from or.inr h2

-- 3ª demostración
example 
  (h1 : P ∧ Q)
  : R ∨ Q :=
have h2 : Q := h1.2,
show R ∨ Q,
  from or.inr h2

-- 4ª demostración
example 
  (h1 : P ∧ Q)
  : R ∨ Q :=
show R ∨ Q,
  from or.inr h1.2

-- 5ª demostración
example 
  (h1 : P ∧ Q)
  : R ∨ Q :=
or.inr h1.2

-- 6ª demostración
example 
  (h1 : P ∧ Q)
  : R ∨ Q :=
by tauto

-- 7ª demostración
example 
  (h1 : P ∧ Q)
  : R ∨ Q :=
by finish

-- ** Regla de eliminación de la disyunción
-- ========================================

-- ----------------------------------------------------
-- Ej. 21. Demostrar
--    P ∨ Q, P → R, Q → R ⊢ R
-- ----------------------------------------------------

-- 1ª demostración
example
  (h1 : P ∨ Q)
  (h2 : P → R) 
  (h3 : Q → R)
  : R :=
or.elim h1 h2 h3

-- 2ª demostración
example
  (h1 : P ∨ Q)
  (h2 : P → R) 
  (h3 : Q → R)
  : R :=
h1.elim h2 h3

-- 3ª demostración
example
  (h1 : P ∨ Q)
  (h2 : P → R) 
  (h3 : Q → R)
  : R :=
or.rec h2 h3 h1

-- 4ª demostración
example
  (h1 : P ∨ Q)
  (h2 : P → R) 
  (h3 : Q → R)
  : R :=
begin
  cases h1 with hP hQ,
  { exact h2 hP, },
  { exact h3 hQ, },
end

-- 5ª demostración
example
  (h1 : P ∨ Q)
  (h2 : P → R) 
  (h3 : Q → R)
  : R :=
by tauto

-- 6ª demostración
example
  (h1 : P ∨ Q)
  (h2 : P → R) 
  (h3 : Q → R)
  : R :=
by finish


