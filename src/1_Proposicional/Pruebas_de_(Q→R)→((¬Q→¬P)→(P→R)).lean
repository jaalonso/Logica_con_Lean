-- Pruebas de (Q → R) → ((¬Q → ¬P) → (P → R))
-- ==========================================

-- Ej. 1. Demostrar
--    (Q → R) → ((¬Q → ¬P) → (P → R))

import tactic

variables (P Q R : Prop)

-- 1ª demostración
example :
  (Q → R) → ((¬Q → ¬P) → (P → R)) :=
assume h1 : Q → R,
show (¬Q → ¬P) → (P → R), from
  ( assume h2 : ¬Q → ¬P,
    show P → R, from
      ( assume h3 : P,
        have h4 : ¬¬P, from not_not_intro h3,
        have h5 : ¬¬Q, from mt h2 h4,
        have h6 : Q,   from not_not.mp h5,
        show R, from h1 h6))
  
-- 2ª demostración
example :
  (Q → R) → ((¬Q → ¬P) → (P → R)) :=
assume h1 : Q → R,
show (¬Q → ¬P) → (P → R), from
  ( assume h2 : ¬Q → ¬P,
    show P → R, from
      ( assume h3 : P,
        have h4 : ¬¬P, from not_not_intro h3,
        have h5 : ¬¬Q, from mt h2 h4,
        have h6 : Q,   from not_not.mp h5,
        h1 h6))

-- 3ª demostración
example :
  (Q → R) → ((¬Q → ¬P) → (P → R)) :=
assume h1 : Q → R,
show (¬Q → ¬P) → (P → R), from
  ( assume h2 : ¬Q → ¬P,
    show P → R, from
      ( assume h3 : P,
        have h4 : ¬¬P, from not_not_intro h3,
        have h5 : ¬¬Q, from mt h2 h4,
        h1 (not_not.mp h5)))

-- 4ª demostración
example :
  (Q → R) → ((¬Q → ¬P) → (P → R)) :=
assume h1 : Q → R,
show (¬Q → ¬P) → (P → R), from
  ( assume h2 : ¬Q → ¬P,
    show P → R, from
      ( assume h3 : P,
        have h4 : ¬¬P, from not_not_intro h3,
        h1 (not_not.mp (mt h2 h4))))

-- 5ª demostración
example :
  (Q → R) → ((¬Q → ¬P) → (P → R)) :=
assume h1 : Q → R,
show (¬Q → ¬P) → (P → R), from
  ( assume h2 : ¬Q → ¬P,
    show P → R, from
      ( assume h3 : P,
        h1 (not_not.mp (mt h2 (not_not_intro h3)))))

-- 6ª demostración
example :
  (Q → R) → ((¬Q → ¬P) → (P → R)) :=
assume h1 : Q → R,
show (¬Q → ¬P) → (P → R), from
  ( assume h2 : ¬Q → ¬P,
    show P → R, from
      (λh3, h1 (not_not.mp (mt h2 (not_not_intro h3)))))

-- 7ª demostración
example :
  (Q → R) → ((¬Q → ¬P) → (P → R)) :=
assume h1 : Q → R,
show (¬Q → ¬P) → (P → R), from
  ( assume h2 : ¬Q → ¬P,
    (λh3, h1 (not_not.mp (mt h2 (not_not_intro h3)))))

-- 8ª demostración
example :
  (Q → R) → ((¬Q → ¬P) → (P → R)) :=
assume h1 : Q → R,
show (¬Q → ¬P) → (P → R), from
  ( λh2, 
    (λh3, h1 (not_not.mp (mt h2 (not_not_intro h3)))))

-- 9ª demostración
example :
  (Q → R) → ((¬Q → ¬P) → (P → R)) :=
assume h1 : Q → R,
(λ h2 h3, h1 (not_not.mp (mt h2 (not_not_intro h3))))

-- 10ª demostración
example :
  (Q → R) → ((¬Q → ¬P) → (P → R)) :=
λ h1 h2 h3, h1 (not_not.mp (mt h2 (not_not_intro h3)))

-- 11ª demostración
example :
  (Q → R) → ((¬Q → ¬P) → (P → R)) :=
begin
  intro h1,
  intro h2,
  intro h3,
  apply h1,
  apply not_not.mp,
  apply mt h2,
  exact not_not_intro h3,
end

-- 12ª demostración
example :
  (Q → R) → ((¬Q → ¬P) → (P → R)) :=
begin
  intros h1 h2 h3,
  apply h1,
  apply not_not.mp,
  apply mt h2,
  exact not_not_intro h3,
end

-- 13ª demostración
example :
  (Q → R) → ((¬Q → ¬P) → (P → R)) :=
begin
  intros h1 h2 h3,
  apply h1,
  apply not_not.mp,
  exact mt h2 (not_not_intro h3),
end

-- 14ª demostración
example :
  (Q → R) → ((¬Q → ¬P) → (P → R)) :=
begin
  intros h1 h2 h3,
  exact h1 (not_not.mp (mt h2 (not_not_intro h3))),
end

-- 15ª demostración
example :
  (Q → R) → ((¬Q → ¬P) → (P → R)) :=
λ h1 h2 h3, h1 (not_not.mp (mt h2 (not_not_intro h3)))

-- 16ª demostración
lemma aux :
  (Q → R) → ((¬Q → ¬P) → (P → R)) :=
-- by hint
by finish

#print axioms aux
