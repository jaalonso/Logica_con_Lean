-- Las irreflexivas y transitivas son antisimétricas
-- =================================================

variable A : Type
variable R : A → A → Prop

-- #reduce irreflexive R
-- #reduce transitive R

-- ?ª demostración
example 
  (h1 : irreflexive R) 
  (h2 : transitive R) 
  : ∀ x y, R x y → ¬ R y x :=
begin
  intros x y h3 h4,
  apply h1 x,
  apply h2 h3 h4,
end

-- ?ª demostración
example 
  (h1 : irreflexive R) 
  (h2 : transitive R) 
  : ∀ x y, R x y → ¬ R y x :=
begin
  intros x y h3 h4,
  apply (h1 x) (h2 h3 h4),
end

-- ?ª demostración
example 
  (h1 : irreflexive R) 
  (h2 : transitive R) 
  : ∀ x y, R x y → ¬ R y x :=
λ x y h3 h4, (h1 x) (h2 h3 h4)

-- ?ª demostración
example 
  (h1 : irreflexive R) 
  (h2 : transitive R) 
  : ∀ x y, R x y → ¬ R y x :=
assume x y,
assume h3 : R x y,
assume h4 : R y x,
have h5 : R x x, from h2 h3 h4,
have h6 : ¬ R x x, from h1 x,
show false, from h6 h5
