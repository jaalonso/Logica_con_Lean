-- Lógica de primer orden en Lean
-- ==============================

import tactic

variable  {U : Type}
variable  c : U
variables {P Q : U → Prop}
variable  {R : U -> U -> Prop}
variables (x y z : U)

-- * Reglas del cuantificador universal
-- ====================================

-- ** Regla de eliminación del cuantificador universal
-- ===================================================

-- ----------------------------------------------------
-- Ej. 1. Demostrar
--    P(c), ∀x (P(x) → ¬Q(x)) ⊢ ¬Q(c)
-- ----------------------------------------------------

-- 1ª demostración
example
  (h1 : P c) 
  (h2 : ∀x, P x → ¬Q x)
  : ¬Q c :=
have h3 : P c → ¬Q c, from h2 c,
show ¬Q c,            from h3 h1

-- 2ª demostración
example
  (h1 : P c) 
  (h2 : ∀x, P x → ¬Q x)
  : ¬Q c :=
have h3 : P c → ¬Q c, from h2 c,
h3 h1

-- 3ª demostración
example
  (h1 : P c) 
  (h2 : ∀x, P x → ¬Q x)
  : ¬Q c :=
(h2 c) h1

-- 4ª demostración
example
  (h1 : P c) 
  (h2 : ∀x, P x → ¬Q x)
  : ¬Q c :=
-- by library_search
h2 c h1

-- 5ª demostración
example
  (h1 : P c) 
  (h2 : ∀x, P x → ¬Q x)
  : ¬Q c :=
-- by hint
by tauto

-- 6ª demostración
example
  (h1 : P c) 
  (h2 : ∀x, P x → ¬Q x)
  : ¬Q c :=
by finish

-- 7ª demostración
example
  (h1 : P c) 
  (h2 : ∀x, P x → ¬Q x)
  : ¬Q c :=
begin
  apply h2,
  exact h1,
end

-- ** Regla de introducción del cuantificador universal
-- ====================================================

-- ----------------------------------------------------
-- Ej. 2. Demostrar
--    ∀x [P(x) → ¬Q(x)], ∀x P(x) ⊢ ∀x ¬Q(x)
-- ----------------------------------------------------

-- 1ª demostración
example
  (h1 : ∀x, P x → ¬Q x) 
  (h2 : ∀x, P x)
  : ∀x, ¬Q x :=
assume x₀,
have h4 : P x₀ → ¬Q x₀, from h1 x₀,
have h5 : P x₀,         from h2 x₀,
show ¬Q x₀,             from h4 h5 

-- 2ª demostración
example
  (h1 : ∀x, P x → ¬Q x) 
  (h2 : ∀x, P x)
  : ∀x, ¬Q x :=
assume x₀, (h1 x₀) (h2 x₀) 

-- 3ª demostración
example
  (h1 : ∀x, P x → ¬Q x) 
  (h2 : ∀x, P x)
  : ∀x, ¬Q x :=
λ x₀, (h1 x₀) (h2 x₀) 

-- 4ª demostración
example
  (h1 : ∀x, P x → ¬Q x) 
  (h2 : ∀x, P x)
  : ∀x, ¬Q x :=
begin
  intro x₀,
  apply h1,
  apply h2,
end

-- 5ª demostración
example
  (h1 : ∀x, P x → ¬Q x) 
  (h2 : ∀x, P x)
  : ∀x, ¬Q x :=
begin
  intro x₀,
  specialize h1 x₀,
  specialize h2 x₀,
  apply h1,
  exact h2,
end

-- 6ª demostración
example
  (h1 : ∀x, P x → ¬Q x) 
  (h2 : ∀x, P x)
  : ∀x, ¬Q x :=
begin
  intro x₀,
  specialize h1 x₀,
  specialize h2 x₀,
  exact h1 h2,
end

-- 7ª demostración
example
  (h1 : ∀x, P x → ¬Q x) 
  (h2 : ∀x, P x)
  : ∀x, ¬Q x :=
-- by hint
by tauto

-- 8ª demostración
example
  (h1 : ∀x, P x → ¬Q x) 
  (h2 : ∀x, P x)
  : ∀x, ¬Q x :=
by finish

-- * Reglas del cuantificador existencial
-- ======================================

-- ** Regla de introducción del cuantificador existencial
-- ======================================================

-- ----------------------------------------------------
-- Ej. 3. Demostrar
--    ∀x P(x) ⊢ ∃x P(x)
-- ----------------------------------------------------

-- 1ª demostración
example 
  (h1 : ∀x, P x)
  : ∃x, P x :=
have h2 : P c, from h1 c,
show ∃x, P x,  from exists.intro c h2

-- 2ª demostración
example 
  (h1 : ∀x, P x)
  : ∃x, P x :=
show ∃x, P x,  from exists.intro c (h1 c)

-- 3ª demostración
example 
  (h1 : ∀x, P x)
  : ∃x, P x :=
exists.intro c (h1 c)

-- 4ª demostración
example 
  (h1 : ∀x, P x)
  : ∃x, P x :=
⟨c, h1 c⟩

-- 5ª demostración
example 
  (a : U)
  (h1 : ∀x, P x)
  : ∃x, P x :=
begin
  use a,
  apply h1,
end

-- 6ª demostración
example 
  (a : U)
  (h1 : ∀x, P x)
  : ∃x, P x :=
begin
  constructor,
  apply h1 a,
end

-- 7ª demostración
example 
  [inhabited U]
  (h1 : ∀x, P x)
  : ∃x, P x :=
begin
  constructor,
  apply h1 (default U),
end

-- 8ª demostración
example 
  (h : nonempty U)
  (h1 : ∀x, P x)
  : ∃x, P x :=
begin
  use (classical.choice h),
  apply h1,
end

-- ** Regla de eliminación del cuantificador existencial
-- =====================================================

-- ----------------------------------------------------
-- Ej. 4. Demostrar
--    ∀x [P(x) → Q(x)], ∃x P(x) ⊢ ∃x Q(x)
-- ----------------------------------------------------

-- 1ª demostración
-- ===============

example 
  (h1 : ∀x, P x → Q x) 
  (h2 : ∃x, P x)
  : ∃x, Q x :=
exists.elim h2 
  ( assume x₀ (h3 : P x₀),
    have h4 : P x₀ → Q x₀, from h1 x₀,
    have h5 : Q x₀,        from h4 h3,
    show ∃x, Q x,          from exists.intro x₀ h5 )

-- 2ª demostración
-- ===============

example 
  (h1 : ∀x, P x → Q x) 
  (h2 : ∃x, P x)
  : ∃x, Q x :=
exists.elim h2 
  ( assume x₀ (h3 : P x₀),
    have h4 : P x₀ → Q x₀, from h1 x₀,
    have h5 : Q x₀,        from h4 h3,
    show ∃x, Q x,          from ⟨x₀, h5⟩ )

-- 3ª demostración
-- ===============

example 
  (h1 : ∀x, P x → Q x) 
  (h2 : ∃x, P x)
  : ∃x, Q x :=
exists.elim h2 
  ( assume x₀ (h3 : P x₀),
    have h4 : P x₀ → Q x₀, from h1 x₀,
    have h5 : Q x₀,        from h4 h3,
    ⟨x₀, h5⟩ )

-- 4ª demostración
-- ===============

example 
  (h1 : ∀x, P x → Q x) 
  (h2 : ∃x, P x)
  : ∃x, Q x :=
exists.elim h2 
  ( assume x₀ (h3 : P x₀),
    have h4 : P x₀ → Q x₀, from h1 x₀,
    ⟨x₀, h4 h3⟩ )

-- 5ª demostración
-- ===============

example 
  (h1 : ∀x, P x → Q x) 
  (h2 : ∃x, P x)
  : ∃x, Q x :=
exists.elim h2 
  ( assume x₀ (h3 : P x₀),
    ⟨x₀, h1 x₀ h3⟩ )

-- 6ª demostración
-- ===============

example 
  (h1 : ∀x, P x → Q x) 
  (h2 : ∃x, P x)
  : ∃x, Q x :=
exists.elim h2 (λ x₀ h3, ⟨x₀, h1 x₀ h3⟩)

-- 7ª demostración
-- ===============

example 
  (h1 : ∀x, P x → Q x) 
  (h2 : ∃x, P x)
  : ∃x, Q x :=
-- by library_search
Exists.imp h1 h2

-- 8ª demostración
-- ===============

example 
  (h1 : ∀x, P x → Q x) 
  (h2 : ∃x, P x)
  : ∃x, Q x :=
begin
  cases h2 with x₀ h3,
  use x₀,
  apply h1,
  exact h3,
end

-- 9ª demostración
-- ===============

example 
  (h1 : ∀x, P x → Q x) 
  (h2 : ∃x, P x)
  : ∃x, Q x :=
begin
  cases h2 with x₀ h3,
  use x₀,
  specialize h1 x₀,
  apply h1,
  exact h3,
end

-- 10ª demostración
-- ===============

example 
  (h1 : ∀x, P x → Q x) 
  (h2 : ∃x, P x)
  : ∃x, Q x :=
-- by hint
by tauto

-- 11ª demostración
-- ===============

example 
  (h1 : ∀x, P x → Q x) 
  (h2 : ∃x, P x)
  : ∃x, Q x :=
by finish

-- * Ejercicios sobre cuantificadores
-- ==================================

-- ------------------------------------------------------
-- Ej. 5. Demostrar que
--    ¬∀x P(x) ⊢ ∃x ¬P(x)
-- ------------------------------------------------------

-- 1ª demostración
example 
  (h1 : ¬∀x, P x)
  : ∃x, ¬P x :=
by_contra 
  ( assume h2 : ¬∃x, ¬P x,
    have h8 : ∀x, P x, from 
      ( assume x₀,
        show P x₀, from
          by_contra 
            ( assume h4 : ¬P x₀,
              have h5 : ∃x, ¬P x, from exists.intro x₀ h4,
              show false, from h2 h5 )),
    show false, from h1 h8)

-- 2ª demostración
example 
  (h1 : ¬∀x, P x)
  : ∃x, ¬P x :=
by_contra 
  ( assume h2 : ¬∃x, ¬P x,
    have h8 : ∀x, P x, from 
      ( assume x₀,
        show P x₀, from
          by_contra 
            ( assume h4 : ¬P x₀,
              have h5 : ∃x, ¬P x, from exists.intro x₀ h4,
              show false, from h2 h5 )),
    h1 h8)

-- 3ª demostración
example 
  (h1 : ¬∀x, P x)
  : ∃x, ¬P x :=
by_contra 
  ( assume h2 : ¬∃x, ¬P x,
    have h8 : ∀x, P x, from 
      ( assume x₀,
        show P x₀, from
          by_contra 
            ( assume h4 : ¬P x₀,
              have h5 : ∃x, ¬P x, from exists.intro x₀ h4,
              h2 h5 )),
    h1 h8)

-- 4ª demostración
example 
  (h1 : ¬∀x, P x)
  : ∃x, ¬P x :=
by_contra 
  ( assume h2 : ¬∃x, ¬P x,
    have h8 : ∀x, P x, from 
      ( assume x₀,
        show P x₀, from
          by_contra 
            ( assume h4 : ¬P x₀,
              have h5 : ∃x, ¬P x, from ⟨x₀, h4⟩,
              h2 h5 )),
    h1 h8)

-- 5ª demostración
example 
  (h1 : ¬∀x, P x)
  : ∃x, ¬P x :=
by_contra 
  ( assume h2 : ¬∃x, ¬P x,
    have h8 : ∀x, P x, from 
      ( assume x₀,
        show P x₀, from
          by_contra 
            ( assume h4 : ¬P x₀,
              h2 ⟨x₀, h4⟩ )),
    h1 h8)

-- 6ª demostración
example 
  (h1 : ¬∀x, P x)
  : ∃x, ¬P x :=
by_contra 
  ( assume h2 : ¬∃x, ¬P x,
    have h8 : ∀x, P x, from 
      ( assume x₀,
        show P x₀, from
          by_contra (λ h4, h2 ⟨x₀, h4⟩)),
    h1 h8)

-- 7ª demostración
example 
  (h1 : ¬∀x, P x)
  : ∃x, ¬P x :=
by_contra 
  ( assume h2 : ¬∃x, ¬P x,
    have h8 : ∀x, P x, from 
      ( assume x₀,
        by_contra (λ h4, h2 ⟨x₀, h4⟩)),
    h1 h8)

-- 8ª demostración
example 
  (h1 : ¬∀x, P x)
  : ∃x, ¬P x :=
by_contra 
  ( assume h2 : ¬∃x, ¬P x,
    have h8 : ∀x, P x, from 
      (λ x₀, by_contra (λ h4, h2 ⟨x₀, h4⟩)),
    h1 h8)

-- 9ª demostración
example 
  (h1 : ¬∀x, P x)
  : ∃x, ¬P x :=
by_contra 
  ( assume h2 : ¬∃x, ¬P x,
    h1 (λ x₀, by_contra (λ h4, h2 ⟨x₀, h4⟩)))

-- 10ª demostración
example 
  (h1 : ¬∀x, P x)
  : ∃x, ¬P x :=
by_contra (λ h2, h1 (λ x₀, by_contra (λ h4, h2 ⟨x₀, h4⟩)))

-- 11ª demostración
example 
  (h1 : ¬∀x, P x)
  : ∃x, ¬P x :=
-- by library_search
not_forall.mp h1

-- 12ª demostración
lemma aux1
  (h1 : ¬∀x, P x)
  : ∃x, ¬P x :=
-- by hint
by finish

-- ------------------------------------------------------
-- Ej. 6. Demostrar que
--    ∃x ¬P(x) ⊢ ¬∀x P(x)
-- ------------------------------------------------------

-- 1ª demostración
example
  (h1 : ∃x, ¬P x) 
  : ¬∀x, P x :=
assume h2 : ∀x, P x,
exists.elim h1
  ( assume x₀ (h3 : ¬P x₀),
    have h4 : P x₀, from h2 x₀,
    show false, from h3 h4)

-- 2ª demostración
example
  (h1 : ∃x, ¬P x) 
  : ¬∀x, P x :=
assume h2 : ∀x, P x,
exists.elim h1
  ( assume x₀ (h3 : ¬P x₀),
    have h4 : P x₀, from h2 x₀,
    h3 h4)

-- 3ª demostración
example
  (h1 : ∃x, ¬P x) 
  : ¬∀x, P x :=
assume h2 : ∀x, P x,
exists.elim h1
  ( assume x₀ (h3 : ¬P x₀),
    h3 (h2 x₀))

-- 4ª demostración
example
  (h1 : ∃x, ¬P x) 
  : ¬∀x, P x :=
assume h2 : ∀x, P x,
exists.elim h1
  (λ x₀ h3, h3 (h2 x₀))

-- 5ª demostración
example
  (h1 : ∃x, ¬P x) 
  : ¬∀x, P x :=
λ h2, exists.elim h1 (λ x₀ h3, h3 (h2 x₀))

-- 6ª demostración
example
  (h1 : ∃x, ¬P x) 
  : ¬∀x, P x :=
-- by library_search
not_forall.mpr h1

-- 7ª demostración
example
  (h1 : ∃x, ¬P x) 
  : ¬∀x, P x :=
assume h2 : ∀x, P x,
match h1 with ⟨x₀, (h3 : ¬P x₀)⟩ :=
  ( have h4 : P x₀, from h2 x₀,
    show false,     from h3 h4)
end

-- 8ª demostración
example
  (h1 : ∃x, ¬P x) 
  : ¬∀x, P x :=
begin
  intro h2,
  cases h1 with x₀ h3,
  apply h3,
  apply h2,
end

example
  (h1 : ∃x, ¬P x) 
  : ¬∀x, P x :=
begin
  intro h2,
  obtain ⟨x₀, h3⟩ := h1,
  apply h3,
  apply h2,
end

-- 9ª demostración
example
  (h1 : ∃x, ¬P x) 
  : ¬∀x, P x :=
-- by hint
by tauto

-- 10ª demostración
lemma aux2
  (h1 : ∃x, ¬P x) 
  : ¬∀x, P x :=
by finish

-- ------------------------------------------------------
-- Ej. 7. Demostrar que
--    ¬∀x P(x) ↔ ∃x ¬P(x)
-- ------------------------------------------------------

-- 1ª demostración
example :
  (¬∀x, P x) ↔ (∃x, ¬P x) :=
iff.intro 
  ( assume h1 : ¬∀x, P x,
    show ∃x, ¬P x, from aux1 h1)
  ( assume h2 : ∃x, ¬P x,
    show ¬∀x, P x, from aux2 h2)

-- 2ª demostración
example :
  (¬∀x, P x) ↔ (∃x, ¬P x) :=
iff.intro aux1 aux2

-- 3ª demostración
example :
  (¬∀x, P x) ↔ (∃x, ¬P x) :=
-- by library_search
not_forall 

-- 4ª demostración
example :
  (¬∀x, P x) ↔ (∃x, ¬P x) :=
begin
  split,
  { exact aux1, },
  { exact aux2, },
end  

-- 5ª demostración
example :
  (¬∀x, P x) ↔ (∃x, ¬P x) :=
-- by hint
by finish

-- ------------------------------------------------------
-- Ej. 8. Demostrar
--    ∀x (P(x) ∧ Q(x)) ⊢ ∀x P(x) ∧ ∀x Q(x)
-- ------------------------------------------------------

-- 1ª demostración
example
  (h1 : ∀x, P x ∧ Q x)
  : (∀x, P x) ∧ (∀x, Q x) :=
have h5 : ∀x, P x, from
    assume x₀,
    have h3 : P x₀ ∧ Q x₀,  from h1 x₀,
    show P x₀,              from and.elim_left h3,
have h9 : ∀x, Q x, from
    assume x₁,
    have h7 : P x₁ ∧ Q x₁,  from h1 x₁,
    show Q x₁,              from and.elim_right h7,
show (∀x, P x) ∧ (∀x, Q x), from and.intro h5 h9

-- 2ª demostración
example
  (h1 : ∀x, P x ∧ Q x)
  : (∀x, P x) ∧ (∀x, Q x) :=
have h5 : ∀x, P x, from
    assume x₀,
    have h3 : P x₀ ∧ Q x₀,  from h1 x₀,
    show P x₀,              from h3.left,
have h9 : ∀x, Q x, from
    assume x₁,
    have h7 : P x₁ ∧ Q x₁,  from h1 x₁,
    show Q x₁,              from h7.right,
show (∀x, P x) ∧ (∀x, Q x), from ⟨h5, h9⟩

-- 3ª demostración
example
  (h1 : ∀x, P x ∧ Q x)
  : (∀x, P x) ∧ (∀x, Q x) :=
have h5 : ∀x, P x, from
    assume x₀,
    have h3 : P x₀ ∧ Q x₀,  from h1 x₀,
    h3.left,
have h9 : ∀x, Q x, from
    assume x₁,
    have h7 : P x₁ ∧ Q x₁,  from h1 x₁,
    h7.right,
show (∀x, P x) ∧ (∀x, Q x), from ⟨h5, h9⟩

-- 4ª demostración
example
  (h1 : ∀x, P x ∧ Q x)
  : (∀x, P x) ∧ (∀x, Q x) :=
have h5 : ∀x, P x, from
    assume x₀,
    (h1 x₀).left,
have h9 : ∀x, Q x, from
    assume x₁,
    (h1 x₁).right,
show (∀x, P x) ∧ (∀x, Q x), from ⟨h5, h9⟩

-- 5ª demostración
example
  (h1 : ∀x, P x ∧ Q x)
  : (∀x, P x) ∧ (∀x, Q x) :=
have h5 : ∀x, P x, from
    λ x₀, (h1 x₀).left,
have h9 : ∀x, Q x, from
    λ x₁, (h1 x₁).right,
show (∀x, P x) ∧ (∀x, Q x), from ⟨h5, h9⟩

-- 6ª demostración
example
  (h1 : ∀x, P x ∧ Q x)
  : (∀x, P x) ∧ (∀x, Q x) :=
have h5 : ∀x, P x, from
    λ x₀, (h1 x₀).left,
have h9 : ∀x, Q x, from
    λ x₁, (h1 x₁).right,
⟨h5, h9⟩

-- 7ª demostración
example
  (h1 : ∀x, P x ∧ Q x)
  : (∀x, P x) ∧ (∀x, Q x) :=
⟨λ x₀, (h1 x₀).left, λ x₁, (h1 x₁).right⟩

-- 8ª demostración
example
  (h1 : ∀x, P x ∧ Q x)
  : (∀x, P x) ∧ (∀x, Q x) :=
-- by library_search
forall_and_distrib.mp h1

-- 9ª demostración
example
  (h1 : ∀x, P x ∧ Q x)
  : (∀x, P x) ∧ (∀x, Q x) :=
begin
  split,
  { intro x₀,
    specialize h1 x₀,
    exact h1.left, },
  { intro x₁,
    specialize h1 x₁,
    exact h1.right, },
end

-- 9ª demostración
lemma aux3
  (h1 : ∀x, P x ∧ Q x)
  : (∀x, P x) ∧ (∀x, Q x) :=
-- by hint
by finish

-- ------------------------------------------------------
-- Ej. 9. Demostrar
--    ∀x P(x) ∧ ∀x Q(x) ⊢ ∀x (P(x) ∧ Q(x))
-- ------------------------------------------------------

-- 1ª demostración
example
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
assume x₀,
have h3 : ∀x, P x, from and.elim_left h1,
have h4 : P x₀,    from h3 x₀,
have h5 : ∀x, Q x, from and.elim_right h1,
have h6 : Q x₀,    from h5 x₀,
show P x₀ ∧ Q x₀,  from and.intro h4 h6

-- 2ª demostración
example
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
assume x₀,
have h3 : ∀x, P x, from h1.left,
have h4 : P x₀,    from h3 x₀,
have h5 : ∀x, Q x, from h1.right,
have h6 : Q x₀,    from h5 x₀,
show P x₀ ∧ Q x₀,  from ⟨h4, h6⟩

-- 3ª demostración
example
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
assume x₀,
have h3 : ∀x, P x, from h1.left,
have h4 : P x₀,    from h3 x₀,
have h5 : ∀x, Q x, from h1.right,
have h6 : Q x₀,    from h5 x₀,
⟨h4, h6⟩

-- 4ª demostración
example
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
assume x₀,
have h3 : ∀x, P x, from h1.left,
have h4 : P x₀,    from h3 x₀,
have h5 : ∀x, Q x, from h1.right,
⟨h4, h5 x₀⟩

-- 5ª demostración
example
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
assume x₀,
have h3 : ∀x, P x, from h1.left,
have h4 : P x₀,    from h3 x₀,
⟨h4, h1.right x₀⟩

-- 6ª demostración
example
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
assume x₀,
have h3 : ∀x, P x, from h1.left,
⟨h3 x₀, h1.right x₀⟩

-- 7ª demostración
example
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
assume x₀,
⟨h1.left x₀, h1.right x₀⟩

-- 8ª demostración
example
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
λ x₀, ⟨h1.left x₀, h1.right x₀⟩

-- 9ª demostración
example
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
-- by library_search
forall_and_distrib.mpr h1

-- 10ª demostración
example
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
begin
  cases h1 with h2 h3,
  intro x₀,
  split,
  { apply h2, },
  { apply h3, },
end

-- 11ª demostración
example
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
-- by hint
by tauto

-- 12ª demostración
lemma aux4
  (h1 : (∀x, P x) ∧ (∀x, Q x))
  : ∀x, P x ∧ Q x :=
by finish

-- ------------------------------------------------------
-- Ej. 10. Demostrar
--    ∀x (P(x) ∧ Q(x)) ↔ ∀x P(x) ∧ ∀x Q(x)
-- ------------------------------------------------------

-- 1ª demostración
example :
  (∀x, P x ∧ Q x) ↔ (∀x, P x) ∧ (∀x, Q x) :=
iff.intro aux3 aux4

-- 2ª demostración
example :
  (∀x, P x ∧ Q x) ↔ (∀x, P x) ∧ (∀x, Q x) :=
-- by library_search
forall_and_distrib

-- 3ª demostración
example :
  (∀x, P x ∧ Q x) ↔ (∀x, P x) ∧ (∀x, Q x) :=
-- by hint
by finish

-- -----------------------------------------------------
-- Ej. 11. Demostrar
--    ∃x (P(x) ∨ Q(x)) ⊢ ∃x P(x) ∨ ∃x Q(x)
-- -----------------------------------------------------

-- 1ª demostración
example
  (h1 : ∃x, P x  ∨ Q x)
  : (∃x, P x) ∨ (∃x, Q x) :=
exists.elim h1 
  ( assume x₀ (h2 : P x₀ ∨ Q x₀),
    or.elim h2
    ( assume h3 : P x₀,
      have h4 : ∃x, P x,          from exists.intro x₀ h3,
      show (∃x, P x) ∨ (∃x, Q x), from or.inl h4 )
    ( assume h6 : Q x₀,
      have h7 : ∃x, Q x,          from exists.intro x₀ h6,
      show (∃x, P x) ∨ (∃x, Q x), from or.inr h7 ))

-- 2ª demostración
example
  (h1 : ∃x, P x  ∨ Q x)
  : (∃x, P x) ∨ (∃x, Q x) :=
exists.elim h1 
  ( assume x₀ (h2 : P x₀ ∨ Q x₀),
    or.elim h2
    ( assume h3 : P x₀,
      have h4 : ∃x, P x,          from ⟨x₀, h3⟩,
      show (∃x, P x) ∨ (∃x, Q x), from or.inl h4 )
    ( assume h6 : Q x₀,
      have h7 : ∃x, Q x,          from ⟨x₀, h6⟩,
      show (∃x, P x) ∨ (∃x, Q x), from or.inr h7 ))

-- 3ª demostración
example
  (h1 : ∃x, P x  ∨ Q x)
  : (∃x, P x) ∨ (∃x, Q x) :=
exists.elim h1 
  ( assume x₀ (h2 : P x₀ ∨ Q x₀),
    or.elim h2
    ( assume h3 : P x₀,
      have h4 : ∃x, P x,          from ⟨x₀, h3⟩,
      or.inl h4 )
    ( assume h6 : Q x₀,
      have h7 : ∃x, Q x,          from ⟨x₀, h6⟩,
      or.inr h7 ))

-- 4ª demostración
example
  (h1 : ∃x, P x  ∨ Q x)
  : (∃x, P x) ∨ (∃x, Q x) :=
exists.elim h1 
  ( assume x₀ (h2 : P x₀ ∨ Q x₀),
    or.elim h2
    ( assume h3 : P x₀,
      or.inl ⟨x₀, h3⟩ )
    ( assume h6 : Q x₀,
      or.inr ⟨x₀, h6⟩ ))

-- 5ª demostración
example
  (h1 : ∃x, P x  ∨ Q x)
  : (∃x, P x) ∨ (∃x, Q x) :=
exists.elim h1 
  ( assume x₀ (h2 : P x₀ ∨ Q x₀),
    or.elim h2
    ( λ h3, or.inl ⟨x₀, h3⟩ )
    ( λ h6, or.inr ⟨x₀, h6⟩ ))

-- 6ª demostración
example
  (h1 : ∃x, P x  ∨ Q x)
  : (∃x, P x) ∨ (∃x, Q x) :=
exists.elim h1 
  (λ x₀ h2, h2.elim (λ h3, or.inl ⟨x₀, h3⟩)
                    (λ h6, or.inr ⟨x₀, h6⟩))

-- 7ª demostración
example
  (h1 : ∃x, P x  ∨ Q x)
  : (∃x, P x) ∨ (∃x, Q x) :=
-- by library_search
exists_or_distrib.mp h1

-- 8ª demostración
example
  (h1 : ∃x, P x  ∨ Q x)
  : (∃x, P x) ∨ (∃x, Q x) :=
match h1 with ⟨x₀, (h2 : P x₀ ∨ Q x₀)⟩ :=
  ( or.elim h2
    ( assume h3 : P x₀,
      have h4 : ∃x, P x,          from exists.intro x₀ h3,
      show (∃x, P x) ∨ (∃x, Q x), from or.inl h4 )
    ( assume h6 : Q x₀,
      have h7 : ∃x, Q x,          from exists.intro x₀ h6,
      show (∃x, P x) ∨ (∃x, Q x), from or.inr h7 ))
end

-- 9ª demostración
example
  (h1 : ∃x, P x  ∨ Q x)
  : (∃x, P x) ∨ (∃x, Q x) :=
begin
  cases h1 with x₀ h3,
  cases h3 with hp hq,
  { left,
    use x₀,
    exact hp, },
  { right,
    use x₀,
    exact hq, },
end

-- 10ª demostración
example
  (h1 : ∃x, P x  ∨ Q x)
  : (∃x, P x) ∨ (∃x, Q x) :=
begin
  rcases h1 with ⟨x₀, hp | hq⟩,
  { left,
    use x₀,
    exact hp, },
  { right,
    use x₀,
    exact hq, },
end

-- 11ª demostración
lemma aux5
  (h1 : ∃x, P x  ∨ Q x)
  : (∃x, P x) ∨ (∃x, Q x) :=
-- by hint
by finish

-- -----------------------------------------------------
-- Ej. 12. Demostrar
--    ∃x P(x) ∨ ∃x Q(x) ⊢ ∃x (P(x) ∨ Q(x))
-- -----------------------------------------------------

-- 1ª demostración
example
  (h1 : (∃x, P x) ∨ (∃x, Q x))
  : ∃x, P x  ∨ Q x :=
or.elim h1 
  ( assume h2 : ∃x, P x,
    exists.elim h2 
      ( assume x₀ (h3 : P x₀),
        have h4 : P x₀ ∨ Q x₀, from or.inl h3,
        show ∃x, P x  ∨ Q x,   from exists.intro x₀ h4 ))
  ( assume h2 : ∃x, Q x,
    exists.elim h2 
      ( assume x₀ (h3 : Q x₀),
        have h4 : P x₀ ∨ Q x₀, from or.inr h3,
        show ∃x, P x  ∨ Q x,   from exists.intro x₀ h4 ))

-- 2ª demostración
example
  (h1 : (∃x, P x) ∨ (∃x, Q x))
  : ∃x, P x  ∨ Q x :=
h1.elim 
  ( assume ⟨x₀, (h3 : P x₀)⟩,
    have h4 : P x₀ ∨ Q x₀, from or.inl h3,
    show ∃x, P x  ∨ Q x,   from ⟨x₀, h4⟩ )
  ( assume ⟨x₀, (h3 : Q x₀)⟩,
    have h4 : P x₀ ∨ Q x₀, from or.inr h3,
    show ∃x, P x  ∨ Q x,   from ⟨x₀, h4⟩ )

-- 3ª demostración
example
  (h1 : (∃x, P x) ∨ (∃x, Q x))
  : ∃x, P x  ∨ Q x :=
h1.elim 
  ( assume ⟨x₀, (h3 : P x₀)⟩,
    have h4 : P x₀ ∨ Q x₀, from or.inl h3,
    ⟨x₀, h4⟩ )
  ( assume ⟨x₀, (h3 : Q x₀)⟩,
    have h4 : P x₀ ∨ Q x₀, from or.inr h3,
    ⟨x₀, h4⟩ )

-- 4ª demostración
example
  (h1 : (∃x, P x) ∨ (∃x, Q x))
  : ∃x, P x  ∨ Q x :=
h1.elim 
  ( assume ⟨x₀, (h3 : P x₀)⟩,
    ⟨x₀, or.inl h3⟩ )
  ( assume ⟨x₀, (h3 : Q x₀)⟩,
    ⟨x₀, or.inr h3⟩ )

-- 5ª demostración
example
  (h1 : (∃x, P x) ∨ (∃x, Q x))
  : ∃x, P x  ∨ Q x :=
h1.elim 
  (λ ⟨x₀, h3⟩, ⟨x₀, or.inl h3⟩)
  (λ ⟨x₀, h3⟩, ⟨x₀, or.inr h3⟩)

-- 6ª demostración
example
  (h1 : (∃x, P x) ∨ (∃x, Q x))
  : ∃x, P x  ∨ Q x :=
-- by library_search
exists_or_distrib.mpr h1

-- 7ª demostración
example
  (h1 : (∃x, P x) ∨ (∃x, Q x))
  : ∃x, P x  ∨ Q x :=
begin
  cases h1 with hp hq,
  { cases hp with x₀ hx₀,
    use x₀,
    left,
    exact hx₀, },
  { cases hq with x₁ hx₁,
    use x₁,
    right,
    exact hx₁, },
end

-- 8ª demostración
example
  (h1 : (∃x, P x) ∨ (∃x, Q x))
  : ∃x, P x  ∨ Q x :=
begin
  rcases h1 with ⟨x₀, hx₀⟩ | ⟨x₁, hx₁⟩,
  { use x₀,
    left,
    exact hx₀, },
  { use x₁,
    right,
    exact hx₁, },
end

-- 9ª demostración
lemma aux6
  (h1 : (∃x, P x) ∨ (∃x, Q x))
  : ∃x, P x  ∨ Q x :=
-- by hint
by finish

-- -----------------------------------------------------
-- Ej. 13. Demostrar
--    ∃x (P(x) ∨ Q(x)) ↔ ∃x P(x) ∨ ∃x Q(x) 
-- -----------------------------------------------------

-- 1ª demostración
example :
  (∃x, P x  ∨ Q x) ↔ (∃x, P x) ∨ (∃x, Q x) :=
iff.intro aux5 aux6

-- 2ª demostración
example :
  (∃x, P x  ∨ Q x) ↔ (∃x, P x) ∨ (∃x, Q x) :=
⟨aux5, aux6⟩

-- 3ª demostración
example :
  (∃x, P x  ∨ Q x) ↔ (∃x, P x) ∨ (∃x, Q x) :=
-- by library_search
exists_or_distrib

-- ------------------------------------------------------
-- Ej. 14. Demostrar que
--    ∃x∃yR(x,y) → ∃y∃xR(x,y)
-- ------------------------------------------------------

-- 1ª demostración
example :
  (∃ x, ∃ y, R x y) → (∃ y, ∃ x, R x y) :=
assume h1 : ∃ x, ∃ y, R x y,
exists.elim h1 
  ( assume x₀ (h2 : ∃ y, R x₀ y), 
    exists.elim h2
      ( assume y₀ (h3 : R x₀ y₀),
        have h4 : ∃ x, R x y₀, from exists.intro x₀ h3,
        show ∃ y, ∃ x, R x y,  from exists.intro y₀ h4))

-- 2ª demostración
example :
  (∃ x, ∃ y, R x y) → (∃ y, ∃ x, R x y) :=
assume ⟨x₀, y₀, (h1 : R x₀ y₀)⟩,
have h2 : ∃ x, R x y₀, from ⟨x₀, h1⟩,
show (∃ y, ∃ x, R x y), from ⟨y₀, h2⟩

-- 3ª demostración
example :
  (∃ x, ∃ y, R x y) → (∃ y, ∃ x, R x y) :=
assume ⟨x₀, y₀, (h1 : R x₀ y₀)⟩,
show (∃ y, ∃ x, R x y), from ⟨y₀, ⟨x₀, h1⟩⟩

-- 4ª demostración
example :
  (∃ x, ∃ y, R x y) → (∃ y, ∃ x, R x y) :=
assume ⟨x₀, y₀, (h1 : R x₀ y₀)⟩,
show (∃ y, ∃ x, R x y), from ⟨y₀, x₀, h1⟩

-- 5ª demostración
example :
  (∃ x, ∃ y, R x y) → (∃ y, ∃ x, R x y) :=
assume ⟨x₀, y₀, (h1 : R x₀ y₀)⟩,
⟨y₀, x₀, h1⟩

-- 6ª demostración
example :
  (∃ x, ∃ y, R x y) → (∃ y, ∃ x, R x y) :=
λ ⟨x₀, y₀, h1⟩, ⟨y₀, x₀, h1⟩

-- 7ª demostración
example :
  (∃ x y, R x y) → (∃ y x, R x y) :=
-- by library_search
exists_comm.mp 

-- 8ª demostración
example :
  (∃ x, ∃ y, R x y) → (∃ y, ∃ x, R x y) :=
begin
  intro h1,
  cases h1 with x₀ h2,
  cases h2 with y₀ h3,
  use y₀,
  use x₀,
  exact h3,
end

-- 9ª demostración
example :
  (∃ x, ∃ y, R x y) → (∃ y, ∃ x, R x y) :=
begin
  intro h1,
  cases h1 with x₀ h2,
  cases h2 with y₀ h3,
  use [y₀, x₀],
  exact h3,
end

-- 10ª demostración
example :
  (∃ x, ∃ y, R x y) → (∃ y, ∃ x, R x y) :=
begin
  intro h1,
  rcases h1 with ⟨x₀, y₀, h2⟩,
  use [y₀, x₀],
  exact h2,
end

-- 11ª demostración
example :
  (∃ x, ∃ y, R x y) → (∃ y, ∃ x, R x y) :=
begin
  intro h1,
  rcases h1 with ⟨x₀, y₀, h2⟩,
  exact ⟨y₀, x₀, h2⟩,
end

-- 12ª demostración
example :
  (∃ x, ∃ y, R x y) → (∃ y, ∃ x, R x y) :=
begin
  rintro ⟨x₀, y₀, h2⟩,
  exact ⟨y₀, x₀, h2⟩,
end

-- 13ª demostración
example :
  (∃ x, ∃ y, R x y) → (∃ y, ∃ x, R x y) :=
-- by hint
by tauto

-- 14ª demostración
lemma aux :
  (∃ x, ∃ y, R x y) → (∃ y, ∃ x, R x y) :=
by finish

-- ------------------------------------------------------
-- Ej. 15. Demostrar que
--    ∃x∃yR(x,y) ↔ ∃y∃xR(x,y)
-- ------------------------------------------------------

-- 1ª demostración
example :
  (∃ x y, R x y) ↔ (∃ y x, R x y) :=
iff.intro aux aux

-- 2ª demostración
example :
  (∃ x y, R x y) ↔ (∃ y x, R x y) :=
⟨aux, aux⟩

-- 3ª demostración
example :
  (∃ x y, R x y) ↔ (∃ y x, R x y) :=
-- by library_search
exists_comm

-- 4ª demostración
example :
  (∃ x y, R x y) ↔ (∃ y x, R x y) :=
-- by hint
by tauto

-- * Reglas de la igualdad
-- =======================

-- ** Regla de eliminación de la igualdad
-- ======================================

-- ----------------------------------------------------
-- Ej. 16. Demostrar que
--      x + 1 = 1 + x
--      x + 1 > 1 → x + 1 > 0
--      ⊢ 1 + x > 1 → 1 + x > 0
-- ----------------------------------------------------

variable [has_add U]
variable [has_one U]
variable [has_lt U]
variable [has_zero U]

-- 1ª demostración
example 
  (h1 : x + 1 = 1 + x)
  (h2 : x + 1 > 1 → x + 1 > 0)
  : 1 + x > 1 → 1 + x > 0 :=
eq.subst h1 h2


-- 2ª demostración
example 
  (h1 : x + 1 = 1 + x)
  (h2 : x + 1 > 1 → x + 1 > 0)
  : 1 + x > 1 → 1 + x > 0 :=
h1 ▸ h2

-- 3ª demostración
example 
  (h1 : x + 1 = 1 + x)
  (h2 : x + 1 > 1 → x + 1 > 0)
  : 1 + x > 1 → 1 + x > 0 :=
begin
  rw h1 at h2,
  exact h2,
end

-- 4ª demostración
example 
  (h1 : x + 1 = 1 + x)
  (h2 : x + 1 > 1 → x + 1 > 0)
  : 1 + x > 1 → 1 + x > 0 :=
begin
  rw ←h1,
  exact h2,
end

-- 5ª demostración
example 
  (h1 : x + 1 = 1 + x)
  (h2 : x + 1 > 1 → x + 1 > 0)
  : 1 + x > 1 → 1 + x > 0 :=
-- by hint
by finish

-- ----------------------------------------------------
-- Ej. 17. Demostrar que
--    x = y, y = z ⊢ x = z
-- ----------------------------------------------------

-- 1ª demostración
example 
  (h1 : x = y)
  (h2 : y = z)
  : x = z :=
eq.subst h2 h1

-- 2ª demostración
example 
  (h1 : x = y)
  (h2 : y = z)
  : x = z :=
h2 ▸ h1

-- 3ª demostración
example 
  (h1 : x = y)
  (h2 : y = z)
  : x = z :=
eq.substr h1 h2

-- 4ª demostración
example 
  (h1 : x = y)
  (h2 : y = z)
  : x = z :=
eq.trans h1 h2

-- 5ª demostración
example 
  (h1 : x = y)
  (h2 : y = z)
  : x = z :=
begin
  rw h1,
  exact h2,
end

-- 6ª demostración
example 
  (h1 : x = y)
  (h2 : y = z)
  : x = z :=
begin
  rw h1,
  assumption,
end

-- 7ª demostración
example 
  (h1 : x = y)
  (h2 : y = z)
  : x = z :=
begin
  rwa h1,
end

-- 8ª demostración
example 
  (h1 : x = y)
  (h2 : y = z)
  : x = z :=
by rwa h1

-- 9ª demostración
example 
  (h1 : x = y)
  (h2 : y = z)
  : x = z :=
begin
  rwa ←h2,
end

-- 10ª demostración
example 
  (h1 : x = y)
  (h2 : y = z)
  : x = z :=
begin
  rwa h2 at h1,
end

-- 11ª demostración
example 
  (h1 : x = y)
  (h2 : y = z)
  : x = z :=
by simp *

-- 12ª demostración
example 
  (h1 : x = y)
  (h2 : y = z)
  : x = z :=
-- by hint
by finish

-- ** Regla de introducción de la igualdad
-- =======================================

-- ----------------------------------------------------
-- Ej. 18. Demostrar
--    x = y ⊢ y = x 
-- ----------------------------------------------------

-- 1ª demostración
example
  (h1 : x = y)
  : y = x :=
have h2 : x = x, from eq.refl x,
show y = x,      from eq.subst h1 h2

-- 2ª demostración
example
  (h1 : x = y)
  : y = x :=
have h2 : x = x, from eq.refl x,
show y = x,      from h1 ▸ h2

-- 3ª demostración
example
  (h1 : x = y)
  : y = x :=
have h2 : x = x, from eq.refl x,
h1 ▸ h2

-- 4ª demostración
example
  (h1 : x = y)
  : y = x :=
h1 ▸ eq.refl x

-- 5ª demostración
example
  (h1 : x = y)
  : y = x :=
h1 ▸ rfl

-- 6ª demostración
example
  (h1 : x = y)
  : y = x :=
-- by library_search
eq.symm h1

-- 7ª demostración
example
  (h1 : x = y)
  : y = x :=
begin
  rw h1,
end

-- 8ª demostración
example
  (h1 : x = y)
  : y = x :=
by rw h1

-- 9ª demostración
example
  (h1 : x = y)
  : y = x :=
by simp *

-- 10ª demostración
example
  (h1 : x = y)
  : y = x :=
-- by hint
by tauto

-- 11ª demostración
example
  (h1 : x = y)
  : y = x :=
by finish

-- 12ª demostración
example
  (h1 : x = y)
  : y = x :=
by solve_by_elim

-- ----------------------------------------------------
-- Ej. 19. Demostrar
--    y = x → y = z → x = z
-- ----------------------------------------------------

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
