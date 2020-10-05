-- Pruebas de ∃x (P(x) ∨ Q(x)) ↔ ∃x P(x) ∨ ∃x Q(x) 
-- ============================================

import tactic

section

variable  {U : Type}
variables {P Q : U -> Prop}

-- ------------------------------------------------------
-- Ej. 1. Demostrar
--    ∃x (P(x) ∨ Q(x)) ⊢ ∃x P(x) ∨ ∃x Q(x)
-- ------------------------------------------------------

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

-- 9ª demostración
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

-- 10ª demostración
lemma aux1
  (h1 : ∃x, P x  ∨ Q x)
  : (∃x, P x) ∨ (∃x, Q x) :=
-- by hint
by finish

-- ------------------------------------------------------
-- Ej. 2. Demostrar
--    ∃x P(x) ∨ ∃x Q(x) ⊢ ∃x (P(x) ∨ Q(x))
-- ------------------------------------------------------

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
lemma aux2
  (h1 : (∃x, P x) ∨ (∃x, Q x))
  : ∃x, P x  ∨ Q x :=
-- by hint
by finish

-- ------------------------------------------------------
-- Ej. 3. Demostrar
--    ∃x (P(x) ∨ Q(x)) ↔ ∃x P(x) ∨ ∃x Q(x) 
-- ------------------------------------------------------

-- 1ª demostración
example :
  (∃x, P x  ∨ Q x) ↔ (∃x, P x) ∨ (∃x, Q x) :=
iff.intro aux1 aux2

-- 2ª demostración
example :
  (∃x, P x  ∨ Q x) ↔ (∃x, P x) ∨ (∃x, Q x) :=
⟨aux1, aux2⟩

-- 3ª demostración
example :
  (∃x, P x  ∨ Q x) ↔ (∃x, P x) ∨ (∃x, Q x) :=
-- by library_search
exists_or_distrib

end
