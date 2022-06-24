-- Pruebas de ∃x (P(x) ∨ Q(x)) ↔ ∃x P(x) ∨ ∃x Q(x)
-- ===============================================

import tactic

section

variable  {U : Type}
variables {P Q : U -> Prop}

-- ----------------------------------------------------
-- Ej. 1. Demostrar
--    ∃x (P(x) ∨ Q(x)) ⊢ ∃x P(x) ∨ ∃x Q(x)
-- ----------------------------------------------------

-- 1ª demostración
example
  (h1 : ∃x, P x  ∨ Q x)
  : (∃x, P x) ∨ (∃x, Q x) :=
exists.elim h1
  ( assume a (h2 : P a ∨ Q a),
    or.elim h2
    ( assume h3 : P a,
      have h4 : ∃x, P x,          from exists.intro a h3,
      show (∃x, P x) ∨ (∃x, Q x), from or.inl h4 )
    ( assume h6 : Q a,
      have h7 : ∃x, Q x,          from exists.intro a h6,
      show (∃x, P x) ∨ (∃x, Q x), from or.inr h7 ))

-- 2ª demostración
example
  (h1 : ∃x, P x  ∨ Q x)
  : (∃x, P x) ∨ (∃x, Q x) :=
exists.elim h1
  ( assume a (h2 : P a ∨ Q a),
    or.elim h2
    ( assume h3 : P a,
      have h4 : ∃x, P x,          from ⟨a, h3⟩,
      show (∃x, P x) ∨ (∃x, Q x), from or.inl h4 )
    ( assume h6 : Q a,
      have h7 : ∃x, Q x,          from ⟨a, h6⟩,
      show (∃x, P x) ∨ (∃x, Q x), from or.inr h7 ))

-- 3ª demostración
example
  (h1 : ∃x, P x  ∨ Q x)
  : (∃x, P x) ∨ (∃x, Q x) :=
exists.elim h1
  ( assume a (h2 : P a ∨ Q a),
    or.elim h2
    ( assume h3 : P a,
      have h4 : ∃x, P x,          from ⟨a, h3⟩,
      or.inl h4 )
    ( assume h6 : Q a,
      have h7 : ∃x, Q x,          from ⟨a, h6⟩,
      or.inr h7 ))

-- 4ª demostración
example
  (h1 : ∃x, P x  ∨ Q x)
  : (∃x, P x) ∨ (∃x, Q x) :=
exists.elim h1
  ( assume a (h2 : P a ∨ Q a),
    or.elim h2
    ( assume h3 : P a,
      or.inl ⟨a, h3⟩ )
    ( assume h6 : Q a,
      or.inr ⟨a, h6⟩ ))

-- 5ª demostración
example
  (h1 : ∃x, P x  ∨ Q x)
  : (∃x, P x) ∨ (∃x, Q x) :=
exists.elim h1
  ( assume a (h2 : P a ∨ Q a),
    or.elim h2
    ( λ h3, or.inl ⟨a, h3⟩ )
    ( λ h6, or.inr ⟨a, h6⟩ ))

-- 6ª demostración
example
  (h1 : ∃x, P x  ∨ Q x)
  : (∃x, P x) ∨ (∃x, Q x) :=
exists.elim h1
  (λ a h2, h2.elim (λ h3, or.inl ⟨a, h3⟩)
                   (λ h6, or.inr ⟨a, h6⟩))

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
match h1 with ⟨a, (h2 : P a ∨ Q a)⟩ :=
  ( or.elim h2
    ( assume h3 : P a,
      have h4 : ∃x, P x,          from exists.intro a h3,
      show (∃x, P x) ∨ (∃x, Q x), from or.inl h4 )
    ( assume h6 : Q a,
      have h7 : ∃x, Q x,          from exists.intro a h6,
      show (∃x, P x) ∨ (∃x, Q x), from or.inr h7 ))
end

-- 9ª demostración
example
  (h1 : ∃x, P x  ∨ Q x)
  : (∃x, P x) ∨ (∃x, Q x) :=
begin
  cases h1 with a h3,
  cases h3 with hp hq,
  { left,
    use a,
    exact hp, },
  { right,
    use a,
    exact hq, },
end

-- 10ª demostración
example
  (h1 : ∃x, P x  ∨ Q x)
  : (∃x, P x) ∨ (∃x, Q x) :=
begin
  rcases h1 with ⟨a, hp | hq⟩,
  { left,
    use a,
    exact hp, },
  { right,
    use a,
    exact hq, },
end

-- 11ª demostración
lemma aux1
  (h1 : ∃x, P x  ∨ Q x)
  : (∃x, P x) ∨ (∃x, Q x) :=
-- by hint
by finish

-- ----------------------------------------------------
-- Ej. 2. Demostrar
--    ∃x P(x) ∨ ∃x Q(x) ⊢ ∃x (P(x) ∨ Q(x))
-- ----------------------------------------------------

-- 1ª demostración
example
  (h1 : (∃x, P x) ∨ (∃x, Q x))
  : ∃x, P x  ∨ Q x :=
or.elim h1
  ( assume h2 : ∃x, P x,
    exists.elim h2
      ( assume a (h3 : P a),
        have h4 : P a ∨ Q a, from or.inl h3,
        show ∃x, P x  ∨ Q x, from exists.intro a h4 ))
  ( assume h2 : ∃x, Q x,
    exists.elim h2
      ( assume a (h3 : Q a),
        have h4 : P a ∨ Q a, from or.inr h3,
        show ∃x, P x  ∨ Q x, from exists.intro a h4 ))

-- 2ª demostración
example
  (h1 : (∃x, P x) ∨ (∃x, Q x))
  : ∃x, P x  ∨ Q x :=
h1.elim
  ( assume ⟨a, (h3 : P a)⟩,
    have h4 : P a ∨ Q a, from or.inl h3,
    show ∃x, P x  ∨ Q x, from ⟨a, h4⟩ )
  ( assume ⟨a, (h3 : Q a)⟩,
    have h4 : P a ∨ Q a, from or.inr h3,
    show ∃x, P x  ∨ Q x, from ⟨a, h4⟩ )

-- 3ª demostración
example
  (h1 : (∃x, P x) ∨ (∃x, Q x))
  : ∃x, P x  ∨ Q x :=
h1.elim
  ( assume ⟨a, (h3 : P a)⟩,
    have h4 : P a ∨ Q a, from or.inl h3,
    ⟨a, h4⟩ )
  ( assume ⟨a, (h3 : Q a)⟩,
    have h4 : P a ∨ Q a, from or.inr h3,
    ⟨a, h4⟩ )

-- 4ª demostración
example
  (h1 : (∃x, P x) ∨ (∃x, Q x))
  : ∃x, P x  ∨ Q x :=
h1.elim
  ( assume ⟨a, (h3 : P a)⟩,
    ⟨a, or.inl h3⟩ )
  ( assume ⟨a, (h3 : Q a)⟩,
    ⟨a, or.inr h3⟩ )

-- 5ª demostración
example
  (h1 : (∃x, P x) ∨ (∃x, Q x))
  : ∃x, P x  ∨ Q x :=
h1.elim
  (λ ⟨a, h3⟩, ⟨a, or.inl h3⟩)
  (λ ⟨a, h3⟩, ⟨a, or.inr h3⟩)

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
  { cases hp with a ha,
    use a,
    left,
    exact ha, },
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
  rcases h1 with ⟨a, ha⟩ | ⟨x₁, hx₁⟩,
  { use a,
    left,
    exact ha, },
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

-- ----------------------------------------------------
-- Ej. 3. Demostrar
--    ∃x (P(x) ∨ Q(x)) ↔ ∃x P(x) ∨ ∃x Q(x)
-- ----------------------------------------------------

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
