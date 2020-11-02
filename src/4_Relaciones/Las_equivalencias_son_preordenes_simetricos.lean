-- Las equivalencias son preórdenes simétricos
-- ===========================================

-- ----------------------------------------------------
-- Ej. 1. Un preorden es una relación reflexiva y 
-- transitiva. 
-- 
-- Demostrar que las relaciones de equivalencias son
-- los prórdenes simétricos.
-- ----------------------------------------------------

import tactic

variable {A : Type}
variable R : A → A → Prop

def preorden (R : A → A → Prop) : Prop :=
  reflexive R ∧ transitive R

-- #print equivalence  
-- #print symmetric

-- 1ª demostración
example :
  equivalence R ↔ preorden R ∧ symmetric R :=
begin
  split,
  { rintros ⟨h1, h2, h3⟩,
    exact ⟨⟨h1, h3⟩, h2⟩, },
  { rintros ⟨⟨h1, h3⟩, h2⟩,
    exact ⟨h1, h2, h3⟩, },
end
  
-- 2ª demostración
example :
  equivalence R ↔ preorden R ∧ symmetric R :=
⟨λ ⟨h1, h2, h3⟩, ⟨⟨h1, h3⟩, h2⟩,
 λ ⟨⟨h1, h3⟩, h2⟩, ⟨h1, h2, h3⟩⟩  

-- 3ª demostración
example :
  equivalence R ↔ preorden R ∧ symmetric R :=
iff.intro
  ( assume h1 : equivalence R,
    have h2 : reflexive R, from and.left h1,
    have h3 : symmetric R, from and.left (and.right h1),
    have h4 : transitive R, from and.right (and.right h1),
    show preorden R ∧ symmetric R,
      from and.intro (and.intro h2 h4) h3)
  ( assume h1 : preorden R ∧ symmetric R,
    have h2 : preorden R, from and.left h1,
    show equivalence R,
      from and.intro (and.left h2)
             (and.intro (and.right h1) (and.right h2)))

-- 4ª demostración
example :
  equivalence R ↔ preorden R ∧ symmetric R :=
begin
  unfold equivalence preorden,
  tauto,
end

-- 5ª demostración
example :
  equivalence R ↔ preorden R ∧ symmetric R :=
by finish [preorden]

