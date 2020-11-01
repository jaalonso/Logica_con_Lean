-- Las equivalencias son preórdenes simétricos
-- ===========================================

import tactic

namespace hidden

variable {A : Type}

def preorder (R : A → A → Prop) : Prop :=
reflexive R ∧ transitive R

variable R : A → A → Prop

-- #print equivalence  
-- #print symmetric

-- 1ª demostración
example :
  equivalence R ↔ preorder R ∧ symmetric R :=
begin
  split,
  { rintros ⟨h1, h2, h3⟩,
    exact ⟨⟨h1, h3⟩, h2⟩, },
  { rintros ⟨⟨h1, h3⟩, h2⟩,
    exact ⟨h1, h2, h3⟩, },
end
  
-- 2ª demostración
example :
  equivalence R ↔ preorder R ∧ symmetric R :=
⟨λ ⟨h1, h2, h3⟩, ⟨⟨h1, h3⟩, h2⟩,
 λ ⟨⟨h1, h3⟩, h2⟩, ⟨h1, h2, h3⟩⟩  

-- 3ª demostración
example :
  equivalence R ↔ preorder R ∧ symmetric R :=
iff.intro
  ( assume h1 : equivalence R,
    have h2 : reflexive R, from and.left h1,
    have h3 : symmetric R, from and.left (and.right h1),
    have h4 : transitive R, from and.right (and.right h1),
    show preorder R ∧ symmetric R,
      from and.intro (and.intro h2 h4) h3)
  ( assume h1 : preorder R ∧ symmetric R,
    have h2 : preorder R, from and.left h1,
    show equivalence R,
      from and.intro (and.left h2)
             (and.intro (and.right h1) (and.right h2)))

-- 4ª demostración
example :
  equivalence R ↔ preorder R ∧ symmetric R :=
begin
  unfold equivalence preorder,
  tauto,
end

-- 5ª demostración
example :
  equivalence R ↔ preorder R ∧ symmetric R :=
by finish [preorder]

end hidden
