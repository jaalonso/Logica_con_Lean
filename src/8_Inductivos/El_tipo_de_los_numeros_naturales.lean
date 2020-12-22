-- El tipo de los números naturales
-- ================================

import tactic

-- ----------------------------------------------------
-- Ejercicio 1. Definir el tipo Nat de los números
-- naturales con los constructores Cero (para el número
-- 0) y Suc (para la función sucesor).
-- ----------------------------------------------------

inductive Nat : Type
| Cero : Nat
| Suc  : Nat → Nat

-- #print prefix Nat

-- ----------------------------------------------------
-- Ejercicio 2. Abrir el espacio de nimbre de Nat
-- ----------------------------------------------------

namespace Nat

-- ----------------------------------------------------
-- Ejercicio 3. Definir la función
--    repr : Nat → string
-- tal que (repr n) es la cadena que representa al
-- número natural. Por ejemplo,
--     repr (Suc (Cero)) = "Suc (Cero)"
-- ----------------------------------------------------

def repr : Nat → string
| Cero    := "Cero"
| (Suc n) := "Suc (" ++ repr n ++ ")"

-- #eval repr (Suc (Cero)) -- = "Suc (Cero)"

-- ----------------------------------------------------
-- Ejercicio 4. Declarar repr la función para
-- representar números naturales. Por ejemplo,
--    #eval Suc (Cero) = Suc (Cero)
-- ----------------------------------------------------

instance : has_repr Nat := ⟨repr⟩

-- #eval Suc (Cero) -- = Suc (Cero)

-- ----------------------------------------------------
-- Ejercicio 5. Definir la función
--    nat2int : Nat → ℕ
-- tal que (nat2int n) es el número entero
-- correspondiente al número natural n. Por ejemplo,
--    nat2int (Suc (Suc (Suc Cero))) =  3
-- ----------------------------------------------------

def nat2int : Nat → ℕ
| Cero    := 0
| (Suc n) := 1 + nat2int n

-- #eval nat2int (Suc (Suc (Suc Cero)))

-- ----------------------------------------------------
-- Ejercicio 6. Definir la función
--    int2nat : ℕ -> Nat
-- tal que (int2nat n) es el número natural
-- correspondiente al número entero n. Por ejemplo,
--    int2nat 3 = Suc (Suc (Suc (Cero)))
-- ----------------------------------------------------

def int2nat : ℕ -> Nat
| 0     := Cero
| (n+1) := Suc (int2nat n)

-- #eval int2nat 3 -- ==  Suc (Suc (Suc (Cero)))

-- ----------------------------------------------------
-- Ejercicio 7. Definir la función
--    suma : Nat → Nat → Nat
-- tal que (suma m n) es la suma de los número
-- naturales m y n. Por ejemplo,
--    #eval suma (Suc (Suc Cero)) (Suc Cero)
--    Da: Suc (Suc (Suc (Cero)))
-- ----------------------------------------------------

def suma : Nat → Nat → Nat
| Cero    n := n
| (Suc m) n := Suc (suma m n)

-- #eval suma (Suc (Suc Cero)) (Suc Cero)
-- Da: Suc (Suc (Suc (Cero)))

-- ----------------------------------------------------
-- Ejercicio 8. Declarar lar variables m y n sobre Nat.
-- ----------------------------------------------------

variables (m n : Nat)

-- ----------------------------------------------------
-- Ejercicio 9. Demostrar los siguientes lemas:
-- + suma_1 :
--      suma Cero n = n :=
-- + suma_2 :
--      suma (Suc m) n = Suc (suma m n) :=
-- ----------------------------------------------------

@[simp]
lemma suma_1 :
  suma Cero n = n :=
rfl

@[simp]
lemma suma_2 :
  suma (Suc m) n = Suc (suma m n) :=
rfl

-- ----------------------------------------------------
-- Ejercicio 10. Demostrar que
--    suma n Cero = n
-- ----------------------------------------------------

-- 1ª demostración
example :
  suma n Cero = n :=
begin
  induction n with m HI,
  { rw suma_1, },
  { rw suma_2,
    rw HI, },
end

-- 2ª demostración
example :
  suma n Cero = n :=
begin
  induction n with m HI,
  { show suma Cero Cero = Cero,
      by rw suma_1, },
  { calc suma (Suc m) Cero
         = Suc (suma m Cero) :by rw suma_2
     ... = Suc m             :by rw congr_arg Suc HI, },
end

-- 3ª demostración
example :
  suma n Cero = n :=
begin
  induction n with m HI,
  { show suma Cero Cero = Cero,
      by simp, },
  { calc suma (Suc m) Cero
         = Suc (suma m Cero) :by simp
     ... = Suc m             :by simp [HI], },
end

-- 4ª demostración
example :
  suma n Cero = n :=
begin
  induction n with m HI,
  { simp, },
  { simp [HI], },
end

-- 5ª demostración
example :
  suma n Cero = n :=
by induction n ; simp [*]

-- 6ª demostración
example :
  suma n Cero = n :=
Nat.rec_on n
  ( show suma Cero Cero = Cero,
      by rw suma_1)
  ( assume m,
    assume HI: suma m Cero = m,
    show suma (Suc m) Cero = Suc m, from
      calc suma (Suc m) Cero
           = Suc (suma m Cero) :by rw suma_2
       ... = Suc m             :by rw congr_arg Suc HI)


-- 7ª demostración
example :
  suma n Cero = n :=
Nat.rec_on n
  ( show suma Cero Cero = Cero,
      by simp)
  ( assume m,
    assume HI: suma m Cero = m,
    show suma (Suc m) Cero = Suc m, from
      calc suma (Suc m) Cero
           = Suc (suma m Cero) :by simp
       ... = Suc m             :by simp [HI])

-- 8ª demostración
example :
  suma n Cero = n :=
Nat.rec_on n
  ( by simp)
  ( assume m,
    assume HI: suma m Cero = m,
    by simp [HI])

-- 9ª demostración
example :
  suma n Cero = n :=
Nat.rec_on n
  (by simp)
  (λ m HI, by simp [HI])

-- 10ª demostración
lemma suma_Cero :
  ∀ n, suma n Cero = n
| Cero    := by simp
| (Suc m) := by simp [suma_Cero m]

-- ----------------------------------------------------
-- Ejercicio 11. Cerrar el espacio de nombre Nat.
-- ----------------------------------------------------

end Nat
