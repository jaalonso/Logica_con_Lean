-- Razonamiento con tipos enumerados: Los días de la semana
-- ========================================================

-- ----------------------------------------------------
-- Ejercicio ?. Definir el tipo dia cuyos constructores
-- sean los días de la semana.
-- ---------------------------------------------------------------------

inductive dia : Type
| lunes     : dia
| martes    : dia
| miercoles : dia
| jueves    : dia
| viernes   : dia
| sabado    : dia
| domingo   : dia

-- ----------------------------------------------------
-- Ejercicio ?. Calcular el tipo del constructor lunes.
-- ----------------------------------------------------

-- #check dia.lunes
-- Da: dia

-- ----------------------------------------------------
-- Ejercicio ?. Abrir el espacio de nombre dia.
-- ----------------------------------------------------

namespace dia

-- ----------------------------------------------------
-- Ejercicio ?. Calcular el tipo del constructor lunes.
-- ----------------------------------------------------

-- #check lunes
-- Da: dia

-- ----------------------------------------------------
-- Ejercicio ?. Calcular la lista de las funciones
-- definidas en el espacio de nombres dia.
-- ----------------------------------------------------

-- #print prefix dia
-- Da:
--    dia : Type
--    dia.cases_on : Π {C : dia → Sort l} (n : dia),
--      C lunes → C martes → C miercoles → C jueves → C viernes → C sabado → C domingo → C n
--    dia.domingo : dia
--    dia.domingo.inj : domingo = domingo → true
--    dia.domingo.inj_arrow : domingo = domingo → Π ⦃P : Sort l⦄, (true → P) → P
--    dia.domingo.inj_eq : domingo = domingo = true
--    dia.domingo.sizeof_spec : domingo.sizeof = 1
--    dia.has_sizeof_inst : has_sizeof dia
--    dia.jueves : dia
--    dia.jueves.inj : jueves = jueves → true
--    dia.jueves.inj_arrow : jueves = jueves → Π ⦃P : Sort l⦄, (true → P) → P
--    dia.jueves.inj_eq : jueves = jueves = true
--    dia.jueves.sizeof_spec : jueves.sizeof = 1
--    dia.lunes : dia
--    dia.lunes.inj : lunes = lunes → true
--    dia.lunes.inj_arrow : lunes = lunes → Π ⦃P : Sort l⦄, (true → P) → P
--    dia.lunes.inj_eq : lunes = lunes = true
--    dia.lunes.sizeof_spec : lunes.sizeof = 1
--    dia.martes : dia
--    dia.martes.inj : martes = martes → true
--    dia.martes.inj_arrow : martes = martes → Π ⦃P : Sort l⦄, (true → P) → P
--    dia.martes.inj_eq : martes = martes = true
--    dia.martes.sizeof_spec : martes.sizeof = 1
--    dia.miercoles : dia
--    dia.miercoles.inj : miercoles = miercoles → true
--    dia.miercoles.inj_arrow : miercoles = miercoles → Π ⦃P : Sort l⦄, (true → P) → P
--    dia.miercoles.inj_eq : miercoles = miercoles = true
--    dia.miercoles.sizeof_spec : miercoles.sizeof = 1
--    dia.no_confusion : Π {P : Sort l} {v1 v2 : dia}, v1 = v2 → dia.no_confusion_type P v1 v2
--    dia.no_confusion_type : Sort l → dia → dia → Sort l
--    dia.rec : Π {C : dia → Sort l},
--      C lunes → C martes → C miercoles → C jueves → C viernes → C sabado → C domingo → Π (n : dia), C n
--    dia.rec_on : Π {C : dia → Sort l} (n : dia),
--      C lunes → C martes → C miercoles → C jueves → C viernes → C sabado → C domingo → C n
--    dia.sabado : dia
--    dia.sabado.inj : sabado = sabado → true
--    dia.sabado.inj_arrow : sabado = sabado → Π ⦃P : Sort l⦄, (true → P) → P
--    dia.sabado.inj_eq : sabado = sabado = true
--    dia.sabado.sizeof_spec : sabado.sizeof = 1
--    dia.sizeof : dia → ℕ
--    dia.viernes : dia
--    dia.viernes.inj : viernes = viernes → true
--    dia.viernes.inj_arrow : viernes = viernes → Π ⦃P : Sort l⦄, (true → P) → P
--    dia.viernes.inj_eq : viernes = viernes = true
--    dia.viernes.sizeof_spec : viernes.sizeof = 1

-- ----------------------------------------------------
-- Ejercicio ?. Calcular el tipo de las reglas de
-- eliminación (recursores) del tipo dia: dia.rec,
-- dia.rec_on y dia.cases_on.
-- ----------------------------------------------------

-- Recursor (regla de eliminación):
-- #check @dia.rec
-- Da: Π {C : dia → Sort u_1},
--       C lunes →
--       C martes →
--       C miercoles →
--       C jueves →
--       C viernes →
--       C sabado →
--       C domingo
--       → Π (n : dia), C n
--
-- #check @dia.rec_on
-- Da: Π {C : dia → Sort u_1} (n : dia),
--       C lunes →
--       C martes →
--       C miercoles →
--       C jueves →
--       C viernes →
--       C sabado →
--       C domingo
--
-- #check @dia.cases_on
-- Da: Π {C : dia → Sort u_1} (n : dia),
--       C lunes →
--       C martes →
--       C miercoles →
--       C jueves →
--       C viernes →
--       C sabado →
--       C domingo

-- ----------------------------------------------------
-- Ejercicio ?. Definir la función
--    numero_del_dia : dia → ℕ
-- tal que (numero_del_dia d) es el número del día de
-- la semana de d. Por ejemplo,
--    numero_del_dia martes = 2
-- ----------------------------------------------------

-- 1ª definición
def numero_del_dia (d : dia) : ℕ :=
dia.rec_on d 1 2 3 4 5 6 7

-- 2ª definición
def numero_del_dia_2 (d : dia) : ℕ :=
dia.cases_on d 1 2 3 4 5 6 7

-- 3ª definición
def numero_del_dia_3 : dia → ℕ :=
λ d, dia.rec 1 2 3 4 5 6 7 d

-- ----------------------------------------------------
-- Ejercicio ?. Definir la función
--    siguiente : dia → dia
-- tal que (siguiente d) es el día siguiente a d. Por
-- ejemplo,
--    siguiente (siguiente jueves) = sabado
-- ----------------------------------------------------

-- 1ª definición
def siguiente : dia → dia :=
λ d, dia.cases_on d martes miercoles jueves viernes sabado domingo lunes

-- 2ª definición
def siguiente_2 (d : dia) : dia :=
dia.cases_on d martes miercoles jueves viernes sabado domingo lunes

-- 3ª definición
def siguiente_3 : dia → dia
| lunes     := martes
| martes    := miercoles
| miercoles := jueves
| jueves    := viernes
| viernes   := sabado
| sabado    := domingo
| domingo   := lunes

-- #reduce siguiente (siguiente jueves)
-- Da: sabado

-- ----------------------------------------------------
-- Ejercicio ?. Definir la función
--    anterior : dia → dia
-- tal que (anterior d) es el día anterior a d. Por
-- ejemplo,
--    siguiente (anterior jueves) = jueves
-- ----------------------------------------------------

-- 1ª definición
def anterior : dia → dia :=
λ d, dia.cases_on d domingo lunes martes miercoles jueves viernes sabado

-- 2ª definición
def anterior_2 (d : dia) : dia :=
dia.cases_on d domingo lunes martes miercoles jueves viernes sabado

-- 3ª definición
def anterior_3 : dia → dia
| lunes     := domingo
| martes    := lunes
| miercoles := martes
| jueves    := miercoles
| viernes   := jueves
| sabado    := viernes
| domingo   := sabado

-- #reduce siguiente (anterior jueves)
-- Da: jueves

-- ----------------------------------------------------
-- Ejercicio ?. Demostrar que
--    siguiente (anterior jueves) = jueves
-- ----------------------------------------------------

example : siguiente (anterior jueves) = jueves :=
rfl

-- ----------------------------------------------------
-- Ejercicio ?. Demostrar que, para cualquier día d,
--    siguiente (anterior d) = d
-- ----------------------------------------------------

-- 1ª demostración
example (d: dia) :
  siguiente (anterior d) = d :=
dia.cases_on d
  (show siguiente (anterior lunes)     = lunes,     from rfl)
  (show siguiente (anterior martes)    = martes,    from rfl)
  (show siguiente (anterior miercoles) = miercoles, from rfl)
  (show siguiente (anterior jueves)    = jueves,    from rfl)
  (show siguiente (anterior viernes)   = viernes,   from rfl)
  (show siguiente (anterior sabado)    = sabado,    from rfl)
  (show siguiente (anterior domingo)   = domingo,   from rfl)

-- 2ª demostración
example (d: dia) :
  siguiente (anterior d) = d :=
dia.cases_on d rfl rfl rfl rfl rfl rfl rfl

-- 3ª demostración
example (d: dia) :
  siguiente (anterior d) = d :=
begin
 apply dia.cases_on d,
 refl,
 refl,
 refl,
 refl,
 refl,
 refl,
 refl,
end

-- 4ª demostración
example (d: dia) :
  siguiente (anterior d) = d :=
by apply dia.cases_on d; refl

-- 5ª demostración
example (d: dia) :
  siguiente (anterior d) = d :=
by apply dia.rec_on d; refl

end dia
