-- ----------------------------------------------------
  Ejercicio 30. Demostrar o refutar
       (¬(∀ x. P x)) ⟷ (∃x. ¬P x)
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_30a:
  "(¬(∀ x. P x)) ⟷ (∃x. ¬P x)"
by auto

― ‹La demostración estructurada es›
lemma ejercicio_30b:
  "(¬(∀ x. P x)) ⟷ (∃x. ¬P x)"
proof
  assume "¬(∀ x. P x)"
  show "∃x. ¬P x"
  proof (rule ccontr)
    assume "¬(∃x. ¬P x)"
    have "∀ x. P x"
    proof
      fix a
      show "P a"
      proof (rule ccontr)
        assume "¬P a"
        hence "∃x. ¬P x" ..
        with ‹¬(∃x. ¬P x)› show False ..
      qed
    qed
    with ‹¬(∀ x. P x)› show False ..
  qed
next
  assume "∃x. ¬P x"
  then obtain a where "¬P a" ..
  show "¬(∀ x. P x)"
  proof
    assume "∀ x. P x"
    hence "P a" ..
    with ‹¬P a› show False ..
  qed
qed

― ‹La demostración detallada es›
lemma ejercicio_30c:
  "(¬(∀ x. P x)) ⟷ (∃x. ¬P x)"
proof (rule iffI)
  assume "¬(∀ x. P x)"
  show "∃x. ¬P x"
  proof (rule ccontr)
    assume "¬(∃x. ¬P x)"
    have "∀ x. P x"
    proof (rule allI)
      fix a
      show "P a"
      proof (rule ccontr)
        assume "¬P a"
        hence "∃x. ¬P x" by (rule exI)
        with ‹¬(∃x. ¬P x)› show False by (rule notE)
      qed
    qed
    with ‹¬(∀ x. P x)› show False by (rule notE)
  qed
next
  assume "∃x. ¬P x"
  then obtain a where "¬P a" by (rule exE)
  show "¬(∀ x. P x)"
  proof (rule notI)
    assume "∀ x. P x"
    hence "P a" by (rule allE)
    show False using ‹¬P a› ‹P a› by (rule notE)
  qed
qed

section ‹Ejercicios sobre igualdad›

-- ----------------------------------------------------
  Ejercicio 31. Demostrar o refutar
       P a ⟹ ∀ x. x = a → P x
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_31a:
  "P a ⟹ ∀ x. x = a → P x"
by auto

― ‹La demostración estructurada es›
lemma ejercicio_31b:
  assumes "P a"
  shows   "∀ x. x = a → P x"
proof
  fix b
  show "b = a → P b"
  proof
    assume "b = a"
    thus "P b" using assms by (rule ssubst)
  qed
qed

― ‹La demostración detallada es›
lemma ejercicio_31c:
  assumes "P a"
  shows   "∀ x. x = a → P x"
proof (rule allI)
  fix b
  show "b = a → P b"
  proof (rule impI)
    assume "b = a"
    thus "P b" using assms by (rule ssubst)
  qed
qed

-- ----------------------------------------------------
  Ejercicio 32. Demostrar o refutar
       ∃x y. R x y ∨ R y x; ¬(∃x. R x x)⟧ ⟹ ∃x y. x ≠ y
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_32a:
  fixes R :: "'c ⇒ 'c ⇒ bool"
  assumes "∃x y. R x y ∨ R y x"
          "¬(∃x. R x x)"
  shows   "∃(x::'c) y. x ≠ y"
using assms
by metis

― ‹La demostración estructurada es›
lemma ejercicio_32b:
  fixes R :: "'c ⇒ 'c ⇒ bool"
  assumes "∃x y. R x y ∨ R y x"
          "¬(∃x. R x x)"
  shows   "∃(x::'c) y. x ≠ y"
proof -
  obtain a where "∃y. R a y ∨ R y a" using assms(1) ..
  then obtain b where "R a b ∨ R b a" ..
  hence "a ≠ b"
  proof
    assume "R a b"
    show "a ≠ b"
    proof
      assume "a = b"
      hence "R b b" using ‹R a b› by (rule subst)
      hence "∃x. R x x" ..
      with assms(2) show False ..
    qed
  next
    assume "R b a"
    show "a ≠ b"
    proof
      assume "a = b"
      hence "R a a" using ‹R b a› by (rule ssubst)
      hence "∃x. R x x" ..
      with assms(2) show False ..
    qed
  qed
  hence "∃y. a ≠ y" ..
  thus "∃(x::'c) y. x ≠ y" ..
qed

― ‹La demostración detallada es›
lemma ejercicio_32c:
  fixes R :: "'c ⇒ 'c ⇒ bool"
  assumes "∃x y. R x y ∨ R y x"
          "¬(∃x. R x x)"
  shows   "∃(x::'c) y. x ≠ y"
proof -
  obtain a where "∃y. R a y ∨ R y a" using assms(1) by (rule exE)
  then obtain b where "R a b ∨ R b a" by (rule exE)
  hence "a ≠ b"
  proof (rule disjE)
    assume "R a b"
    show "a ≠ b"
    proof (rule notI)
      assume "a = b"
      hence "R b b" using ‹R a b› by (rule subst)
      hence "∃x. R x x" by (rule exI)
      with assms(2) show False by (rule notE)
    qed
  next
    assume "R b a"
    show "a ≠ b"
    proof (rule notI)
      assume "a = b"
      hence "R a a" using ‹R b a› by (rule ssubst)
      hence "∃x. R x x" by (rule exI)
      with assms(2) show False by (rule notE)
    qed
  qed
  hence "∃y. a ≠ y" by (rule exI)
  thus "∃(x::'c) y. x ≠ y" by (rule exI)
qed

-- ----------------------------------------------------
  Ejercicio 33. Demostrar o refutar
     {∀ x. P a x x,
      ∀ x y z. P x y z → P (f x) y (f z)}
     ⊢ P (f a) a (f a)
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_33a:
  "⟦∀ x. P a x x; ∀ x y z. P x y z → P (f x) y (f z)⟧ ⟹ P (f a) a (f a)"
by auto

― ‹La demostración estructura es›
lemma ejercicio_33b:
  assumes "∀ x. P a x x"
          "∀ x y z. P x y z → P (f x) y (f z)"
  shows   "P (f a) a (f a)"
proof -
  have "P a a a" using assms(1) ..
  have "∀y z. P a y z → P (f a) y (f z)" using assms(2) ..
  hence "∀z. P a a z → P (f a) a (f z)" ..
  hence "P a a a → P (f a) a (f a)" ..
  thus "P (f a) a (f a)" using ‹P a a a› ..
qed

― ‹La demostración detallada es›
lemma ejercicio_33c:
  assumes "∀ x. P a x x"
          "∀ x y z. P x y z → P (f x) y (f z)"
  shows   "P (f a) a (f a)"
proof -
  have "P a a a" using assms(1) by (rule allE)
  have "∀y z. P a y z → P (f a) y (f z)" using assms(2) by (rule allE)
  hence "∀z. P a a z → P (f a) a (f z)" by (rule allE)
  hence "P a a a → P (f a) a (f a)" by (rule allE)
  thus "P (f a) a (f a)" using ‹P a a a› by (rule mp)
qed

-- ----------------------------------------------------
  Ejercicio 34. Demostrar o refutar
     {∀ x. P a x x,
      ∀ x y z. P x y z → P (f x) y (f z)⟧
     ⊢ ∃z. P (f a) z (f (f a))
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_34a:
  "⟦∀ x. P a x x; ∀ x y z. P x y z → P (f x) y (f z)⟧
   ⟹ ∃z. P (f a) z (f (f a))"
by metis

― ‹La demostración estructura es›
lemma ejercicio_34b:
  assumes "∀ x. P a x x"
          "∀ x y z. P x y z → P (f x) y (f z)"
  shows   "∃z. P (f a) z (f (f a))"
proof -
  have "P a (f a) (f a)" using assms(1) ..
  have "∀y z. P a y z → P (f a) y (f z)" using assms(2) ..
  hence "∀z. P a (f a) z → P (f a) (f a) (f z)" ..
  hence "P a (f a) (f a) → P (f a) (f a) (f (f a))" ..
  hence "P (f a) (f a) (f (f a))" using ‹P a (f a) (f a)› ..
  thus "∃z. P (f a) z (f (f a))" ..
qed

― ‹La demostración detallada es›
lemma ejercicio_34c:
  assumes "∀ x. P a x x"
          "∀ x y z. P x y z → P (f x) y (f z)"
  shows   "∃z. P (f a) z (f (f a))"
proof -
  have "P a (f a) (f a)" using assms(1) by (rule allE)
  have "∀y z. P a y z → P (f a) y (f z)" using assms(2) by (rule allE)
  hence "∀z. P a (f a) z → P (f a) (f a) (f z)" by (rule allE)
  hence "P a (f a) (f a) → P (f a) (f a) (f (f a))" by (rule allE)
  hence "P (f a) (f a) (f (f a))" using ‹P a (f a) (f a)› by (rule mp)
  thus "∃z. P (f a) z (f (f a))" by (rule exI)
qed

-- ----------------------------------------------------
  Ejercicio 35. Demostrar o refutar
     {∀y. Q a y,
      ∀ x y. Q x y → Q (s x) (s y)}
     ⊢ ∃z. Qa z ∧ Q z (s (s a))
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_35a:
  "⟦∀y. Q a y; ∀ x y. Q x y → Q (s x) (s y)⟧ ⟹ ∃z. Q a z ∧ Q z (s (s a))"
by auto

― ‹La demostración estructura es›
lemma ejercicio_35b:
  assumes "∀y. Q a y"
          "∀ x y. Q x y → Q (s x) (s y)"
  shows   "∃z. Q a z ∧ Q z (s (s a))"
proof -
  have "Q a (s a)" using assms(1) ..
  have "∀y. Q a y → Q (s a) (s y)" using assms(2) ..
  hence "Q a (s a) → Q (s a) (s (s a))" ..
  hence "Q (s a) (s (s a))" using ‹Q a (s a)› ..
  with ‹Q a (s a)› have "Q a (s a) ∧ Q (s a) (s (s a))" ..
  thus "∃z. Q a z ∧ Q z (s (s a))" ..
qed

― ‹La demostración detallada es›
lemma ejercicio_35c:
  assumes "∀y. Q a y"
          "∀ x y. Q x y → Q (s x) (s y)"
  shows   "∃z. Q a z ∧ Q z (s (s a))"
proof -
  have "Q a (s a)" using assms(1) by (rule allE)
  have "∀y. Q a y → Q (s a) (s y)" using assms(2) by (rule allE)
  hence "Q a (s a) → Q (s a) (s (s a))" by (rule allE)
  hence "Q (s a) (s (s a))" using ‹Q a (s a)› by (rule mp)
  with ‹Q a (s a)› have "Q a (s a) ∧ Q (s a) (s (s a))" by (rule conjI)
  thus "∃z. Q a z ∧ Q z (s (s a))" by (rule exI)
qed

-- ----------------------------------------------------
  Ejercicio 36. Demostrar o refutar
     {x = f x, odd (f x)} ⊢ odd x
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_36a:
  "⟦x = f x; odd (f x)⟧ ⟹ odd x"
by auto

― ‹La demostración semiautomática es›
lemma ejercicio_36b:
  "⟦x = f x; odd (f x)⟧ ⟹ odd x"
by (rule ssubst)

― ‹La demostración estructurada es›
lemma ejercicio_36c:
  assumes "x = f x"
          "odd (f x)"
  shows   "odd x"
proof -
  show "odd x" using assms by (rule ssubst)
qed

-- ----------------------------------------------------
  Ejercicio 37. Demostrar o refutar
     {x = f x, triple (f x) (f x) x} ⊢ triple x x x
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_37a:
  "⟦x = f x; triple (f x) (f x) x⟧ ⟹ triple x x x"
by auto

― ‹La demostración semiautomática es›
lemma ejercicio_37b:
  "⟦x = f x; triple (f x) (f x) x⟧ ⟹ triple x x x"
by (rule ssubst)

― ‹La demostración estructurada es›
lemma ejercicio_37c:
  assumes "x = f x"
          "triple (f x) (f x) x"
  shows   "triple x x x"
proof -
  show "triple x x x" using assms by (rule ssubst)
qed

end
