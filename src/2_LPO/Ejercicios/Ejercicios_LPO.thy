-- ----------------------------------------------------
  Ejercicio 1. Demostrar
       ∀x, P x → Q x ⊢ (∀x, P x) → (∀x, Q x)
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_1a:
  "∀x. P x → Q x ⟹ (∀x. P x) → (∀x. Q x)"
by auto

― ‹La demostración estructurada es›
lemma ejercicio_1b:
  assumes "∀x. P x → Q x"
  shows   "(∀x. P x) → (∀x. Q x)"
proof
  assume "∀x. P x"
  show "∀x. Q x"
  proof
    fix a
    have "P a" using ‹∀x. P x› ..
    have "P a → Q a" using assms(1) ..
    thus "Q a" using ‹P a› ..
  qed
qed

― ‹La demostración detallada es›
lemma ejercicio_1c:
  assumes "∀x. P x → Q x"
  shows   "(∀x. P x) → (∀x. Q x)"
proof (rule impI)
  assume "∀x. P x"
  show "∀x. Q x"
  proof (rule allI)
    fix a
    have "P a" using ‹∀x. P x› by (rule allE)
    have "P a → Q a" using assms(1) by (rule allE)
    thus "Q a" using ‹P a› by (rule mp)
  qed
qed

-- ----------------------------------------------------
  Ejercicio 2. Demostrar
       ∃x. ¬(P x) ⊢ ¬(∀x. P x)
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_2a: "∃x. ¬(P x) ⟹ ¬(∀x. P x)"
by auto

― ‹La demostración estructurada es›
lemma ejercicio_2b:
  assumes "∃x. ¬(P x)"
  shows   "¬(∀x. P x)"
proof
  assume "∀x. P x"
  obtain a where "¬(P a)" using assms(1) ..
  have "P a" using ‹∀x. P x› ..
  with ‹¬(P a)› show False ..
qed

― ‹La demostración detallada es›
lemma ejercicio_2c:
  assumes "∃x. ¬(P x)"
  shows   "¬(∀x. P x)"
proof (rule notI)
  assume "∀x. P x"
  obtain a where "¬(P a)" using assms(1) by (rule exE)
  have "P a" using ‹∀x. P x› by (rule allE)
  with ‹¬(P a)› show False by (rule notE)
qed

-- ----------------------------------------------------
  Ejercicio 3. Demostrar
       ∀x. P x ⊢ ∀y. P y
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_3a: "∀x. P x  ⟹ ∀y. P y"
by auto

― ‹La demostración estructurada es›
lemma ejercicio_3b:
  assumes "∀x. P x"
  shows   "∀y. P y"
proof
  fix a
  show "P a" using assms ..
qed

― ‹La demostración estructurada es›
lemma ejercicio_3c:
  assumes "∀x. P x"
  shows   "∀y. P y"
proof (rule allI)
  fix a
  show "P a" using assms by (rule allE)
qed

-- ----------------------------------------------------
  Ejercicio 4. Demostrar
       ∀x. P x → Q x ⊢ (∀x. ¬(Q x)) → (∀x. ¬ (P x))
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_4a:
  "∀x. P x → Q x ⟹ (∀x. ¬(Q x)) → (∀x. ¬ (P x))"
by auto

― ‹La demostración estructurada es›
lemma ejercicio_4b:
  assumes "∀x. P x → Q x"
  shows   "(∀x. ¬(Q x)) → (∀x. ¬ (P x))"
proof
  assume "∀x. ¬(Q x)"
  show "∀x. ¬(P x)"
  proof
    fix a
    show "¬(P a)"
    proof
      assume "P a"
      have "P a → Q a" using assms ..
      hence "Q a" using ‹P a› ..
      have "¬(Q a)" using ‹∀x. ¬(Q x)› ..
      thus False using ‹Q a› ..
    qed
  qed
qed

― ‹La demostración detallada es›
lemma ejercicio_4c:
  assumes "∀x. P x → Q x"
  shows   "(∀x. ¬(Q x)) → (∀x. ¬ (P x))"
proof (rule impI)
  assume "∀x. ¬(Q x)"
  show "∀x. ¬(P x)"
  proof (rule allI)
    fix a
    show "¬(P a)"
    proof
      assume "P a"
      have "P a → Q a" using assms by (rule allE)
      hence "Q a" using ‹P a› by (rule mp)
      have "¬(Q a)" using ‹∀x. ¬(Q x)› by (rule allE)
      thus False using ‹Q a› by (rule notE)
    qed
  qed
qed

-- ----------------------------------------------------
  Ejercicio 5. Demostrar
       ∀x. P x  → ¬(Q x) ⊢ ¬(∃x. P x ∧ Q x)
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_5a:
  "∀x. P x  → ¬(Q x) ⟹ ¬(∃x. P x ∧ Q x)"
by auto

― ‹La demostración estructurada es›
lemma ejercicio_5b:
  assumes "∀x. P x  → ¬(Q x)"
  shows   "¬(∃x. P x ∧ Q x)"
proof
  assume "∃x. P x ∧ Q x"
  then obtain a where "P a ∧ Q a" ..
  hence "P a" ..
  have "P a → ¬(Q a)" using assms ..
  hence "¬(Q a)" using ‹P a› ..
  have "Q a" using ‹P a ∧ Q a› ..
  with ‹¬(Q a)› show False ..
qed

― ‹La demostración estructurada es›
lemma ejercicio_5c:
  assumes "∀x. P x  → ¬(Q x)"
  shows   "¬(∃x. P x ∧ Q x)"
proof (rule notI)
  assume "∃x. P x ∧ Q x"
  then obtain a where "P a ∧ Q a" by (rule exE)
  hence "P a" by (rule conjunct1)
  have "P a → ¬(Q a)" using assms by (rule allE)
  hence "¬(Q a)" using ‹P a› by (rule mp)
  have "Q a" using ‹P a ∧ Q a› by (rule conjunct2)
  with ‹¬(Q a)› show False by (rule notE)
qed

-- ----------------------------------------------------
  Ejercicio 6. Demostrar
       ∀x y. P x y ⊢ ∀u v. P u v
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_6a:
  "∀x y. P x y ⟹ ∀u v. P u v"
by auto

― ‹La demostración estructurada es›
lemma ejercicio_6b:
  assumes "∀x y. P x y"
  shows   "∀u v. P u v"
proof
  fix a
  show "∀v. P a v"
  proof
    fix b
    have "∀y. P a y" using assms ..
    thus "P a b" ..
  qed
qed

― ‹La demostración estructurada simplificada es›
lemma ejercicio_6b2:
  assumes "∀x y. P x y"
  shows   "∀u v. P u v"
proof (rule allI)+
  fix a b
  have "∀y. P a y" using assms ..
  thus "P a b" ..
qed

― ‹La demostración detallada es›
lemma ejercicio_6c:
  assumes "∀x y. P x y"
  shows   "∀u v. P u v"
proof (rule allI)+
  fix a b
  have "∀y. P a y" using assms by (rule allE)
  thus "P a b" by (rule allE)
qed

-- ----------------------------------------------------
  Ejercicio 7. Demostrar
       ∃x y. P x y ⟹ ∃u v. P u v
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_7a:
  "∃x y. P x y ⟹ ∃u v. P u v"
by auto

― ‹La demostración estructurada es›
lemma ejercicio_7b:
  assumes "∃x y. P x y"
  shows   "∃u v. P u v"
proof -
  obtain a where "∃y. P a y" using assms ..
  then obtain b where "P a b" ..
  hence "∃v. P a v" ..
  thus "∃u v. P u v" ..
qed

-- ----------------------------------------------------
  Ejercicio 8. Demostrar
       ∃x. ∀y. P x y ⊢ ∀y. ∃x. P x y
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_8a:
  "∃x. ∀y. P x y ⟹ ∀y. ∃x. P x y"
by auto

― ‹La demostración estructurada es›
lemma ejercicio_8b:
  assumes "∃x. ∀y. P x y"
  shows   "∀y. ∃x. P x y"
proof
  fix b
  obtain a where "∀y. P a y" using assms ..
  hence "P a b" ..
  thus "∃x. P x b" ..
qed

― ‹La demostración detallada es›
lemma ejercicio_8c:
  assumes "∃x. ∀y. P x y"
  shows   "∀y. ∃x. P x y"
proof (rule allI)
  fix b
  obtain a where "∀y. P a y" using assms by (rule exE)
  hence "P a b" by (rule allE)
  thus "∃x. P x b" by (rule exI)
qed

-- ----------------------------------------------------
  Ejercicio 9. Demostrar
       ∃x. P a → Q x ⊢ P a → (∃x. Q x)
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_9a:
  "∃x. P a → Q x ⟹ P a → (∃x. Q x)"
by auto

― ‹La demostración estructurada es›
lemma ejercicio_9b:
  assumes "∃x. P a → Q x"
  shows   "P a → (∃x. Q x)"
proof
  assume "P a"
  obtain b where "P a → Q b" using assms ..
  hence "Q b" using ‹P a› ..
  thus "∃x. Q x" ..
qed

― ‹La demostración detallada es›
lemma ejercicio_9c:
  assumes "∃x. P a → Q x"
  shows   "P a → (∃x. Q x)"
proof (rule impI)
  assume "P a"
  obtain b where "P a → Q b" using assms by (rule exE)
  hence "Q b" using ‹P a› by (rule mp)
  thus "∃x. Q x" by (rule exI)
qed

-- ----------------------------------------------------
  Ejercicio 10. Demostrar
       P a → (∃x. Q x) ⊢ ∃x. P a → Q x
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_10a:
  "P a → (∃x. Q x) ⟹ ∃x. P a → Q x"
by auto

declare [[show_types]]

― ‹La demostración estructurada es›
lemma ejercicio_10b:
  fixes P Q :: "'b ⇒ bool"
  assumes "P a → (∃x. Q x)"
  shows   "∃x. P a → Q x"
proof -
  have "¬(P a) ∨ P a" ..
  thus "∃x. P a → Q x"
  proof
    assume "¬(P a)"
    have "P a → Q a"
    proof
      assume "P a"
      with ‹¬(P a)› show "Q a" ..
    qed
    thus "∃x. P a → Q x" ..
  next
    assume "P a"
    with assms have "∃x. Q x" by (rule mp)
    then obtain b where "Q b" ..
    have "P a → Q b"
    proof
      assume "P a"
      note ‹Q b›
      thus "Q b" .
    qed
    thus "∃x. P a → Q x" ..
  qed
qed

― ‹La demostración detallada es›
lemma ejercicio_10c:
  fixes P Q :: "'b ⇒ bool"
  assumes "P a → (∃x. Q x)"
  shows   "∃x. P a → Q x"
proof -
  have "¬(P a) ∨ P a" by (rule excluded_middle)
  thus "∃x. P a → Q x"
  proof (rule disjE)
    assume "¬(P a)"
    have "P a → Q a"
    proof (rule impI)
      assume "P a"
      with ‹¬(P a)› show "Q a" by (rule notE)
    qed
    thus "∃x. P a → Q x" by (rule exI)
  next
    assume "P a"
    with assms have "∃x. Q x" by (rule mp)
    then obtain b where "Q b" by (rule exE)
    have "P a → Q b"
    proof (rule impI)
      assume "P a"
      note ‹Q b›
      thus "Q b" by this
    qed
    thus "∃x. P a → Q x" by (rule exI)
  qed
qed

-- ----------------------------------------------------
  Ejercicio 11. Demostrar
       (∃x. P x) → Q a ⊢ ∀x. P x → Q a
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_11a:
  "(∃x. P x) → Q a ⟹ ∀x. P x → Q a"
by auto

― ‹La demostración estructurada es›
lemma ejercicio_11b:
  assumes "(∃x. P x) → Q a"
  shows   "∀x. P x → Q a"
proof
  fix b
  show "P b → Q a"
  proof
    assume "P b"
    hence "∃x. P x" ..
    with assms show "Q a" ..
  qed
qed

― ‹La demostración detallada es›
lemma ejercicio_11c:
  assumes "(∃x. P x) → Q a"
  shows   "∀x. P x → Q a"
proof (rule allI)
  fix b
  show "P b → Q a"
  proof (rule impI)
    assume "P b"
    hence "∃x. P x" by (rule exI)
    with assms show "Q a" by (rule mp)
  qed
qed

-- ----------------------------------------------------
  Ejercicio 12. Demostrar
       ∀x. P x → Q a ⊢ ∃ x. P x → Q a
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_12a:
  "∀x. P x → Q a ⟹ ∃x. P x → Q a"
by auto

― ‹La demostración estructurada es›
lemma ejercicio_12b:
  assumes "∀x. P x → Q a"
  shows   "∃x. P x → Q a"
proof -
  have "P b → Q a" using assms ..
  thus "∃x. P x → Q a" ..
qed

― ‹La demostración detallada es›
lemma ejercicio_12c:
  assumes "∀x. P x → Q a"
  shows   "∃x. P x → Q a"
proof -
  have "P b → Q a" using assms by (rule allE)
  thus "∃x. P x → Q a" by (rule exI)
qed

-- ----------------------------------------------------
  Ejercicio 13. Demostrar
       (∀x. P x) ∨ (∀x. Q x) ⊢ ∀x. P x ∨ Q x
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_13a:
  "(∀x. P x) ∨ (∀x. Q x) ⟹ ∀x. P x ∨ Q x"
by auto

― ‹La demostración estructurada es›
lemma ejercicio_13b:
  assumes "(∀x. P x) ∨ (∀x. Q x)"
  shows   "∀x. P x ∨ Q x"
proof
  fix a
  note assms
  thus "P a ∨ Q a"
  proof
    assume "∀x. P x"
    hence "P a" ..
    thus "P a ∨ Q a" ..
  next
    assume "∀x. Q x"
    hence "Q a" ..
    thus "P a ∨ Q a" ..
  qed
qed

― ‹La demostración detallada es›
lemma ejercicio_13c:
  assumes "(∀x. P x) ∨ (∀x. Q x)"
  shows   "∀x. P x ∨ Q x"
proof (rule  allI)
  fix a
  note assms
  thus "P a ∨ Q a"
  proof (rule disjE)
    assume "∀x. P x"
    hence "P a" by (rule allE)
    thus "P a ∨ Q a" by (rule disjI1)
  next
    assume "∀x. Q x"
    hence "Q a" by (rule allE)
    thus "P a ∨ Q a" by (rule disjI2)
  qed
qed

-- ----------------------------------------------------
  Ejercicio 14. Demostrar
       ∃x. P x ∧ Q x ⊢ (∃x. P x) ∧ (∃x. Q x)
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_14a:
  "∃x. P x ∧ Q x ⟹ (∃x. P x) ∧ (∃x. Q x)"
by auto

― ‹La demostración estructurada es›
lemma ejercicio_14b:
  assumes "∃x. P x ∧ Q x"
  shows   "(∃x. P x) ∧ (∃x. Q x)"
proof
  obtain a where "P a ∧ Q a" using assms ..
  hence "P a" ..
  thus "∃x. P x" ..
next
  obtain a where "P a ∧ Q a" using assms ..
  hence "Q a" ..
  thus "∃x. Q x" ..
qed

― ‹La demostración detallada es›
lemma ejercicio_14c:
  assumes "∃x. P x ∧ Q x"
  shows   "(∃x. P x) ∧ (∃x. Q x)"
proof (rule conjI)
  obtain a where "P a ∧ Q a" using assms by (rule exE)
  hence "P a" by (rule conjunct1)
  thus "∃x. P x" by (rule exI)
next
  obtain a where "P a ∧ Q a" using assms by (rule exE)
  hence "Q a" by (rule conjunct2)
  thus "∃x. Q x" by (rule exI)
qed

-- ----------------------------------------------------
  Ejercicio 15. Demostrar
       ∀x y. P y → Q x ⊢ (∃y. P y) → (∀x. Q x)
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_15a:
  "∀x y. P y → Q x ⟹ (∃y. P y) → (∀x. Q x)"
by auto

― ‹La demostración estructurada es›
lemma ejercicio_15b:
  assumes "∀x y. P y → Q x"
  shows   "(∃y. P y) → (∀x. Q x)"
proof
  assume "∃y. P y"
  then obtain b where "P b" ..
  show "∀x. Q x"
  proof
    fix a
    have "∀y. P y → Q a" using assms ..
    hence "P b → Q a" ..
    thus "Q a" using ‹P b› ..
  qed
qed

― ‹La demostración detallada es›
lemma ejercicio_15c:
  assumes "∀x y. P y → Q x"
  shows   "(∃y. P y) → (∀x. Q x)"
proof (rule impI)
  assume "∃y. P y"
  then obtain b where "P b" by (rule exE)
  show "∀x. Q x"
  proof (rule allI)
    fix a
    have "∀y. P y → Q a" using assms by (rule allE)
    hence "P b → Q a" by (rule allE)
    thus "Q a" using ‹P b› by (rule mp)
  qed
qed

-- ----------------------------------------------------
  Ejercicio 16. Demostrar
       ¬(∀x. ¬(P x)) ⊢ ∃x. P x
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_16a:
  "¬(∀x. ¬(P x)) ⟹ ∃x. P x"
by auto

― ‹La demostración estructurada es›
lemma ejercicio_16b:
  assumes "¬(∀x. ¬(P x))"
  shows   "∃x. P x"
proof (rule ccontr)
  assume "¬(∃x. P x)"
  have "∀x. ¬(P x)"
  proof
    fix a
    show "¬(P a)"
    proof
      assume "P a"
      hence "∃x. P x" ..
      with ‹¬(∃x. P x)› show False ..
    qed
  qed
  with assms show False ..
qed

― ‹La demostración detallada es›
lemma ejercicio_16c:
  assumes "¬(∀x. ¬(P x))"
  shows   "∃x. P x"
proof (rule ccontr)
  assume "¬(∃x. P x)"
  have "∀x. ¬(P x)"
  proof (rule allI)
    fix a
    show "¬(P a)"
    proof
      assume "P a"
      hence "∃x. P x" by (rule exI)
      with ‹¬(∃x. P x)› show False by (rule notE)
    qed
  qed
  with assms show False by (rule notE)
qed

-- ----------------------------------------------------
  Ejercicio 17. Demostrar
       ∀x. ¬(P x) ⊢ ¬(∃x. P x)
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_17a:
  "∀x. ¬(P x) ⟹ ¬(∃x. P x)"
by auto

― ‹La demostración estructurada es›
lemma ejercicio_17b:
  assumes "∀x. ¬(P x)"
  shows   "¬(∃x. P x)"
proof
  assume "∃x. P x"
  then obtain a where "P a" ..
  have "¬(P a)" using assms ..
  thus False using ‹P a› ..
qed

― ‹La demostración detallada es›
lemma ejercicio_17c:
  assumes "∀x. ¬(P x)"
  shows   "¬(∃x. P x)"
proof (rule notI)
  assume "∃x. P x"
  then obtain a where "P a" by (rule exE)
  have "¬(P a)" using assms by (rule allE)
  thus False using ‹P a› by (rule notE)
qed

-- ----------------------------------------------------
  Ejercicio 18. Demostrar
       ∃x. P x ⊢ ¬(∀x. ¬(P x))
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_18a:
  "∃x. P x ⟹ ¬(∀x. ¬(P x))"
by auto

― ‹La demostración estructurada es›
lemma ejercicio_18b:
  assumes "∃x. P x"
  shows   "¬(∀x. ¬(P x))"
proof
  assume "∀x. ¬(P x)"
  obtain a where "P a" using assms ..
  have "¬(P a)" using ‹∀x. ¬(P x)› ..
  thus False using ‹P a› ..
qed

― ‹La demostración detallada es›
lemma ejercicio_18c:
  assumes "∃x. P x"
  shows   "¬(∀x. ¬(P x))"
proof (rule notI)
  assume "∀x. ¬(P x)"
  obtain a where "P a" using assms by (rule exE)
  have "¬(P a)" using ‹∀x. ¬(P x)› by (rule allE)
  thus False using ‹P a› by (rule notE)
qed

-- ----------------------------------------------------
  Ejercicio 19. Demostrar
       P a → (∀x. Q x) ⊢ ∀x. P a → Q x
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_19a:
  "P a → (∀x. Q x) ⟹ ∀x. P a → Q x"
by auto

― ‹La demostración estructurada es›
lemma ejercicio_19b:
  assumes "P a → (∀x. Q x)"
  shows   "∀x. P a → Q x"
proof
  fix b
  show "P a → Q b"
  proof
    assume "P a"
    with assms have "∀x. Q x" ..
    thus "Q b" ..
  qed
qed

― ‹La demostración detallada es›
lemma ejercicio_19c:
  assumes "P a → (∀x. Q x)"
  shows   "∀x. P a → Q x"
proof (rule allI)
  fix b
  show "P a → Q b"
  proof (rule impI)
    assume "P a"
    with assms have "∀x. Q x" by (rule mp)
    thus "Q b" by (rule allE)
  qed
qed

-- ----------------------------------------------------
  Ejercicio 20. Demostrar
       {∀x y z. R x y ∧ R y z → R x z,
        ∀x. ¬(R x x)}
       ⊢ ∀x y. R x y → ¬(R y x)
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_20a:
  "⟦∀x y z. R x y ∧ R y z → R x z; ∀x. ¬(R x x)⟧ ⟹ ∀x y. R x y → ¬(R y x)"
by metis

― ‹La demostración estructurada es›
lemma ejercicio_20b:
  assumes "∀x y z. R x y ∧ R y z → R x z"
          "∀x. ¬(R x x)"
  shows   "∀x y. R x y → ¬(R y x)"
proof (rule allI)+
  fix a b
  show "R a b → ¬(R b a)"
  proof
    assume "R a b"
    show "¬(R b a)"
    proof
      assume "R b a"
      show False
      proof -
        have "R a b ∧ R b a" using ‹R a b› ‹R b a› ..
        have "∀y z. R a y ∧ R y z → R a z" using assms(1) ..
        hence "∀z. R a b ∧ R b z → R a z" ..
        hence "R a b ∧ R b a → R a a" ..
        hence "R a a" using ‹R a b ∧ R b a› ..
        have "¬(R a a)" using assms(2) ..
        thus False using ‹R a a› ..
      qed
    qed
  qed
qed

― ‹La demostración detallada es›
lemma ejercicio_20c:
  assumes "∀x y z. R x y ∧ R y z → R x z"
          "∀x. ¬(R x x)"
  shows   "∀x y. R x y → ¬(R y x)"
proof (rule allI)+
  fix a b
  show "R a b → ¬(R b a)"
  proof (rule impI)
    assume "R a b"
    show "¬(R b a)"
    proof (rule notI)
      assume "R b a"
      show False
      proof -
        have "R a b ∧ R b a" using ‹R a b› ‹R b a› by (rule conjI)
        have "∀y z. R a y ∧ R y z → R a z" using assms(1) by (rule allE)
        hence "∀z. R a b ∧ R b z → R a z" by (rule allE)
        hence "R a b ∧ R b a → R a a" by (rule allE)
        hence "R a a" using ‹R a b ∧ R b a› by (rule mp)
        have "¬(R a a)" using assms(2) by (rule allE)
        thus False using ‹R a a› by (rule notE)
      qed
    qed
  qed
qed

-- ----------------------------------------------------
  Ejercicio 21. Demostrar
     {∀x. P x ∨ Q x, ∃x. ¬(Q x), ∀x. R x → ¬(P x)} ⊢ ∃x. ¬(R x)
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_21a:
  "⟦∀x. P x ∨ Q x; ∃x. ¬(Q x); ∀x. R x → ¬(P x)⟧ ⟹ ∃x. ¬(R x)"
by auto

― ‹La demostración estructurada es›
lemma ejercicio_21b:
  assumes "∀x. P x ∨ Q x"
          "∃x. ¬(Q x)"
          "∀x. R x → ¬(P x)"
  shows   "∃x. ¬(R x)"
proof -
  obtain a where "¬(Q a)" using assms(2) ..
  have "P a ∨ Q a" using assms(1) ..
  hence "P a"
  proof
    assume "P a"
    thus "P a" .
  next
    assume "Q a"
    with ‹¬(Q a)› show "P a" ..
  qed
  hence "¬¬(P a)" by (rule notnotI)
  have "R a → ¬(P a)" using assms(3) ..
  hence "¬(R a)" using ‹¬¬(P a)› by (rule mt)
  thus "∃x. ¬(R x)" ..
qed

― ‹La demostración detallada es›
lemma ejercicio_21c:
  assumes "∀x. P x ∨ Q x"
          "∃x. ¬(Q x)"
          "∀x. R x → ¬(P x)"
  shows   "∃x. ¬(R x)"
proof -
  obtain a where "¬(Q a)" using assms(2) by (rule exE)
  have "P a ∨ Q a" using assms(1) by (rule allE)
  hence "P a"
  proof (rule disjE)
    assume "P a"
    thus "P a" by this
  next
    assume "Q a"
    with ‹¬(Q a)› show "P a" by (rule notE)
  qed
  hence "¬¬(P a)" by (rule notnotI)
  have "R a → ¬(P a)" using assms(3) by (rule allE)
  hence "¬(R a)" using ‹¬¬(P a)› by (rule mt)
  thus "∃x. ¬(R x)" by (rule exI)
qed

-- ----------------------------------------------------
  Ejercicio 22. Demostrar
     {∀x. P x → Q x ∨ R x, ¬(∃x. P x ∧ R x)} ⊢ ∀x. P x → Q x
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_22a:
  "⟦∀x. P x → Q x ∨ R x; ¬(∃x. P x ∧ R x)⟧ ⟹ ∀x. P x → Q x"
by auto

― ‹La demostración estructurada es›
lemma ejercicio_22b:
  assumes "∀x. P x → Q x ∨ R x"
          "¬(∃x. P x ∧ R x)"
  shows   "∀x. P x → Q x"
proof
  fix a
  show "P a → Q a"
  proof
    assume "P a"
    have "P a → Q a ∨ R a" using assms(1) ..
    hence "Q a ∨ R a" using ‹P a› ..
    thus "Q a"
    proof
      assume "Q a"
      thus "Q a" .
    next
      assume "R a"
      with ‹P a› have "P a ∧ R a" ..
      hence "∃x. P x ∧ R x" ..
      with assms(2) show "Q a" ..
    qed
  qed
qed

― ‹La demostración detallada es›
lemma ejercicio_22c:
  assumes "∀x. P x → Q x ∨ R x"
          "¬(∃x. P x ∧ R x)"
  shows   "∀x. P x → Q x"
proof (rule allI)
  fix a
  show "P a → Q a"
  proof (rule impI)
    assume "P a"
    have "P a → Q a ∨ R a" using assms(1) by (rule allE)
    hence "Q a ∨ R a" using ‹P a› by (rule mp)
    thus "Q a"
    proof (rule disjE)
      assume "Q a"
      thus "Q a" by this
    next
      assume "R a"
      with ‹P a› have "P a ∧ R a" by (rule conjI)
      hence "∃x. P x ∧ R x" by (rule exI)
      with assms(2) show "Q a" by (rule notE)
    qed
  qed
qed

-- ----------------------------------------------------
  Ejercicio 23. Demostrar
     ∃x y. R x y ∨ R y x ⊢ ∃x y. R x y
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_23a:
  "∃x y. R x y ∨ R y x ⟹ ∃x y. R x y"
by auto

― ‹La demostración estructurada es›
lemma ejercicio_23b:
  assumes "∃x y. R x y ∨ R y x"
  shows   "∃x y. R x y"
proof -
  obtain a where "∃y. R a y ∨ R y a" using assms ..
  then obtain b where "R a b ∨ R b a" ..
  thus "∃x y. R x y"
  proof
    assume "R a b"
    hence "∃y. R a y" ..
    thus "∃ x y. R x y" ..
  next
    assume "R b a"
    hence "∃y. R b y" ..
    thus "∃ x y. R x y" ..
  qed
qed

― ‹La demostración detallada es›
lemma ejercicio_23c:
  assumes "∃x y. R x y ∨ R y x"
  shows   "∃x y. R x y"
proof -
  obtain a where "∃y. R a y ∨ R y a" using assms by (rule exE)
  then obtain b where "R a b ∨ R b a" by (rule exE)
  thus "∃x y. R x y"
  proof (rule disjE)
    assume "R a b"
    hence "∃y. R a y" by (rule exI)
    thus "∃ x y. R x y" by (rule exI)
  next
    assume "R b a"
    hence "∃y. R b y" by (rule exI)
    thus "∃ x y. R x y" by (rule exI)
  qed
qed

-- ----------------------------------------------------
  Ejercicio 24. Demostrar
       (∃x. ∀y. P x y) → (∀y. ∃x. P x y)
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_24a: "(∃x. ∀y. P x y) → (∀y. ∃x. P x y)"
by auto

― ‹La demostración estructurada es›
lemma ejercicio_24b: "(∃x. ∀y. P x y) → (∀y. ∃x. P x y)"
proof
  assume "∃x. ∀y. P x y"
  then obtain a where "∀y. P a y" ..
  show "∀y. ∃x. P x y"
  proof
    fix b
    have "P a b" using ‹∀y. P a y› ..
    thus "∃x. P x b" ..
  qed
qed

― ‹La demostración detallada es›
lemma ejercicio_24c: "(∃x. ∀y. P x y) → (∀y. ∃x. P x y)"
proof (rule impI)
  assume "∃x. ∀y. P x y"
  then obtain a where "∀y. P a y" by (rule exE)
  show "∀y. ∃x. P x y"
  proof (rule allI)
    fix b
    have "P a b" using ‹∀y. P a y› by (rule allE)
    thus "∃x. P x b" by (rule exI)
  qed
qed

-- ----------------------------------------------------
  Ejercicio 25. Demostrar
       (∀x. P x → Q) ⟷ ((∃x. P x) → Q)
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_25a: "(∀x. P x → Q) ⟷ ((∃x. P x) → Q)"
by auto

― ‹La demostración estructurada es›
lemma ejercicio_25b: "(∀x. P x → Q) ⟷ ((∃x. P x) → Q)"
proof
  assume "∀x. P x → Q"
  show "(∃x. P x) → Q"
  proof
    assume "∃x. P x"
    then obtain a where "P a" ..
    have "P a → Q" using ‹∀x. P x → Q› ..
    thus "Q" using ‹P a› ..
  qed
next
  assume "(∃x. P x) → Q"
  show "∀x. P x → Q"
  proof
    fix b
    show "P b → Q"
    proof
      assume "P b"
      hence "∃x. P x" ..
      with ‹(∃x. P x) → Q› show "Q" ..
    qed
  qed
qed

― ‹La demostración detallada es›
lemma ejercicio_25c: "(∀x. P x → Q) ⟷ ((∃x. P x) → Q)"
proof (rule iffI)
  assume "∀x. P x → Q"
  show "(∃x. P x) → Q"
  proof (rule impI)
    assume "∃x. P x"
    then obtain a where "P a" by (rule exE)
    have "P a → Q" using ‹∀x. P x → Q› by (rule allE)
    thus "Q" using ‹P a› by (rule mp)
  qed
next
  assume "(∃x. P x) → Q"
  show "∀x. P x → Q"
  proof (rule allI)
    fix b
    show "P b → Q"
    proof (rule impI)
      assume "P b"
      hence "∃x. P x" by (rule exI)
      with ‹(∃x. P x) → Q› show "Q" by (rule mp)
    qed
  qed
qed

-- ----------------------------------------------------
  Ejercicio 26. Demostrar
       ((∀x. P x) ∧ (∀x. Q x)) ⟷ (∀x. P x ∧ Q x)
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_26a: "((∀x. P x) ∧ (∀x. Q x)) ⟷ (∀x. P x ∧ Q x)"
by auto

― ‹La demostración estructurada es›
lemma ejercicio_26b: "((∀x. P x) ∧ (∀x. Q x)) ⟷ (∀x. P x ∧ Q x)"
proof
  assume "(∀x. P x) ∧ (∀x. Q x)"
  show "∀x. P x ∧ Q x"
  proof
    fix a
    have "∀x. P x" using ‹(∀x. P x) ∧ (∀x. Q x)› ..
    have "∀x. Q x" using ‹(∀x. P x) ∧ (∀x. Q x)› ..
    hence "Q a" ..
    have "P a" using ‹∀x. P x› ..
    thus "P a ∧ Q a" using ‹Q a› ..
  qed
next
  assume "∀x. P x ∧ Q x"
  have "∀x. P x"
  proof
    fix a
    have "P a ∧ Q a" using ‹∀x. P x ∧ Q x› ..
    thus "P a" ..
  qed
  moreover have "∀x. Q x"
  proof
    fix a
    have "P a ∧ Q a" using ‹∀x. P x ∧ Q x› ..
    thus "Q a" ..
  qed
  ultimately show "(∀x. P x) ∧ (∀x. Q x)" ..
qed

― ‹La demostración detallada es›
lemma ejercicio_26c: "((∀x. P x) ∧ (∀x. Q x)) = (∀x. P x ∧ Q x)"
proof (rule iffI)
  assume "(∀x. P x) ∧ (∀x. Q x)"
  show "∀x. P x ∧ Q x"
  proof (rule allI)
    fix a
    have "∀x. P x" using ‹(∀x. P x) ∧ (∀x. Q x)› by (rule conjunct1)
    have "∀x. Q x" using ‹(∀x. P x) ∧ (∀x. Q x)› by (rule conjunct2)
    hence "Q a" by (rule allE)
    have "P a" using ‹∀x. P x› by (rule allE)
    thus "P a ∧ Q a" using ‹Q a› by (rule conjI)
  qed
next
  assume "∀x. P x ∧ Q x"
  have "∀x. P x"
  proof (rule allI)
    fix a
    have "P a ∧ Q a" using ‹∀x. P x ∧ Q x› by (rule allE)
    thus "P a" by (rule conjunct1)
  qed
  moreover have "∀x. Q x"
  proof (rule allI)
    fix a
    have "P a ∧ Q a" using ‹∀x. P x ∧ Q x› by (rule allE)
    thus "Q a" by (rule conjunct2)
  qed
  ultimately show "(∀x. P x) ∧ (∀x. Q x)" by (rule conjI)
qed

-- ----------------------------------------------------
  Ejercicio 27. Demostrar o refutar
       ((∀x. P x) ∨ (∀x. Q x)) ⟷ (∀x. P x ∨ Q x)
-- ----------------------------------------------------

lemma ejercicio_27: "((∀x. P x) ∨ (∀x. Q x)) ⟷ (∀x. P x ∨ Q x)"
oops

(*
Auto Quickcheck found a counterexample:
P = {a\<^isub>1}
Q = {a\<^isub>2}
*)

-- ----------------------------------------------------
  Ejercicio 28. Demostrar o refutar
       ((∃x. P x) ∨ (∃x. Q x)) ⟷ (∃x. P x ∨ Q x)
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_28a:
  "((∃x. P x) ∨ (∃x. Q x)) ⟷ (∃x. P x ∨ Q x)"
by auto

― ‹La demostración estructurada es›
lemma ejercicio_28b:
  "((∃x. P x) ∨ (∃x. Q x)) ⟷ (∃x. P x ∨ Q x)"
proof
  assume "(∃x. P x) ∨ (∃x. Q x)"
  thus "∃x. P x ∨ Q x"
  proof
    assume "∃x. P x"
    then obtain a where "P a" ..
    hence "P a ∨ Q a" ..
    thus "∃x. P x ∨ Q x" ..
  next
    assume "∃x. Q x"
    then obtain a where "Q a" ..
    hence "P a ∨ Q a" ..
    thus "∃x. P x ∨ Q x" ..
  qed
next
  assume "∃x. P x ∨ Q x"
  then obtain a where "P a ∨ Q a" ..
  thus "(∃x. P x) ∨ (∃x. Q x)"
  proof
    assume "P a"
    hence "∃x. P x" ..
    thus "(∃x. P x) ∨ (∃x. Q x)" ..
  next
    assume "Q a"
    hence "∃x. Q x" ..
    thus "(∃x. P x) ∨ (∃x. Q x)" ..
  qed
qed

― ‹La demostración detallada es›
lemma ejercicio_28c:
  "((∃x. P x) ∨ (∃x. Q x)) ⟷ (∃x. P x ∨ Q x)"
proof (rule iffI)
  assume "(∃x. P x) ∨ (∃x. Q x)"
  thus "∃x. P x ∨ Q x"
  proof (rule disjE)
    assume "∃x. P x"
    then obtain a where "P a" by (rule exE)
    hence "P a ∨ Q a" by (rule disjI1)
    thus "∃x. P x ∨ Q x" by (rule exI)
  next
    assume "∃x. Q x"
    then obtain a where "Q a" by (rule exE)
    hence "P a ∨ Q a" by (rule disjI2)
    thus "∃x. P x ∨ Q x" by (rule exI)
  qed
next
  assume "∃x. P x ∨ Q x"
  then obtain a where "P a ∨ Q a" by (rule exE)
  thus "(∃x. P x) ∨ (∃x. Q x)"
  proof (rule disjE)
    assume "P a"
    hence "∃x. P x" by (rule exI)
    thus "(∃x. P x) ∨ (∃x. Q x)" by (rule disjI1)
  next
    assume "Q a"
    hence "∃x. Q x" by (rule exI)
    thus "(∃x. P x) ∨ (∃x. Q x)" by (rule disjI2)
  qed
qed

-- ----------------------------------------------------
  Ejercicio 29. Demostrar o refutar
       (∀x. ∃y. P x y) → (∃y. ∀x. P x y)
-- ----------------------------------------------------

lemma ejercicio_29:
  "(∀x. ∃y. P x y) → (∃y. ∀x. P x y)"
quickcheck
(*
Quickcheck found a counterexample:

P = (λx. undefined)(a\<^isub> := {b}, b := {a})
*)
oops

-- ----------------------------------------------------
  Ejercicio 30. Demostrar o refutar
       (¬(∀x. P x)) ⟷ (∃x. ¬P x)
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_30a:
  "(¬(∀x. P x)) ⟷ (∃x. ¬P x)"
by auto

― ‹La demostración estructurada es›
lemma ejercicio_30b:
  "(¬(∀x. P x)) ⟷ (∃x. ¬P x)"
proof
  assume "¬(∀x. P x)"
  show "∃x. ¬P x"
  proof (rule ccontr)
    assume "¬(∃x. ¬P x)"
    have "∀x. P x"
    proof
      fix a
      show "P a"
      proof (rule ccontr)
        assume "¬P a"
        hence "∃x. ¬P x" ..
        with ‹¬(∃x. ¬P x)› show False ..
      qed
    qed
    with ‹¬(∀x. P x)› show False ..
  qed
next
  assume "∃x. ¬P x"
  then obtain a where "¬P a" ..
  show "¬(∀x. P x)"
  proof
    assume "∀x. P x"
    hence "P a" ..
    with ‹¬P a› show False ..
  qed
qed

― ‹La demostración detallada es›
lemma ejercicio_30c:
  "(¬(∀x. P x)) ⟷ (∃x. ¬P x)"
proof (rule iffI)
  assume "¬(∀x. P x)"
  show "∃x. ¬P x"
  proof (rule ccontr)
    assume "¬(∃x. ¬P x)"
    have "∀x. P x"
    proof (rule allI)
      fix a
      show "P a"
      proof (rule ccontr)
        assume "¬P a"
        hence "∃x. ¬P x" by (rule exI)
        with ‹¬(∃x. ¬P x)› show False by (rule notE)
      qed
    qed
    with ‹¬(∀x. P x)› show False by (rule notE)
  qed
next
  assume "∃x. ¬P x"
  then obtain a where "¬P a" by (rule exE)
  show "¬(∀x. P x)"
  proof (rule notI)
    assume "∀x. P x"
    hence "P a" by (rule allE)
    show False using ‹¬P a› ‹P a› by (rule notE)
  qed
qed

section ‹Ejercicios sobre igualdad›

-- ----------------------------------------------------
  Ejercicio 31. Demostrar o refutar
       P a ⟹ ∀x. x = a → P x
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_31a:
  "P a ⟹ ∀x. x = a → P x"
by auto

― ‹La demostración estructurada es›
lemma ejercicio_31b:
  assumes "P a"
  shows   "∀x. x = a → P x"
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
  shows   "∀x. x = a → P x"
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
     {∀x. P a x x,
      ∀x y z. P x y z → P (f x) y (f z)}
     ⊢ P (f a) a (f a)
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_33a:
  "⟦∀x. P a x x; ∀x y z. P x y z → P (f x) y (f z)⟧ ⟹ P (f a) a (f a)"
by auto

― ‹La demostración estructura es›
lemma ejercicio_33b:
  assumes "∀x. P a x x"
          "∀x y z. P x y z → P (f x) y (f z)"
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
  assumes "∀x. P a x x"
          "∀x y z. P x y z → P (f x) y (f z)"
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
     {∀x. P a x x,
      ∀x y z. P x y z → P (f x) y (f z)⟧
     ⊢ ∃z. P (f a) z (f (f a))
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_34a:
  "⟦∀x. P a x x; ∀x y z. P x y z → P (f x) y (f z)⟧
   ⟹ ∃z. P (f a) z (f (f a))"
by metis

― ‹La demostración estructura es›
lemma ejercicio_34b:
  assumes "∀x. P a x x"
          "∀x y z. P x y z → P (f x) y (f z)"
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
  assumes "∀x. P a x x"
          "∀x y z. P x y z → P (f x) y (f z)"
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
      ∀x y. Q x y → Q (s x) (s y)}
     ⊢ ∃z. Qa z ∧ Q z (s (s a))
-- ----------------------------------------------------

― ‹La demostración automática es›
lemma ejercicio_35a:
  "⟦∀y. Q a y; ∀x y. Q x y → Q (s x) (s y)⟧ ⟹ ∃z. Q a z ∧ Q z (s (s a))"
by auto

― ‹La demostración estructura es›
lemma ejercicio_35b:
  assumes "∀y. Q a y"
          "∀x y. Q x y → Q (s x) (s y)"
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
          "∀x y. Q x y → Q (s x) (s y)"
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
