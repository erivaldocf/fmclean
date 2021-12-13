
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro p,
  intro f,
  exact f(p), 
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro h,
  by_cases p : P,
  exact p,
  have h1 : false := h p,
  exfalso,
  exact h1,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  intro h,
  by_cases p : P,
  exact p,
  have h1 : false := h p,
  exfalso,
  exact h1,

  intro p,
  intro f,
  exact f(p), 
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro hpq,
  cases hpq with hp hq,
  right,
  exact hp,
  left,
  exact hq,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro hpq,
  cases hpq with hp hq,
  split,
  exact hq,
  exact hp,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro h,
  cases h with hp hq,
  intro p,
  exfalso,
  apply hp,
  exact p,
  intro p,
  exact hq,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro h,
  intro p,
  cases h with hp hq,
  exfalso,
  apply p,
  exact hp,
  exact hq,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro hpq,
  intro q,
  intro p,
  have hq : Q := hpq p,
  apply q,
  exact hq,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intros hqp p,
  by_cases hq : Q,
  exact hq,
  exfalso,
  have hboom := hqp hq,
  contradiction,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  intros hpq q,
  intro p,
  have hq : Q := hpq p,
  contradiction,

  intros hqp p,
  by_cases hq : Q,
  exact hq,
  have hboom := hqp hq,
  exfalso,
  contradiction,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro hp,
  apply hp,
  right,
  intro p,

  have hpp : P ∨ ¬P,
  left,
  exact p,
  contradiction,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intros hp p,
  have p : P,
  apply hp,
  intro p,
  contradiction,
  contradiction,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intros p q,
  cases p with hp hq,
  cases q with nhp nhq,
  apply nhq,
  contradiction,
  cases q with nhp nhq,
  contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intros p q,
  cases p with hp hq,
  cases q with nhp nhq,
  contradiction,
  contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro npq,
  split,
  intro p,
  have hpq : P ∨ Q,
  left,
  exact p,
  apply npq,
  exact hpq,

  intro q,
  have hpq : P ∨ Q,
  right,
  exact q,
  contradiction,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intros npq p,
  cases npq with np nq,
  cases p with hp hq,
  contradiction,
  contradiction,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro hpq,
  by_contra nqp,
  apply hpq,
  split,
  by_contra np,
  apply nqp,
  right,
  exact np,
  by_contra nq,
  apply nqp,
  left,
  exact nq,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intros nqp,
  intro hpq,
  cases nqp with nq np,
  cases hpq with hp hq,
  contradiction,
  cases hpq with hp hq,
  contradiction,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  exact demorgan_conj P Q,
  exact demorgan_conj_converse P Q,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  exact demorgan_disj P Q,
  exact demorgan_disj_converse P Q,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro hpqr,
  cases hpqr with hp hqr,
  cases hqr with hq hr,
  left,
  split,
  exact hp,
  exact hq,
  right,
  split,
  exact hp,
  exact hr,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro hpqr,
  cases hpqr with hpq hpr,
  cases hpq with hp hq,
  split,
  exact hp,
  left,
  exact hq,
  split,
  cases hpr with hp hr,
  exact hp,
  cases hpr with hp hr,
  right,
  exact hr,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro hpqr,
  cases hpqr with hp hqr,
  split,
  left,
  exact hp,
  left,
  exact hp,
  cases hqr with hq hr,
  split,
  right,
  exact hq,
  right,
  exact hr,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro hpqr,
  cases hpqr with hpq hpr,
  cases hpr with hp hr,
  left,
  exact hp,
  cases hpq with hp hq,
  left,
  exact hp,
  right,
  split,
  exact hq,
  exact hr,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intros hpqr hp hq,
  apply hpqr,
  split,
  exact hp,
  exact hq,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intros hpqr hpq,
  apply hpqr,
  cases hpq with hp hq,
  exact hp,
  cases hpq with hp hq,
  exact hq,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro hp,
  exact hp,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro hp,
  left,
  exact hp,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro hq,
  right,
  exact hq,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro hpq,
  cases hpq with hp hq,
  exact hp,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro hpq,
  cases hpq with hp hq,
  exact hq,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro hp,
  cases hp with p,
  exact p,
  intro p,
  split,
  exact p,
  exact p,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro hpp,
  cases hpp with p hp,
  exact p,
  exact hp,
  intro p,
  left,
  exact p,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intros hpx u pu,
  apply hpx,
  existsi u,
  exact pu,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intros npx hpx,
  cases hpx with u pu,
  apply npx,
  exact pu,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro hpx,
  by_contra npx,
  apply hpx,
  intro u,
  by_contra npu,
  apply npx,
  existsi u,
  exact npu,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intros hpx px,
  cases hpx with u pu,
  have hx := px u,
  contradiction,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  exact demorgan_forall U P,
  exact demorgan_forall_converse U P,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  exact demorgan_exists U P,
  exact demorgan_exists_converse U P,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intros hpx px,
  cases hpx with u hpu,
  have hx := px u,
  contradiction,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intros px hpx,
  cases hpx with u hpu,
  have hx := px u,
  contradiction,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intros hpx u,
  by_contra npu,
  apply hpx,
  existsi u,
  exact npu,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro hpx,
  by_contra npu,
  apply hpx,
  intro u,
  intro pu,
  apply npu,
  existsi u,
  exact pu,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  exact forall_as_neg_exists U P,
  exact forall_as_neg_exists_converse U P,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  exact exists_as_neg_forall U P,
  exact exists_as_neg_forall_converse U P,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro h,
  cases h with u hpq,
  cases hpq with p q,
  split,
  existsi u,
  exact p,
  existsi u,
  exact q,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro h,
  cases h with u hpq,
  cases hpq with p q,
  left,
  existsi u,
  exact p,
  right,
  existsi u,
  exact q,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro h,
  cases h with hpx hqx,
  cases hpx with u hpu,
  split,
  left,
  exact hpu,
  cases hqx with u hqu,
  split,
  right,
  exact hqu,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro h,
  split,
  intro u,
  have hu := h u,
  cases hu with p q,
  exact p,
  intro u,
  have hu := h u,
  cases hu with p q,
  exact q,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro h,
  intro u,
  split,
  cases h with px qx,
  have pu := px u,
  exact pu,
  cases h with px qx,
  have hu := qx u,
  exact hu, 
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro h,
  intro u,
  cases h with px qx,
  have pu := px u,
  left,
  exact pu,
  have hu := qx u,
  right,
  exact hu,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
