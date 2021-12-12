lemma contrapositive (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) :=

begin

repeat {rw not_iff_imp_false},
intro p,
intro q,
intro f,
apply q,
apply p,
exact f,

end