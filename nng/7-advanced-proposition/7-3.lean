lemma and_trans (P Q R : Prop) : P ∧ Q → Q ∧ R → P ∧ R :=

begin

intros p q,
split,
cases p with p q,
exact p,
cases q with q r,
exact r,

end