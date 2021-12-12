lemma and_or_distrib_left (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) :=

begin

split,
intro h,
cases h with p q,
cases q with q r,
left,
split,
exact p,
exact q,
right,
split,
exact p,
exact r,
intro p,
cases p with q r,
cases q with p q,
split,
exact p,
left,
exact q,
cases r with p r,
split,
exact p,
right,
exact r,


end