lemma or_symm (P Q : Prop) : P ∨ Q → Q ∨ P :=
begin
intro p,
cases p with p q,
right,
exact p,
left,
exact q,
end