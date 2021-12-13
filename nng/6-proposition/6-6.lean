example (P Q R : Prop) : (P → (Q → R)) → ((P → Q) → (P → R)) :=
begin
intros f h p,
apply f,
exact p,
apply h,
exact p,
end