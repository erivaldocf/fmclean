example (P Q R : Type) : (P → (Q → R)) → ((P → Q) → (P → R)) :=

begin

intros f h p,
have j : Q → R := f p,
exact j(h(p)),

end