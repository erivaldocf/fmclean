example (P Q F : Type) : (P → Q) → ((Q → F) → (P → F)) :=

begin

intros f h p,
exact h(f(p)),


end