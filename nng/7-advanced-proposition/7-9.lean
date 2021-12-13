lemma contra (P Q : Prop) : (P ∧ ¬ P) → Q :=
begin
intro h,
rw not_iff_imp_false at h,
cases h with p f,
exfalso,
apply f,
exact p,
end