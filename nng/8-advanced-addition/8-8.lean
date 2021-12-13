lemma eq_zero_of_add_right_eq_self {a b : mynat} : a + b = a → b = 0 :=
begin
intro h,
induction a with k hk,
rw zero_add at h,
apply h,
rw  succ_add at h,
apply hk,
apply succ_inj,
apply h,
end