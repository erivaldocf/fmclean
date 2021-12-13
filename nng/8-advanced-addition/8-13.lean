lemma ne_succ_self (n : mynat) : n ≠ succ n :=
begin
induction n with k hk,
apply zero_ne_succ,
intro h,
symmetry at h,
rw succ_eq_add_one at h,
have h1 := eq_zero_of_add_right_eq_self(h),
rw one_eq_succ_zero at h1,
symmetry at h1,
have h2 := zero_ne_succ 0,
exact h2(h1),
end