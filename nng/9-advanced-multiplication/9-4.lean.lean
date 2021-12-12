theorem mul_left_cancel (a b c : mynat) (ha : a ≠ 0) : a * b = a * c → b = c :=


begin

induction c with d hd generalizing b,
intro a,
rw mul_zero at a,
rw mul_eq_zero_iff at a,
cases a with a b,
exfalso,
exact ha(a),
exact b,
intro h,
cases b,
rw mul_zero at h,
symmetry at h,
rw mul_eq_zero_iff at h,
cases h with a,
exfalso,
cases ha(a),
rw h,
refl,
rw mul_succ at h,
rw mul_succ at h,
apply succ_eq_succ_of_eq,
rw add_right_cancel_iff at h,
have h1 := hd(b),
apply h1,
exact h,

end