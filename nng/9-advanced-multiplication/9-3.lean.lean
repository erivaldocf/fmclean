theorem mul_eq_zero_iff (a b : mynat): a * b = 0 ↔ a = 0 ∨ b = 0 :=

begin

split,
intro h,
apply eq_zero_or_eq_zero_of_mul_eq_zero,
exact h,
intro a,
cases a with c hc,
rw c,
rw zero_mul,
refl,
rw hc,
rw mul_zero,
refl,




end