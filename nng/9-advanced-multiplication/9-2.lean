theorem eq_zero_or_eq_zero_of_mul_eq_zero (a b : mynat) (h : a * b = 0) :
  a = 0 ∨ b = 0 :=
begin
cases a,
left,
refl,
right,
rw succ_mul at h,
have h1 := add_left_eq_zero h,
exact h1,
end