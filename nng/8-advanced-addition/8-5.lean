theorem add_right_cancel (a t b : mynat) : a + t = b + t → a = b :=
begin
intro h,
induction t with k hk,
repeat {rw add_zero at h},
exact h,
rw hk,
refl,
apply succ_inj,
exact h,
end