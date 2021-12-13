theorem succ_eq_add_one (n : mynat) : succ n = n + 1 :=
begin
induction n with k hk,
rw one_eq_succ_zero,
rw zero_add,
refl,
rw succ_add,
rw hk,
refl,
end