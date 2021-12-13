lemma mul_left_comm (a b c : mynat) : a * (b * c) = b * (a * c) :=
begin
induction c with k hk,
rw mul_zero,
rw mul_zero,
rw mul_zero,
refl,
rw mul_succ,
rw mul_succ,
rw mul_add,
rw mul_add,
rw hk,
rw mul_comm,
rw add_comm,
rw mul_comm,
rw add_comm,
refl,

end