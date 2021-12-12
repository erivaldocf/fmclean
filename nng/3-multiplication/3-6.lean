lemma succ_mul (a b : mynat) : succ a * b = a * b + b :=

begin

induction b with k hk,
rw mul_zero,
rw add_zero,
rw mul_zero,
refl,
rw mul_succ,
rw add_succ,
rw hk,
rw mul_succ,
rw add_succ,
rw add_right_comm,
refl,

end