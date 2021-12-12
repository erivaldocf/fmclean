lemma zero_mul (m : mynat) : 0 * m = 0 :=

begin

induction m with k hk,
rw mul_zero,
refl,
rw mul_succ,
rw hk,
rw add_zero,
refl,


end