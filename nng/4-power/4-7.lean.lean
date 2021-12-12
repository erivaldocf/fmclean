lemma pow_pow (a m n : mynat) : (a ^ m) ^ n = a ^ (m * n) :=

begin

induction n with k hk,
rw pow_zero,
rw mul_zero,
rw pow_zero,
refl,
rw pow_succ,
rw mul_succ,
rw hk,
rw pow_add,
refl,

end