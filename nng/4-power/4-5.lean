lemma pow_add (a m n : mynat) : a ^ (m + n) = a ^ m * a ^ n :=

begin

induction n with k hk,
rw add_zero,
rw pow_zero,
rw mul_one,
refl,
rw add_succ,
rw pow_succ,
rw pow_succ,
rw hk,
simp,

end