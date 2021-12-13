lemma mul_pow (a b n : mynat) : (a * b) ^ n = a ^ n * b ^ n :=
begin
induction n with k hk,
repeat {rw pow_zero},
rw mul_one,
refl,
rw pow_succ,
rw pow_succ,
rw pow_succ,
rw hk,
simp,

end