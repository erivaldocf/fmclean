lemma mul_comm (a b : mynat) : a * b = b * a :=

begin

induction b with k hk,
rw mul_zero,
rw zero_mul,
refl,
rw mul_succ,
rw succ_mul,
rw hk,
refl,

end