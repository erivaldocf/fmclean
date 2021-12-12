lemma one_mul (m : mynat) : 1 * m = m :=

begin

induction m with k hk,
rw one_eq_succ_zero,
rw mul_zero,
refl,
rw mul_succ,
rw succ_eq_add_one,
rw hk,
refl,

end