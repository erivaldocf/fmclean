lemma add_mul (a b t : mynat) : (a + b) * t = a * t + b * t :=

begin

induction t with k hk,
repeat{rw mul_zero},
rw zero_add,
refl,
rw mul_succ,
rw mul_succ,
rw mul_succ,
rw add_comm,
rw hk,
simp,

end