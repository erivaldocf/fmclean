lemma zero_add (n : mynat) : 0 + n = n :=
begin
induction n with h hk,
rw add_zero,
refl,
rw add_succ,
rw hk,
refl,
end