lemma succ_add (a b : mynat) : succ a + b = succ (a + b) :=
begin
induction b with k hk,
rw add_zero,
rw add_zero,
refl,
rw add_succ,
rw add_succ,
rw hk,
refl,
end