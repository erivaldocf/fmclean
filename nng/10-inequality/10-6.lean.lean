theorem le_antisymm (a b : mynat) (hab : a ≤ b) (hba : b ≤ a) : a = b :=

begin

cases hab with c hc,
cases hba with d hd,
rw hc at hd,
rw add_assoc at hd,
symmetry at hd,
have h1 := eq_zero_of_add_right_eq_self hd,
have h2 := add_right_eq_zero h1,
rw h2 at hc,
rw hc,
rw add_zero,
refl,







end