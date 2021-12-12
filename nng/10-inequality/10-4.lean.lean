lemma zero_le (a : mynat) : 0 ≤ a :=

begin

cases a with b,
refl,
use b + 1,
rw succ_eq_add_one,
rw zero_add,
refl,


end