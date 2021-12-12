theorem le_trans (a b c : mynat) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=

begin


cases hab with b hb,
cases hbc with c hc,
rw le_iff_exists_add,
rw hc,
rw hb,
use b + c,
rw add_assoc,
refl,




end