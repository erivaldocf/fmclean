theorem add_le_add_left {a b : mynat} (h : a ≤ b) (t : mynat) :
  t + a ≤ t + b :=

begin

cases h with c hc,
cases t with d hd,
rw zero_add,
rw zero_add,
rw hc,
use c,
refl,
rw hc,
use c,
rw add_assoc,
refl,

end