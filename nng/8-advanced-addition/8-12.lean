theorem add_one_eq_succ (d : mynat) : d + 1 = succ d :=

begin

rw one_eq_succ_zero,
rw add_succ,
rw add_zero,
refl,

end