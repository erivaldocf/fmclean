theorem le_succ (a b : mynat) : a ≤ b → a ≤ (succ b) :=
begin
intro h,
rw le_iff_exists_add at h,
cases h with c hc,
rw le_iff_exists_add,
rw succ_eq_add_one,
use c + 1,
rw hc,
refl,
end