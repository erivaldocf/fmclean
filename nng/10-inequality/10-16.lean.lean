lemma lt_aux_two (a b : mynat) : succ a ≤ b → a ≤ b ∧ ¬ (b ≤ a) :=

begin

intro h,
split,
cases h with c hc,
cases a with x,
exact zero_le b,
rw succ_eq_add_one at hc,
rw le_iff_exists_add,
use c + 1,
rw hc,
rw add_assoc,
rw add_comm c,
refl,

intro a,
cases h with d hd,
rw hd at a,
cases a with n hn,
rw succ_eq_add_one at hn,
rw add_assoc at hn,
rw add_assoc at hn,
symmetry at hn,
have h1 := eq_zero_of_add_right_eq_self hn,
symmetry at h1,
rw add_comm at h1,
rw add_one_eq_succ at h1,
symmetry at h1,
have h2 := succ_ne_zero (d + n),
exact h2(h1),

end