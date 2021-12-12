theorem not_succ_le_self (a : mynat) : ¬ (succ a ≤ a) :=

begin

intro h,
cases h with c hc,
rw succ_eq_add_one at hc,
rw add_assoc at hc,
symmetry at hc,
have h1 := eq_zero_of_add_right_eq_self hc,
rw add_comm at h1,
rw add_one_eq_succ at h1,
have h2 := succ_ne_zero c,
exact h2(h1),

end