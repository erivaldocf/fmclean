theorem le_total (a b : mynat) : a ≤ b ∨ b ≤ a :=

begin

revert a,
induction b with k hk,
intro a,
right,
exact zero_le a,
intro a,
cases a with c hc,
left,
exact zero_le (succ k),
cases hk c,
left,
apply succ_le_succ,
exact h,
right,
apply succ_le_succ,
exact h,

end