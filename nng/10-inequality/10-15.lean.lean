lemma lt_aux_one (a b : mynat) : a ≤ b ∧ ¬ (b ≤ a) → succ a ≤ b :=

begin

intro a,
cases a with c hc,
cases c with d hd,
cases d with n hn,
exfalso,
rw add_zero at hd,
apply hc,
rw le_iff_exists_add,
use 0,
rw add_zero,
rw hd,
refl,
rw add_succ at hd,
rw hd,
use n,
rw succ_add,
refl,






end