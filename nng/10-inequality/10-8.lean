lemma succ_le_succ (a b : mynat) (h : a ≤ b) : succ a ≤ succ b :=

begin

cases h with c hc,
rw le_iff_exists_add,
rw hc,
use c + 0,
rw add_zero,
rw succ_add,
refl,





end