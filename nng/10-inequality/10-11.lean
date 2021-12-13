theorem add_le_add_right {a b : mynat} : a ≤ b → ∀ t, (a + t) ≤ (b + t) :=
begin
intro t,
intro h,
cases t with c hc,
rw hc,
use c,
simp,
end