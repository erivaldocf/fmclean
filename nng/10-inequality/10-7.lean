lemma le_zero (a : mynat) (h : a ≤ 0) : a = 0 :=
begin
cases h with c hc,
symmetry at hc,
have h1 := add_right_eq_zero hc,
rw h1,
refl,
end