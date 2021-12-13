theorem mul_pos (a b : mynat) : a ≠ 0 → b ≠ 0 → a * b ≠ 0 :=
begin
intros h p f,
cases b with x,
rw mul_zero at f,
exact p(f),
rw mul_succ at f,
have h1 := add_left_eq_zero f,
exact h(h1),
end