lemma iff_trans (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
intro h,
cases h with hpq hqp,
intro qr,
split,
cases qr with q r,
intro p,
apply q,
apply hpq,
exact p,
cases qr with q r,
intro x,
apply hqp,
apply r,
exact x,
end