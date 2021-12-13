lemma iff_trans (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
intros hpq hqr,
split,
intro p,
apply hqr.1,
apply hpq.1,
exact p,
intro r,
apply hpq.2,
apply hqr.2,
exact r,
end