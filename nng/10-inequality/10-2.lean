lemma le_refl (x : mynat) : x ≤ x :=
begin
rw le_iff_exists_add,
use 0,
rw add_zero,
refl,
end