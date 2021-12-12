theorem add_left_cancel (t a b : mynat) : t + a = t + b → a = b :=

begin

rw add_comm t,
rw add_comm t,
exact add_right_cancel a t b,

end