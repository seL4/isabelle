Goal
 "evala env (substa s a) = evala (%x. evala env (s x)) a & \
\ evalb env (substb s b) = evalb (%x. evala env (s x)) b";
by(induct_tac "a b" 1);
