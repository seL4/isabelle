goal HOL.thy "(~(!x. P x)) = (? x. ~(P x)) & \
           \  (~(? x. P x)) = (!x. ~(P x)) & \
           \  (~(x-->y)) = (x & (~ y))     & \
           \  ((~ x) | y) = (x --> y)      & \
           \  (~(x & y)) = ((~ x) | (~ y)) & \
           \  (~(x | y)) = ((~ x) & (~ y)) & \
           \  (~(~x)) = x";
by (fast_tac HOL_cs 1);
val NNF_rews = map (fn th => th RS eq_reflection)
                   (Prim.Rules.CONJUNCTS (result()))

