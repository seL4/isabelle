(*  Title:      ZF/ex/Brouwer.ML
    ID:         $ $
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Infinite branching datatype definitions
  (1) the Brouwer ordinals
  (2) the Martin-Löf wellordering type
*)

open Brouwer;

(** The Brouwer ordinals **)

goal Brouwer.thy "brouwer = {0} + brouwer + (nat -> brouwer)";
let open brouwer;  val rew = rewrite_rule con_defs in  
by (fast_tac (sum_cs addSIs (equalityI :: map rew intrs)
                     addEs [rew elim]) 1)
end;
qed "brouwer_unfold";

(*A nicer induction rule than the standard one*)
val major::prems = goal Brouwer.thy
    "[| b: brouwer;                                     \
\       P(Zero);                                        \
\       !!b. [| b: brouwer;  P(b) |] ==> P(Suc(b));     \
\       !!h. [| h: nat -> brouwer;  ALL i:nat. P(h`i)   \
\            |] ==> P(Lim(h))                           \
\    |] ==> P(b)";
by (rtac (major RS brouwer.induct) 1);
by (REPEAT_SOME (ares_tac prems));
by (fast_tac (!claset addEs [fun_weaken_type]) 1);
by (fast_tac (!claset addDs [apply_type]) 1);
qed "brouwer_induct2";


(** The Martin-Löf wellordering type **)

goal Brouwer.thy "Well(A,B) = (SUM x:A. B(x) -> Well(A,B))";
let open Well;  val rew = rewrite_rule con_defs in  
by (fast_tac (sum_cs addSIs (equalityI :: map rew intrs)
                     addEs [rew elim]) 1)
end;
qed "Well_unfold";

(*A nicer induction rule than the standard one*)
val major::prems = goal Brouwer.thy
    "[| w: Well(A,B);                                                   \
\       !!a f. [| a: A;  f: B(a) -> Well(A,B);  ALL y: B(a). P(f`y)     \
\            |] ==> P(Sup(a,f))                                         \
\    |] ==> P(w)";
by (rtac (major RS Well.induct) 1);
by (REPEAT_SOME (ares_tac prems));
by (fast_tac (!claset addEs [fun_weaken_type]) 1);
by (fast_tac (!claset addDs [apply_type]) 1);
qed "Well_induct2";


(*In fact it's isomorphic to nat, but we need a recursion operator for
  Well to prove this.*)
goal Brouwer.thy "Well(bool, %x.x) = 1 + (1 -> Well(bool, %x.x))";
by (resolve_tac [Well_unfold RS trans] 1);
by (simp_tac (!simpset addsimps [Sigma_bool, Pi_empty1, succ_def]) 1);
qed "Well_bool_unfold";
