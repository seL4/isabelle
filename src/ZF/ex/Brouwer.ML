(*  Title: 	ZF/ex/Brouwer.ML
    ID:         $ $
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Datatype definition of the Brouwer ordinals -- demonstrates infinite branching
*)

open Brouwer;

goal Brouwer.thy "brouwer = {0} + brouwer + (nat -> brouwer)";
by (rtac (brouwer.unfold RS trans) 1);
bws brouwer.con_defs;
br equalityI 1;
by (fast_tac sum_cs 1);
by (fast_tac (sum_cs addIs inf_datatype_intrs
 	             addDs [brouwer.dom_subset RS subsetD]
 	             addEs [fun_into_Vcsucc]) 1);
val brouwer_unfold = result();

(*A nicer induction rule than the standard one*)
val major::prems = goal Brouwer.thy
    "[| b: brouwer;  					\
\       P(Zero);					\
\	!!b. [| b: brouwer;  P(b) |] ==> P(Suc(b));	\
\	!!h. [| h: nat -> brouwer;  ALL i:nat. P(h`i)	\
\            |] ==> P(Lim(h))				\
\    |] ==> P(b)";
by (rtac (major RS brouwer.induct) 1);
by (REPEAT_SOME (ares_tac prems));
by (fast_tac (ZF_cs addEs [fun_weaken_type]) 1);
by (fast_tac (ZF_cs addDs [apply_type]) 1);
val brouwer_induct2 = result();
