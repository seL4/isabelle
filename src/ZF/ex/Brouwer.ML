(*  Title: 	ZF/ex/Brouwer.ML
    ID:         $ $
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Datatype definition of the Brouwer ordinals -- demonstrates infinite branching
*)

structure Brouwer = Datatype_Fun
 (val thy	= InfDatatype.thy;
  val thy_name 	= "Brouwer";
  val rec_specs = [("brouwer", "Vfrom(0, csucc(nat))",
		    [(["Zero"], "i", NoSyn), 
		     (["Suc","Lim"], "i=>i", NoSyn)])];
  val rec_styp 	= "i";
  val sintrs 	= ["Zero : brouwer",
		   "b: brouwer ==> Suc(b): brouwer",
	           "h: nat -> brouwer ==> Lim(h) : brouwer"];
  val monos 	 = [Pi_mono];
  val type_intrs = inf_datatype_intrs;
  val type_elims = []);

val [ZeroI, SucI, LimI] = Brouwer.intrs;

goal Brouwer.thy "brouwer = {0} + brouwer + (nat -> brouwer)";
by (rtac (Brouwer.unfold RS trans) 1);
bws Brouwer.con_defs;
by (fast_tac (sum_cs addIs ([equalityI] @ inf_datatype_intrs)
 	             addDs [Brouwer.dom_subset RS subsetD]
 	             addEs [A_into_Vfrom, fun_into_Vfrom_csucc]) 1);
val brouwer_unfold = result();

(*A nicer induction rule than the standard one*)
val major::prems = goal Brouwer.thy
    "[| b: brouwer;  					\
\       P(Zero);					\
\	!!b. [| b: brouwer;  P(b) |] ==> P(Suc(b));	\
\	!!h. [| h: nat -> brouwer;  ALL i:nat. P(h`i)	\
\            |] ==> P(Lim(h))				\
\    |] ==> P(b)";
by (rtac (major RS Brouwer.induct) 1);
by (REPEAT_SOME (ares_tac prems));
by (fast_tac (ZF_cs addEs [fun_weaken_type]) 1);
by (fast_tac (ZF_cs addDs [apply_type]) 1);
val brouwer_induct2 = result();
