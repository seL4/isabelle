(*  Title: 	ZF/ex/bt.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Datatype definition of binary trees
*)

structure BT = Datatype_Fun
 (val thy = Univ.thy;
  val thy_name = "BT";
  val rec_specs = 
      [("bt", "univ(A)",
	  [(["Lf"],"i",NoSyn), 
           (["Br"],"[i,i,i]=>i", NoSyn)])];
  val rec_styp = "i=>i";
  val sintrs = 
	  ["Lf : bt(A)",
	   "[| a: A;  t1: bt(A);  t2: bt(A) |] ==> Br(a,t1,t2) : bt(A)"];
  val monos = [];
  val type_intrs = datatype_intrs
  val type_elims = []);

val [LfI, BrI] = BT.intrs;

(*Perform induction on l, then prove the major premise using prems. *)
fun bt_ind_tac a prems i = 
    EVERY [res_inst_tac [("x",a)] BT.induct i,
	   rename_last_tac a ["1","2"] (i+2),
	   ares_tac prems i];


(**  Lemmas to justify using "bt" in other recursive type definitions **)

goalw BT.thy BT.defs "!!A B. A<=B ==> bt(A) <= bt(B)";
by (rtac lfp_mono 1);
by (REPEAT (rtac BT.bnd_mono 1));
by (REPEAT (ares_tac (univ_mono::basic_monos) 1));
val bt_mono = result();

goalw BT.thy (BT.defs@BT.con_defs) "bt(univ(A)) <= univ(A)";
by (rtac lfp_lowerbound 1);
by (rtac (A_subset_univ RS univ_mono) 2);
by (fast_tac (ZF_cs addSIs [zero_in_univ, Inl_in_univ, Inr_in_univ,
			    Pair_in_univ]) 1);
val bt_univ = result();

val bt_subset_univ = standard ([bt_mono, bt_univ] MRS subset_trans);

