(*  Title: 	ZF/ex/Data.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Sample datatype definition.  
It has four contructors, of arities 0-3, and two parameters A and B.
*)

open Data;

goal Data.thy "data(A,B) = ({0} + A) + (A*B + A*B*data(A,B))";
by (rtac (data.unfold RS trans) 1);
bws data.con_defs;
br equalityI 1;
by (fast_tac sum_cs 1);
(*for this direction, fast_tac is just too slow!*)
by (safe_tac sum_cs);
by (REPEAT_FIRST (swap_res_tac [refl, conjI, disjCI, exI]));
by (REPEAT (fast_tac (sum_cs addIs datatype_intrs
  		             addDs [data.dom_subset RS subsetD]) 1));
val data_unfold = result();

(**  Lemmas to justify using "data" in other recursive type definitions **)

goalw Data.thy data.defs "!!A B. [| A<=C; B<=D |] ==> data(A,B) <= data(C,D)";
by (rtac lfp_mono 1);
by (REPEAT (rtac data.bnd_mono 1));
by (REPEAT (ares_tac (univ_mono::Un_mono::basic_monos) 1));
val data_mono = result();

goalw Data.thy (data.defs@data.con_defs) "data(univ(A),univ(A)) <= univ(A)";
by (rtac lfp_lowerbound 1);
by (rtac ([A_subset_univ, Un_upper1] MRS subset_trans RS univ_mono) 2);
by (fast_tac (ZF_cs addSIs [zero_in_univ, Inl_in_univ, Inr_in_univ,
			    Pair_in_univ]) 1);
val data_univ = result();

val data_subset_univ = standard ([data_mono, data_univ] MRS subset_trans);


