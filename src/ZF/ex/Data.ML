(*  Title:      ZF/ex/Data.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Sample datatype definition.  
It has four contructors, of arities 0-3, and two parameters A and B.
*)

open Data;

goal Data.thy "data(A,B) = ({0} + A) + (A*B + A*B*data(A,B))";
let open data;  val rew = rewrite_rule con_defs in  
by (fast_tac (sum_cs addSIs (equalityI :: map rew intrs)
                     addEs [rew elim]) 1)
end;
qed "data_unfold";

(**  Lemmas to justify using "data" in other recursive type definitions **)

goalw Data.thy data.defs "!!A B. [| A<=C; B<=D |] ==> data(A,B) <= data(C,D)";
by (rtac lfp_mono 1);
by (REPEAT (rtac data.bnd_mono 1));
by (REPEAT (ares_tac (univ_mono::Un_mono::basic_monos) 1));
qed "data_mono";

goalw Data.thy (data.defs@data.con_defs) "data(univ(A),univ(A)) <= univ(A)";
by (rtac lfp_lowerbound 1);
by (rtac ([A_subset_univ, Un_upper1] MRS subset_trans RS univ_mono) 2);
by (fast_tac (!claset addSIs [zero_in_univ, Inl_in_univ, Inr_in_univ,
                            Pair_in_univ]) 1);
qed "data_univ";

bind_thm ("data_subset_univ", ([data_mono, data_univ] MRS subset_trans));


