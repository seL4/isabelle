(*  Title: 	ZF/ex/data.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Sample datatype definition.  
It has four contructors, of arities 0-3, and two parameters A and B.
*)

structure Data = Datatype_Fun
 (val thy        = Univ.thy
  val rec_specs  = [("data", "univ(A Un B)",
                       [(["Con0"],   "i"),
                        (["Con1"],   "i=>i"),
                        (["Con2"],   "[i,i]=>i"),
                        (["Con3"],   "[i,i,i]=>i")])]
  val rec_styp   = "[i,i]=>i"
  val ext        = None
  val sintrs     = 
          ["Con0 : data(A,B)",
           "[| a: A |] ==> Con1(a) : data(A,B)",
           "[| a: A; b: B |] ==> Con2(a,b) : data(A,B)",
           "[| a: A; b: B;  d: data(A,B) |] ==> Con3(a,b,d) : data(A,B)"]
  val monos      = []
  val type_intrs = datatype_intrs
  val type_elims = datatype_elims);


(**  Lemmas to justify using "data" in other recursive type definitions **)

goalw Data.thy Data.defs "!!A B. [| A<=C; B<=D |] ==> data(A,B) <= data(C,D)";
by (rtac lfp_mono 1);
by (REPEAT (rtac Data.bnd_mono 1));
by (REPEAT (ares_tac (univ_mono::Un_mono::basic_monos) 1));
val data_mono = result();

goalw Data.thy (Data.defs@Data.con_defs) "data(univ(A),univ(A)) <= univ(A)";
by (rtac lfp_lowerbound 1);
by (rtac ([A_subset_univ, Un_upper1] MRS subset_trans RS univ_mono) 2);
by (fast_tac (ZF_cs addSIs [zero_in_univ, Inl_in_univ, Inr_in_univ,
			    Pair_in_univ]) 1);
val data_univ = result();

val data_subset_univ = standard ([data_mono, data_univ] MRS subset_trans);


