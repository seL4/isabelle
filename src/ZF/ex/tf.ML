(*  Title: 	ZF/ex/tf.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Trees & forests, a mutually recursive type definition.
*)

structure TF = Datatype_Fun
 (val thy = Univ.thy;
  val rec_specs = 
      [("tree", "univ(A)",
	  [(["Tcons"],	"[i,i]=>i")]),
       ("forest", "univ(A)",
	  [(["Fnil"],	"i"),
	   (["Fcons"],	"[i,i]=>i")])];
  val rec_styp = "i=>i";
  val ext = None
  val sintrs = 
	  ["[| a:A;  tf: forest(A) |] ==> Tcons(a,tf) : tree(A)",
	   "Fnil : forest(A)",
	   "[| t: tree(A);  tf: forest(A) |] ==> Fcons(t,tf) : forest(A)"];
  val monos = [];
  val type_intrs = data_typechecks
  val type_elims = []);

val [TconsI, FnilI, FconsI] = TF.intrs;

(** tree_forest(A) as the union of tree(A) and forest(A) **)

goalw TF.thy (tl TF.defs) "tree(A) <= tree_forest(A)";
by (rtac Part_subset 1);
val tree_subset_TF = result();

goalw TF.thy (tl TF.defs) "forest(A) <= tree_forest(A)";
by (rtac Part_subset 1);
val forest_subset_TF = result();

goalw TF.thy (tl TF.defs) "tree(A) Un forest(A) = tree_forest(A)";
by (rtac (TF.dom_subset RS Part_sum_equality) 1);
val TF_equals_Un = result();

(** NOT useful, but interesting... **)

goalw TF.thy (tl TF.defs) "tree(A) = {Inl(x). x: A*forest(A)}";
by (res_inst_tac [("P", "%x.?t(x) = ?u::i")] (TF.unfold RS ssubst) 1);
by (rewrite_goals_tac TF.con_defs);
by (rtac equalityI 1);
by (fast_tac (ZF_cs addIs [PartI] addSEs (PartE::TF.free_SEs)) 1);
by (fast_tac (ZF_cs addIs ([PartI,InlI,InrI] @ [TF.dom_subset RS subsetD]
			   @ data_typechecks)
	            addSEs (PartE::TF.free_SEs)) 1);
val tree_unfold = result();

goalw TF.thy (tl TF.defs) "forest(A) = {Inr(x). x: {0} + tree(A)*forest(A)}";
by (res_inst_tac [("P", "%x.?t(x) = ?u::i")] (TF.unfold RS ssubst) 1);
by (rewrite_goals_tac TF.con_defs);
by (rtac equalityI 1);
by (fast_tac (ZF_cs addIs [PartI,InlI,InrI] 
                    addSEs (PartE::TF.free_SEs)) 1);
by (fast_tac (ZF_cs addIs ([PartI,InlI,InrI] @ [TF.dom_subset RS subsetD]
			   @ data_typechecks)
	            addSEs ([PartE, sumE] @ TF.free_SEs)) 1);
val forest_unfold = result();

