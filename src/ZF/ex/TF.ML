(*  Title: 	ZF/ex/tf.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Trees & forests, a mutually recursive type definition.
*)

structure TF = Datatype_Fun
 (val thy        = Univ.thy
  val rec_specs  = [("tree", "univ(A)",
                       [(["Tcons"],  "[i,i]=>i")]),
                    ("forest", "univ(A)",
                       [(["Fnil"],   "i"),
                        (["Fcons"],  "[i,i]=>i")])]
  val rec_styp   = "i=>i"
  val ext        = None
  val sintrs     = 
          ["[| a:A;  f: forest(A) |] ==> Tcons(a,f) : tree(A)",
           "Fnil : forest(A)",
           "[| t: tree(A);  f: forest(A) |] ==> Fcons(t,f) : forest(A)"]
  val monos      = []
  val type_intrs = datatype_intrs
  val type_elims = datatype_elims);

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

(*The (refl RS conjI RS exI RS exI) avoids considerable search!*)
val unfold_cs = sum_cs addSIs [PartI, refl RS conjI RS exI RS exI]
                    addIs datatype_intrs
                    addDs [TF.dom_subset RS subsetD]
	            addSEs ([PartE] @ datatype_elims @ TF.free_SEs);

goalw TF.thy (tl TF.defs)
    "tree_forest(A) = (A*forest(A)) + ({0} + tree(A)*forest(A))";
by (rtac (TF.unfold RS trans) 1);
by (rewrite_goals_tac TF.con_defs);
by (rtac equalityI 1);
by (fast_tac unfold_cs 1);
by (fast_tac unfold_cs 1);
val tree_forest_unfold = result();

val tree_forest_unfold' = rewrite_rule (tl TF.defs) tree_forest_unfold;


goalw TF.thy (tl TF.defs) "tree(A) = {Inl(x). x: A*forest(A)}";
by (rtac (Part_Inl RS subst) 1);
by (rtac (tree_forest_unfold' RS subst_context) 1);
val tree_unfold = result();

goalw TF.thy (tl TF.defs) "forest(A) = {Inr(x). x: {0} + tree(A)*forest(A)}";
by (rtac (Part_Inr RS subst) 1);
by (rtac (tree_forest_unfold' RS subst_context) 1);
val forest_unfold = result();



