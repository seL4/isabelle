(*  Title: 	ZF/list.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Datatype definition of Lists
*)

structure List = Datatype_Fun
 (val thy = Univ.thy;
  val rec_specs = 
      [("list", "univ(A)",
	  [(["Nil"],	"i"), 
	   (["Cons"],	"[i,i]=>i")])];
  val rec_styp = "i=>i";
  val ext = None
  val sintrs = 
      ["Nil : list(A)",
       "[| a: A;  l: list(A) |] ==> Cons(a,l) : list(A)"];
  val monos = [];
  val type_intrs = datatype_intrs
  val type_elims = datatype_elims);

val [NilI, ConsI] = List.intrs;

(*An elimination rule, for type-checking*)
val ConsE = List.mk_cases List.con_defs "Cons(a,l) : list(A)";

(*Proving freeness results*)
val Cons_iff     = List.mk_free "Cons(a,l)=Cons(a',l') <-> a=a' & l=l'";
val Nil_Cons_iff = List.mk_free "~ Nil=Cons(a,l)";

(*Perform induction on l, then prove the major premise using prems. *)
fun list_ind_tac a prems i = 
    EVERY [res_inst_tac [("x",a)] List.induct i,
	   rename_last_tac a ["1"] (i+2),
	   ares_tac prems i];

(**  Lemmas to justify using "list" in other recursive type definitions **)

goalw List.thy List.defs "!!A B. A<=B ==> list(A) <= list(B)";
by (rtac lfp_mono 1);
by (REPEAT (rtac List.bnd_mono 1));
by (REPEAT (ares_tac (univ_mono::basic_monos) 1));
val list_mono = result();

(*There is a similar proof by list induction.*)
goalw List.thy (List.defs@List.con_defs) "list(univ(A)) <= univ(A)";
by (rtac lfp_lowerbound 1);
by (rtac (A_subset_univ RS univ_mono) 2);
by (fast_tac (ZF_cs addSIs [zero_in_univ, Inl_in_univ, Inr_in_univ,
			    Pair_in_univ]) 1);
val list_univ = result();

val list_subset_univ = standard ([list_mono, list_univ] MRS subset_trans);

val major::prems = goal List.thy
    "[| l: list(A);    \
\       c: C(Nil);       \
\       !!x y. [| x: A;  y: list(A) |] ==> h(x,y): C(Cons(x,y))  \
\    |] ==> list_case(c,h,l) : C(l)";
by (rtac (major RS List.induct) 1);
by (ALLGOALS (asm_simp_tac (ZF_ss addsimps (List.case_eqns @ prems))));
val list_case_type = result();


(** For recursion **)

goalw List.thy List.con_defs "rank(a) < rank(Cons(a,l))";
by (simp_tac rank_ss 1);
val rank_Cons1 = result();

goalw List.thy List.con_defs "rank(l) < rank(Cons(a,l))";
by (simp_tac rank_ss 1);
val rank_Cons2 = result();

