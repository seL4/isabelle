(*  Title:      HOL/ex/SList.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Definition of type 'a list by a least fixed point
*)

open SList;

val list_con_defs = [NIL_def, CONS_def];

goal SList.thy "list(A) = {Numb(0)} <+> (A <*> list(A))";
let val rew = rewrite_rule list_con_defs in  
by (fast_tac (!claset addSIs (equalityI :: map rew list.intrs)
                      addEs [rew list.elim]) 1)
end;
qed "list_unfold";

(*This justifies using list in other recursive type definitions*)
goalw SList.thy list.defs "!!A B. A<=B ==> list(A) <= list(B)";
by (rtac lfp_mono 1);
by (REPEAT (ares_tac basic_monos 1));
qed "list_mono";

(*Type checking -- list creates well-founded sets*)
goalw SList.thy (list_con_defs @ list.defs) "list(sexp) <= sexp";
by (rtac lfp_lowerbound 1);
by (fast_tac (!claset addIs sexp.intrs@[sexp_In0I,sexp_In1I]) 1);
qed "list_sexp";

(* A <= sexp ==> list(A) <= sexp *)
bind_thm ("list_subset_sexp", ([list_mono, list_sexp] MRS subset_trans));

(*Induction for the type 'a list *)
val prems = goalw SList.thy [Nil_def,Cons_def]
    "[| P(Nil);   \
\       !!x xs. P(xs) ==> P(x # xs) |]  ==> P(l)";
by (rtac (Rep_list_inverse RS subst) 1);   (*types force good instantiation*)
by (rtac (Rep_list RS list.induct) 1);
by (REPEAT (ares_tac prems 1
     ORELSE eresolve_tac [rangeE, ssubst, Abs_list_inverse RS subst] 1));
qed "list_induct2";

(*Perform induction on xs. *)
fun list_ind_tac a M = 
    EVERY [res_inst_tac [("l",a)] list_induct2 M,
           rename_last_tac a ["1"] (M+1)];

(*** Isomorphisms ***)

goal SList.thy "inj(Rep_list)";
by (rtac inj_inverseI 1);
by (rtac Rep_list_inverse 1);
qed "inj_Rep_list";

goal SList.thy "inj_onto Abs_list (list(range Leaf))";
by (rtac inj_onto_inverseI 1);
by (etac Abs_list_inverse 1);
qed "inj_onto_Abs_list";

(** Distinctness of constructors **)

goalw SList.thy list_con_defs "CONS M N ~= NIL";
by (rtac In1_not_In0 1);
qed "CONS_not_NIL";
bind_thm ("NIL_not_CONS", (CONS_not_NIL RS not_sym));

bind_thm ("CONS_neq_NIL", (CONS_not_NIL RS notE));
val NIL_neq_CONS = sym RS CONS_neq_NIL;

goalw SList.thy [Nil_def,Cons_def] "x # xs ~= Nil";
by (rtac (CONS_not_NIL RS (inj_onto_Abs_list RS inj_onto_contraD)) 1);
by (REPEAT (resolve_tac (list.intrs @ [rangeI, Rep_list]) 1));
qed "Cons_not_Nil";

bind_thm ("Nil_not_Cons", Cons_not_Nil RS not_sym);

(** Injectiveness of CONS and Cons **)

goalw SList.thy [CONS_def] "(CONS K M=CONS L N) = (K=L & M=N)";
by (fast_tac (!claset addSEs [Scons_inject, make_elim In1_inject]) 1);
qed "CONS_CONS_eq";

(*For reasoning about abstract list constructors*)
AddIs ([Rep_list] @ list.intrs);

AddIffs [CONS_not_NIL, NIL_not_CONS, CONS_CONS_eq];

AddSDs [inj_onto_Abs_list RS inj_ontoD,
        inj_Rep_list RS injD, Leaf_inject];

goalw SList.thy [Cons_def] "(x#xs=y#ys) = (x=y & xs=ys)";
by (Fast_tac 1);
qed "Cons_Cons_eq";
bind_thm ("Cons_inject2", (Cons_Cons_eq RS iffD1 RS conjE));

val [major] = goal SList.thy "CONS M N: list(A) ==> M: A & N: list(A)";
by (rtac (major RS setup_induction) 1);
by (etac list.induct 1);
by (ALLGOALS (Fast_tac));
qed "CONS_D";

val prems = goalw SList.thy [CONS_def,In1_def]
    "CONS M N: sexp ==> M: sexp & N: sexp";
by (cut_facts_tac prems 1);
by (fast_tac (!claset addSDs [Scons_D]) 1);
qed "sexp_CONS_D";


(*Reasoning about constructors and their freeness*)
Addsimps list.intrs;

AddIffs [Cons_not_Nil, Nil_not_Cons, Cons_Cons_eq];

goal SList.thy "!!N. N: list(A) ==> !M. N ~= CONS M N";
by (etac list.induct 1);
by (ALLGOALS Asm_simp_tac);
qed "not_CONS_self";

goal SList.thy "!x. l ~= x#l";
by (list_ind_tac "l" 1);
by (ALLGOALS Asm_simp_tac);
qed "not_Cons_self2";


goal SList.thy "(xs ~= []) = (? y ys. xs = y#ys)";
by (list_ind_tac "xs" 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
by (REPEAT(resolve_tac [exI,refl,conjI] 1));
qed "neq_Nil_conv2";

(** Conversion rules for List_case: case analysis operator **)

goalw SList.thy [List_case_def,NIL_def] "List_case c h NIL = c";
by (rtac Case_In0 1);
qed "List_case_NIL";

goalw SList.thy [List_case_def,CONS_def]  "List_case c h (CONS M N) = h M N";
by (simp_tac (!simpset addsimps [Split,Case_In1]) 1);
qed "List_case_CONS";

(*** List_rec -- by wf recursion on pred_sexp ***)

(* The trancl(pred_sexp) is essential because pred_sexp_CONS_I1,2 would not
   hold if pred_sexp^+ were changed to pred_sexp. *)

goal SList.thy
   "(%M. List_rec M c d) = wfrec (trancl pred_sexp) \
                           \     (%g. List_case c (%x y. d x y (g y)))";
by (simp_tac (HOL_ss addsimps [List_rec_def]) 1);
val List_rec_unfold = standard 
  ((wf_pred_sexp RS wf_trancl) RS ((result() RS eq_reflection) RS def_wfrec));

(*---------------------------------------------------------------------------
 * Old:
 * val List_rec_unfold = [List_rec_def,wf_pred_sexp RS wf_trancl] MRS def_wfrec
 *                     |> standard;
 *---------------------------------------------------------------------------*)

(** pred_sexp lemmas **)

goalw SList.thy [CONS_def,In1_def]
    "!!M. [| M: sexp;  N: sexp |] ==> (M, CONS M N) : pred_sexp^+";
by (Asm_simp_tac 1);
qed "pred_sexp_CONS_I1";

goalw SList.thy [CONS_def,In1_def]
    "!!M. [| M: sexp;  N: sexp |] ==> (N, CONS M N) : pred_sexp^+";
by (Asm_simp_tac 1);
qed "pred_sexp_CONS_I2";

val [prem] = goal SList.thy
    "(CONS M1 M2, N) : pred_sexp^+ ==> \
\    (M1,N) : pred_sexp^+ & (M2,N) : pred_sexp^+";
by (rtac (prem RS (pred_sexp_subset_Sigma RS trancl_subset_Sigma RS 
                   subsetD RS SigmaE2)) 1);
by (etac (sexp_CONS_D RS conjE) 1);
by (REPEAT (ares_tac [conjI, pred_sexp_CONS_I1, pred_sexp_CONS_I2,
                      prem RSN (2, trans_trancl RS transD)] 1));
qed "pred_sexp_CONS_D";

(** Conversion rules for List_rec **)

goal SList.thy "List_rec NIL c h = c";
by (rtac (List_rec_unfold RS trans) 1);
by (simp_tac (!simpset addsimps [List_case_NIL]) 1);
qed "List_rec_NIL";

goal SList.thy "!!M. [| M: sexp;  N: sexp |] ==> \
\    List_rec (CONS M N) c h = h M N (List_rec N c h)";
by (rtac (List_rec_unfold RS trans) 1);
by (asm_simp_tac (!simpset addsimps [List_case_CONS, pred_sexp_CONS_I2]) 1);
qed "List_rec_CONS";

(*** list_rec -- by List_rec ***)

val Rep_list_in_sexp =
    [range_Leaf_subset_sexp RS list_subset_sexp, Rep_list] MRS subsetD;

local
  val list_rec_simps = [List_rec_NIL, List_rec_CONS, 
                        Abs_list_inverse, Rep_list_inverse,
                        Rep_list, rangeI, inj_Leaf, inv_f_f,
                        sexp.LeafI, Rep_list_in_sexp]
in
  val list_rec_Nil = prove_goalw SList.thy [list_rec_def, Nil_def]
      "list_rec Nil c h = c"
   (fn _=> [simp_tac (!simpset addsimps list_rec_simps) 1]);

  val list_rec_Cons = prove_goalw SList.thy [list_rec_def, Cons_def]
      "list_rec (a#l) c h = h a l (list_rec l c h)"
   (fn _=> [simp_tac (!simpset addsimps list_rec_simps) 1]);
end;

Addsimps [List_rec_NIL, List_rec_CONS, list_rec_Nil, list_rec_Cons];


(*Type checking.  Useful?*)
val major::A_subset_sexp::prems = goal SList.thy
    "[| M: list(A);     \
\       A<=sexp;        \
\       c: C(NIL);      \
\       !!x y r. [| x: A;  y: list(A);  r: C(y) |] ==> h x y r: C(CONS x y) \
\    |] ==> List_rec M c h : C(M :: 'a item)";
val sexp_ListA_I = A_subset_sexp RS list_subset_sexp RS subsetD;
val sexp_A_I = A_subset_sexp RS subsetD;
by (rtac (major RS list.induct) 1);
by (ALLGOALS(asm_simp_tac (!simpset addsimps ([sexp_A_I,sexp_ListA_I]@prems))));
qed "List_rec_type";

(** Generalized map functionals **)

goalw SList.thy [Rep_map_def] "Rep_map f Nil = NIL";
by (rtac list_rec_Nil 1);
qed "Rep_map_Nil";

goalw SList.thy [Rep_map_def]
    "Rep_map f (x#xs) = CONS (f x) (Rep_map f xs)";
by (rtac list_rec_Cons 1);
qed "Rep_map_Cons";

goalw SList.thy [Rep_map_def] "!!f. (!!x. f(x): A) ==> Rep_map f xs: list(A)";
by (rtac list_induct2 1);
by (ALLGOALS Asm_simp_tac);
qed "Rep_map_type";

goalw SList.thy [Abs_map_def] "Abs_map g NIL = Nil";
by (rtac List_rec_NIL 1);
qed "Abs_map_NIL";

val prems = goalw SList.thy [Abs_map_def]
    "[| M: sexp;  N: sexp |] ==> \
\    Abs_map g (CONS M N) = g(M) # Abs_map g N";
by (REPEAT (resolve_tac (List_rec_CONS::prems) 1));
qed "Abs_map_CONS";

(*These 2 rules ease the use of primitive recursion.  NOTE USE OF == *)
val [rew] = goal SList.thy
    "[| !!xs. f(xs) == list_rec xs c h |] ==> f([]) = c";
by (rewtac rew);
by (rtac list_rec_Nil 1);
qed "def_list_rec_Nil";

val [rew] = goal SList.thy
    "[| !!xs. f(xs) == list_rec xs c h |] ==> f(x#xs) = h x xs (f xs)";
by (rewtac rew);
by (rtac list_rec_Cons 1);
qed "def_list_rec_Cons";

fun list_recs def =
      [standard (def RS def_list_rec_Nil),
       standard (def RS def_list_rec_Cons)];

(*** Unfolding the basic combinators ***)

val [null_Nil, null_Cons]               = list_recs null_def;
val [_, hd_Cons]                        = list_recs hd_def;
val [_, tl_Cons]                        = list_recs tl_def;
val [ttl_Nil, ttl_Cons]                 = list_recs ttl_def;
val [append_Nil3, append_Cons]          = list_recs append_def;
val [mem_Nil, mem_Cons]                 = list_recs mem_def;
val [set_Nil, set_Cons]                 = list_recs set_def;
val [map_Nil, map_Cons]                 = list_recs map_def;
val [list_case_Nil, list_case_Cons]     = list_recs list_case_def;
val [filter_Nil, filter_Cons]           = list_recs filter_def;

Addsimps
  [null_Nil, ttl_Nil,
   mem_Nil, mem_Cons,
   list_case_Nil, list_case_Cons,
   append_Nil3, append_Cons,
   set_Nil, set_Cons, 
   map_Nil, map_Cons,
   filter_Nil, filter_Cons];


(** @ - append **)

goal SList.thy "(xs@ys)@zs = xs@(ys@zs)";
by (list_ind_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "append_assoc2";

goal SList.thy "xs @ [] = xs";
by (list_ind_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "append_Nil4";

(** mem **)

goal SList.thy "x mem (xs@ys) = (x mem xs | x mem ys)";
by (list_ind_tac "xs" 1);
by (ALLGOALS(asm_simp_tac (!simpset addsplits [expand_if])));
qed "mem_append2";

goal SList.thy "x mem [x:xs. P(x)] = (x mem xs & P(x))";
by (list_ind_tac "xs" 1);
by (ALLGOALS(asm_simp_tac (!simpset addsplits [expand_if])));
qed "mem_filter2";


(** The functional "map" **)

Addsimps [Rep_map_Nil, Rep_map_Cons, Abs_map_NIL, Abs_map_CONS];

val [major,A_subset_sexp,minor] = goal SList.thy 
    "[| M: list(A);  A<=sexp;  !!z. z: A ==> f(g(z)) = z |] \
\    ==> Rep_map f (Abs_map g M) = M";
by (rtac (major RS list.induct) 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [sexp_A_I,sexp_ListA_I,minor])));
qed "Abs_map_inverse";

(*Rep_map_inverse is obtained via Abs_Rep_map and map_ident*)

(** list_case **)

goal SList.thy
 "P(list_case a f xs) = ((xs=[] --> P(a)) & \
\                        (!y ys. xs=y#ys --> P(f y ys)))";
by (list_ind_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "expand_list_case2";


(** Additional mapping lemmas **)

goal SList.thy "map (%x. x) xs = xs";
by (list_ind_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "map_ident2";

goal SList.thy "map f (xs@ys) = map f xs @ map f ys";
by (list_ind_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "map_append2";

goalw SList.thy [o_def] "map (f o g) xs = map f (map g xs)";
by (list_ind_tac "xs" 1);
by (ALLGOALS Asm_simp_tac);
qed "map_compose2";

goal SList.thy "!!f. (!!x. f(x): sexp) ==> \
\       Abs_map g (Rep_map f xs) = map (%t. g(f(t))) xs";
by (list_ind_tac "xs" 1);
by (ALLGOALS(asm_simp_tac(!simpset addsimps
       [Rep_map_type,list_sexp RS subsetD])));
qed "Abs_Rep_map";

Addsimps [append_Nil4, map_ident2];
