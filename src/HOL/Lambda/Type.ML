(*  Title:      HOL/Lambda/Type.ML
    ID:         $Id$
    Author:     Stefan Berghofer
    Copyright   2000 TU Muenchen

Subject reduction and strong normalization of simply-typed lambda terms.

Partly based on a paper proof by Ralph Matthes.
*)

AddSIs IT.intrs;
AddSIs typing.intrs;
AddSEs (map typing.mk_cases
  ["e |- Var i : T", "e |- t $ u : T", "e |- Abs t : T"]);
AddSEs [lists.mk_cases "x # xs : lists S"];

(*** test ***)

Goal "e |- Abs (Abs (Abs (Var 1 $ (Var 2 $ Var 1 $ Var 0)))) : ?T";
by (fast_tac (claset() addss simpset()) 1);
result();

Goal "e |- Abs (Abs (Abs (Var 2 $ Var 0 $ (Var 1 $ Var 0)))) : ?T";
by (fast_tac (claset() addss simpset()) 1);
result();

(**** n-ary function types ****)

Goal "ALL t T. \
  \ e |- t $$ ts : T --> (EX Ts. e |- t : Ts =>> T & types e ts Ts)";
by (induct_tac "ts" 1);
by (Simp_tac 1);
by (strip_tac 1);
by (Full_simp_tac 1);
by (eres_inst_tac [("x","t $ a")] allE 1);
by (eres_inst_tac [("x","T")] allE 1);
by (etac impE 1);
by (assume_tac 1);
by (etac exE 1);
by (etac conjE 1);
by (etac (typing.mk_cases "e |- t $ u : T") 1);
by (res_inst_tac [("x","Ta # Ts")] exI 1);
by (Asm_simp_tac 1);
qed_spec_mp "list_app_typeD";

Goal "ALL t T Ts. e |- t : Ts =>> T --> types e ts Ts --> e |- t $$ ts : T";
by (induct_tac "ts" 1);
by (strip_tac 1);
by (Asm_full_simp_tac 1);
by (strip_tac 1);
by (case_tac "Ts" 1);
by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
by (eres_inst_tac [("x","t $ a")] allE 1);
by (eres_inst_tac [("x","T")] allE 1);
by (eres_inst_tac [("x","lista")] allE 1);
by (etac impE 1);
by (etac conjE 1);
by (etac typing.APP 1);
by (assume_tac 1);
by (Fast_tac 1);
qed_spec_mp "list_app_typeI";

Goal "ALL Ts. types e ts Ts --> ts : lists {t. EX T. e |- t : T}";
by (induct_tac "ts" 1);
by (strip_tac 1);
by (case_tac "Ts" 1);
by (Asm_full_simp_tac 1);
by (rtac lists.Nil 1);
by (Asm_full_simp_tac 1);
by (strip_tac 1);
by (case_tac "Ts" 1);
by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
by (rtac lists.Cons 1);
by (Fast_tac 1);
by (Fast_tac 1);
qed_spec_mp "lists_types";

(**** lifting preserves termination and well-typedness ****)

Goal "ALL t. lift (t $$ ts) i = lift t i $$ map (%t. lift t i) ts";
by (induct_tac "ts" 1);
by (ALLGOALS Asm_full_simp_tac);
qed_spec_mp "lift_map";

Goal "ALL t. subst (t $$ ts) u i = subst t u i $$ map (%t. subst t u i) ts";
by (induct_tac "ts" 1);
by (ALLGOALS Asm_full_simp_tac);
qed_spec_mp "subst_map";

Addsimps [lift_map, subst_map];

Goal "t : IT ==> ALL i. lift t i : IT";
by (etac IT.induct 1);
by (rtac allI 1);
by (Simp_tac 1);
by (rtac conjI 1);
by (REPEAT (EVERY
  [rtac impI 1,
   rtac IT.VarI 1,
   etac lists.induct 1,
   Simp_tac 1,
   rtac lists.Nil 1,
   Simp_tac 1,
   etac IntE 1,
   rtac lists.Cons 1,
   Fast_tac 1,
   atac 1]));
by (ALLGOALS (fast_tac (claset() addss simpset())));
qed_spec_mp "lift_IT";
AddSIs [lift_IT];

Goal "ts : lists IT --> map (%t. lift t 0) ts : lists IT";
by (induct_tac "ts" 1);
by (ALLGOALS (fast_tac (claset() addss simpset())));
qed_spec_mp "lifts_IT";

Goal "nat_case T  \
 \   (%j. if j < i then e j else if j = i then Ua else e (j - 1)) =  \
 \ (%j. if j < Suc i then nat_case T e j else if j = Suc i then Ua  \
 \   else nat_case T e (j - 1))";
by (rtac ext 1);
by (case_tac "j" 1);
by (Asm_simp_tac 1);
by (case_tac "nat" 1);
by (ALLGOALS Asm_simp_tac);
qed "shift_env";
Addsimps [shift_env];

Goal "e |- t : T ==> ALL i U. \
  \ (%j. if j < i then e j  \
  \     else if j = i then U \
  \     else e (j-1)) |- lift t i : T";
by (etac typing.induct 1);
by (ALLGOALS (fast_tac (claset() addss simpset())));
qed_spec_mp "lift_type'";

Goal "e |- t : T ==> nat_case U e |- lift t 0 : T";
by (subgoal_tac
  "nat_case U e = (%j. if j < 0 then e j  \
 \  else if j = 0 then U else e (j-1))" 1);
by (etac ssubst 1);
by (etac lift_type' 1);
by (rtac ext 1);
by (case_tac "j" 1);
by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
qed "lift_type";
AddSIs [lift_type];

Goal "ALL Ts. types e ts Ts -->  \
  \ types (%j. if j < i then e j  \
  \     else if j = i then U \
  \     else e (j-1)) (map (%t. lift t i) ts) Ts";
by (induct_tac "ts" 1);
by (Simp_tac 1);
by (strip_tac 1);
by (case_tac "Ts" 1);
by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
by (rtac lift_type' 1);
by (etac conjunct1 1);
qed_spec_mp "lift_types";

(**** substitution lemma ****)

Goal "e |- t : T ==> ALL e' i U u. \
  \ e = (%j. if j < i then e' j  \
  \      else if j = i then U \
  \      else e' (j-1)) -->  \
  \ e' |- u : U --> e' |- t[u/i] : T";
by (etac typing.induct 1);
by (strip_tac 1);
by (case_tac "x=i" 1);
by (Asm_full_simp_tac 1);
by (ftac (linorder_neq_iff RS iffD1) 1);
by (etac disjE 1);
by (Asm_full_simp_tac 1);
by (rtac typing.VAR 1);
by (assume_tac 1);
by (ftac order_less_not_sym 1);
by (asm_full_simp_tac (HOL_ss addsimps [subst_gt]) 1);
by (rtac typing.VAR 1);
by (assume_tac 1);
by (ALLGOALS (fast_tac (claset() addss simpset())));
qed_spec_mp "subst_lemma";

Goal "e |- u : T ==> ALL Ts. types (%j. if j < i then e j  \
  \  else if j = i then T else e (j - 1))  \
  \ ts Ts --> types e (map (%t. t[u/i]) ts) Ts";
by (induct_tac "ts" 1);
by (strip_tac 1);
by (case_tac "Ts" 1);
by (Asm_simp_tac 1);
by (Asm_full_simp_tac 1);
by (strip_tac 1);
by (case_tac "Ts" 1);
by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
by (etac conjE 1);
by (etac subst_lemma 1);
by (rtac refl 1);
by (assume_tac 1);
qed_spec_mp "substs_lemma";

(**** subject reduction ****)

Goal "e |- t : T ==> ALL t'. t -> t' --> e |- t' : T";
by (etac typing.induct 1);
by (Fast_tac 1);
by (Fast_tac 1);
by (strip_tac 1);
by (etac (beta.mk_cases "s $ t -> t'") 1);
by (hyp_subst_tac 1);
by (etac (typing.mk_cases "env |- Abs t : T => U") 1);
by (rtac subst_lemma 1);
by (assume_tac 1);
by (assume_tac 2);
by (rtac ext 1);
by (case_tac "j" 1);
by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
by (Fast_tac 1);
by (Fast_tac 1);
qed_spec_mp "subject_reduction";

(**** additional lemmas ****)

Goal "ALL t. (t $$ ts) $ u = t $$ (ts @ [u])";
by (induct_tac "ts" 1);
by (ALLGOALS Asm_full_simp_tac);
qed_spec_mp "app_last";

Goal "ALL ys. xs : lists S --> ys : lists S --> xs @ ys : lists S";
by (induct_tac "xs" 1);
by (ALLGOALS (fast_tac (claset() addss simpset())));
qed_spec_mp "append_lists";

Goal "r : IT ==> ALL i j. r[Var i/j] : IT";
by (etac IT.induct 1);
(** Var **)
by (strip_tac 1);
by (simp_tac (simpset() addsimps [subst_Var]) 1);
by (REPEAT (EVERY
  [REPEAT (resolve_tac [conjI, impI] 1),
   rtac IT.VarI 1,
   etac lists.induct 1,
   Simp_tac 1,
   rtac lists.Nil 1,
   Simp_tac 1,
   etac IntE 1,
   etac CollectE 1,
   rtac lists.Cons 1,
   Fast_tac 1,
   atac 1]));
(** Lambda **)
by (strip_tac 1);
by (Simp_tac 1);
by (rtac IT.LambdaI 1);
by (Fast_tac 1);
(** Beta **)
by (strip_tac 1);
by (full_simp_tac (simpset() addsimps [subst_subst RS sym]) 1);
by (rtac IT.BetaI 1);
by (Fast_tac 1);
by (Fast_tac 1);
qed_spec_mp "subst_Var_IT";

val Var_IT = rewrite_rule [mk_meta_eq foldl_Nil] (lists.Nil RS IT.VarI);

Goal "t : IT ==> t $ Var i : IT";
by (etac IT.induct 1);
by (stac app_last 1);
by (rtac IT.VarI 1);
by (rtac append_lists 1);
by (Asm_full_simp_tac 1);
by (rtac lists.Cons 1);
by (rtac Var_IT 1);
by (rtac lists.Nil 1);
by (rtac (rewrite_rule [mk_meta_eq foldl_Nil]
  (read_instantiate [("ss","[]")] IT.BetaI)) 1);
by (etac subst_Var_IT 1);
by (rtac Var_IT 1);
by (stac app_last 1);
by (rtac IT.BetaI 1);
by (stac (app_last RS sym) 1);
by (assume_tac 1);
by (assume_tac 1);
qed "app_Var_IT";

(**** well-typed substitution preserves termination ****)

Goal "ALL t. t : IT --> (ALL e T u i. \
  \  (%j. if j < i then e j  \
  \       else if j = i then U  \
  \       else e (j - 1)) |- t : T -->  \
  \  u : IT --> e |- u : U --> t[u/i] : IT)";
by (res_inst_tac [("f","size"),("a","U")] measure_induct 1);
by (rtac allI 1);
by (rtac impI 1);
by (etac IT.induct 1);
(** Var **)
by (strip_tac 1);
by (case_tac "n=i" 1);
(** n=i **)
by (case_tac "rs" 1);
by (Asm_simp_tac 1);
by (Asm_full_simp_tac 1);
by (dtac list_app_typeD 1);
by (REPEAT (eresolve_tac [exE, conjE] 1));
by (etac (typing.mk_cases "e |- t $ u : T") 1);
by (etac (typing.mk_cases "e |- Var i : T") 1);
by (dres_inst_tac [("s","(?T::typ) => ?U")] sym 1);
by (Asm_full_simp_tac 1);
by (subgoal_tac "lift u 0 $ Var 0 : IT" 1);
by (rtac app_Var_IT 2);
by (etac lift_IT 2);
by (subgoal_tac "(lift u 0 $ Var 0)[a[u/i]/0] : IT" 1);
by (Full_simp_tac 1);
by (subgoal_tac "(Var 0 $$ map (%t. lift t 0)  \
  \  (map (%t. t[u/i]) list))[(u $ a[u/i])/0] : IT" 1);
by (full_simp_tac (simpset() delsimps [map_compose] addsimps
  [map_compose RS sym, o_def]) 1);
by (eres_inst_tac [("x", "Ts =>> T")] allE 1);
by (etac impE 1);
by (Simp_tac 1);
by (eres_inst_tac [("x", "Var 0 $$ \
 \  map (%t. lift t 0) (map (%t. t[u/i]) list)")] allE 1);
by (etac impE 1);
by (rtac IT.VarI 1);
by (rtac lifts_IT 1);
by (dtac lists_types 1);
byev [etac (lists.mk_cases "x # xs : lists (Collect P)") 1,
  etac (lists_IntI RS lists.induct) 1,
  atac 1];
by (fast_tac (claset() addss simpset()) 1);
by (fast_tac (claset() addss simpset()) 1);
by (eres_inst_tac [("x","e")] allE 1);
by (eres_inst_tac [("x","T")] allE 1);
by (eres_inst_tac [("x","u $ a[u/i]")] allE 1);
by (eres_inst_tac [("x","0")] allE 1);
by (fast_tac (claset()
  addSIs [list_app_typeI, lift_types, subst_lemma, substs_lemma]
  addss simpset()) 1);
by (eres_inst_tac [("x", "Ta")] allE 1);
by (etac impE 1);
by (Simp_tac 1);
by (eres_inst_tac [("x", "lift u 0 $ Var 0")] allE 1);
by (etac impE 1);
by (assume_tac 1);
by (eres_inst_tac [("x", "e")] allE 1);
by (eres_inst_tac [("x", "Ts =>> T")] allE 1);
by (eres_inst_tac [("x", "a[u/i]")] allE 1);
by (eres_inst_tac [("x", "0")] allE 1);
by (etac impE 1);
by (Simp_tac 1);
by (rtac typing.APP 1);
by (subgoal_tac "(%j. if j = 0 then Ta else e (j - 1)) =  \
 \  (%j. if j < 0 then e j else if j = 0 then Ta else e (j - 1))" 1);
byev [etac ssubst 1, rtac lift_type' 1];
by (assume_tac 1);
by (rtac ext 1);
by (case_tac "j" 1);
by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
by (rtac typing.VAR 1);
by (Simp_tac 1);
by (fast_tac (claset() addSIs [subst_lemma]) 1);
(** n~=i **)
by (dtac list_app_typeD 1);
by (etac exE 1);
by (etac conjE 1);
by (dtac lists_types 1);
by (subgoal_tac "map (%x. x[u/i]) rs : lists IT" 1);
by (asm_simp_tac (simpset() addsimps [subst_Var]) 1);
by (Fast_tac 1);
by (etac (lists_IntI RS lists.induct) 1);
by (assume_tac 1);
by (fast_tac (claset() addss simpset()) 1);
by (fast_tac (claset() addss simpset()) 1);
(** Lambda **)
by (fast_tac (claset() addss simpset()) 1);
(** Beta **)
by (strip_tac 1);
by (Simp_tac 1);
by (rtac IT.BetaI 1);
by (simp_tac (simpset() delsimps [subst_map]
  addsimps [subst_subst, subst_map RS sym]) 1);
by (dtac subject_reduction 1);
by (rtac apps_preserves_beta 1);
by (rtac beta.beta 1);
by (Fast_tac 1);
by (dtac list_app_typeD 1);
by (Fast_tac 1);
qed_spec_mp "subst_type_IT";

(**** main theorem: well-typed terms are strongly normalizing ****)

Goal "e |- t : T ==> t : IT";
by (etac typing.induct 1);
by (rtac Var_IT 1);
by (etac IT.LambdaI 1);
by (subgoal_tac "(Var 0 $ lift t 0)[s/0] : IT" 1);
by (Asm_full_simp_tac 1);
by (rtac subst_type_IT 1);
by (rtac (rewrite_rule (map mk_meta_eq [foldl_Nil, foldl_Cons])
  (lists.Nil RSN (2, lists.Cons RS IT.VarI))) 1);
by (etac lift_IT 1);
by (rtac typing.APP 1);
by (rtac typing.VAR 1);
by (Simp_tac 1);
by (etac lift_type' 1);
by (assume_tac 1);
by (assume_tac 1);
qed "type_implies_IT";

bind_thm ("type_implies_termi", type_implies_IT RS IT_implies_termi);
