(*  Title:      HOL/Lambda/Type.thy
    ID:         $Id$
    Author:     Stefan Berghofer
    Copyright   2000 TU Muenchen

Simply-typed lambda terms.  Subject reduction and strong normalization
of simply-typed lambda terms.  Partly based on a paper proof by Ralph
Matthes.
*)

theory Type = InductTermi:

datatype type =
    Atom nat
  | Fun type type     (infixr "=>" 200)

consts
  typing :: "((nat => type) * dB * type) set"

syntax
  "_typing" :: "[nat => type, dB, type] => bool"   ("_ |- _ : _" [50,50,50] 50)
  "_funs"   :: "[type list, type] => type"         (infixl "=>>" 150)

translations
  "env |- t : T" == "(env, t, T) : typing"
  "Ts =>> T" == "foldr Fun Ts T"

declare IT.intros [intro!]     (* FIXME *)

inductive typing
intros [intro!]
  Var: "env x = T ==> env |- Var x : T"
  Abs: "(nat_case T env) |- t : U ==> env |- (Abs t) : (T => U)"
  App: "env |- s : T => U ==> env |- t : T ==> env |- (s $ t) : U"

consts
  "types" :: "[nat => type, dB list, type list] => bool"
primrec
  "types e [] Ts = (Ts = [])"
  "types e (t # ts) Ts =
    (case Ts of
      [] => False
    | T # Ts => e |- t : T & types e ts Ts)"

inductive_cases [elim!] =
  "e |- Var i : T"
  "e |- t $ u : T"
  "e |- Abs t : T"

inductive_cases [elim!] =
  "x # xs : lists S"


text {* Some tests. *}

lemma "\<exists>T U. e |- Abs (Abs (Abs (Var 1 $ (Var 2 $ Var 1 $ Var 0)))) : T \<and> U = T"
  apply (intro exI conjI)
  apply force
  apply (rule refl)
  done

lemma "\<exists>T U. e |- Abs (Abs (Abs (Var 2 $ Var 0 $ (Var 1 $ Var 0)))) : T \<and> U = T";
  apply (intro exI conjI)
  apply force
  apply (rule refl)
  done


text {* n-ary function types *}

lemma list_app_typeD [rulify]:
    "\<forall>t T. e |- t $$ ts : T --> (\<exists>Ts. e |- t : Ts =>> T \<and> types e ts Ts)"
  apply (induct_tac ts)
   apply simp
  apply (intro strip)
  apply simp
  apply (erule_tac x = "t $ a" in allE)
  apply (erule_tac x = T in allE)
  apply (erule impE)
   apply assumption
  apply (elim exE conjE)
  apply (mk_cases_tac "e |- t $ u : T")
  apply (rule_tac x = "Ta # Ts" in exI)
  apply simp
  done

lemma list_app_typeI [rulify]:
  "\<forall>t T Ts. e |- t : Ts =>> T --> types e ts Ts --> e |- t $$ ts : T"
  apply (induct_tac ts)
   apply (intro strip)
   apply simp
  apply (intro strip)
  apply (case_tac Ts)
   apply simp
  apply simp
  apply (erule_tac x = "t $ a" in allE)
  apply (erule_tac x = T in allE)
  apply (erule_tac x = lista in allE)
  apply (erule impE)
   apply (erule conjE)
   apply (erule typing.App)
   apply assumption
  apply blast
  done

lemma lists_types [rulify]:
    "\<forall>Ts. types e ts Ts --> ts : lists {t. \<exists>T. e |- t : T}"
  apply (induct_tac ts)
   apply (intro strip)
   apply (case_tac Ts)
     apply simp
     apply (rule lists.Nil)
    apply simp
  apply (intro strip)
  apply (case_tac Ts)
   apply simp
  apply simp
  apply (rule lists.Cons)
   apply blast
  apply blast
  done


text {* lifting preserves termination and well-typedness *}

lemma lift_map [rulify, simp]:
    "\<forall>t. lift (t $$ ts) i = lift t i $$ map (\<lambda>t. lift t i) ts"
  apply (induct_tac ts)
  apply simp_all
  done

lemma subst_map [rulify, simp]:
  "\<forall>t. subst (t $$ ts) u i = subst t u i $$ map (\<lambda>t. subst t u i) ts"
  apply (induct_tac ts)
  apply simp_all
  done

lemma lift_IT [rulify, intro!]:
    "t : IT ==> \<forall>i. lift t i : IT"
  apply (erule IT.induct)
    apply (rule allI)
    apply (simp (no_asm))
    apply (rule conjI)
     apply
      (rule impI,
       rule IT.VarI,
       erule lists.induct,
       simp (no_asm),
       rule lists.Nil,
       simp (no_asm),
       erule IntE,
       rule lists.Cons,
       blast,
       assumption)+
     apply auto
   done

lemma lifts_IT [rulify]:
    "ts : lists IT --> map (\<lambda>t. lift t 0) ts : lists IT"
  apply (induct_tac ts)
   apply auto
  done     


lemma shift_env [simp]:
 "nat_case T
    (\<lambda>j. if j < i then e j else if j = i then Ua else e (j - 1)) =
    (\<lambda>j. if j < Suc i then nat_case T e j else if j = Suc i then Ua
          else nat_case T e (j - 1))"
  apply (rule ext)
  apply (case_tac j)
   apply simp
  apply (case_tac nat)
  apply simp_all
  done

lemma lift_type' [rulify]:
  "e |- t : T ==> \<forall>i U.
    (\<lambda>j. if j < i then e j
          else if j = i then U 
          else e (j - 1)) |- lift t i : T"
  apply (erule typing.induct)
    apply auto
  done


lemma lift_type [intro!]:
  "e |- t : T ==> nat_case U e |- lift t 0 : T"
  apply (subgoal_tac
    "nat_case U e =
      (\<lambda>j. if j < 0 then e j
            else if j = 0 then U else e (j - 1))")
   apply (erule ssubst)
   apply (erule lift_type')
  apply (rule ext)
  apply (case_tac j)
   apply simp_all
  done

lemma lift_types:
  "\<forall>Ts. types e ts Ts -->
    types (\<lambda>j. if j < i then e j
                else if j = i then U
                else e (j - 1)) (map (\<lambda>t. lift t i) ts) Ts"
  apply (induct_tac ts)
   apply simp
  apply (intro strip)
  apply (case_tac Ts)
   apply simp_all
  apply (rule lift_type')
  apply (erule conjunct1)
  done


text {* substitution lemma *}

lemma subst_lemma [rulify]:
 "e |- t : T ==> \<forall>e' i U u.
    e = (\<lambda>j. if j < i then e' j
              else if j = i then U
              else e' (j-1)) -->
    e' |- u : U --> e' |- t[u/i] : T"
  apply (erule typing.induct)
    apply (intro strip)
    apply (case_tac "x = i")
     apply simp
    apply (frule linorder_neq_iff [RS iffD1])
    apply (erule disjE)
     apply simp
     apply (rule typing.Var)
     apply assumption
    apply (frule order_less_not_sym)
    apply (simp only: subst_gt split: split_if add: if_False)
    apply (rule typing.Var)
    apply assumption
   apply fastsimp
  apply fastsimp
  done

lemma substs_lemma [rulify]:
  "e |- u : T ==>
    \<forall>Ts. types (\<lambda>j. if j < i then e j
                     else if j = i then T else e (j - 1)) ts Ts -->
      types e (map (%t. t[u/i]) ts) Ts"
  apply (induct_tac ts)
   apply (intro strip)
   apply (case_tac Ts)
    apply simp
   apply simp
  apply (intro strip)
  apply (case_tac Ts)
   apply simp
  apply simp
  apply (erule conjE)
  apply (erule subst_lemma)
  apply (rule refl)
  apply assumption
  done


text {* subject reduction *}

lemma subject_reduction [rulify]:
    "e |- t : T ==> \<forall>t'. t -> t' --> e |- t' : T"
  apply (erule typing.induct)
    apply blast
   apply blast
  apply (intro strip)
  apply (mk_cases_tac "s $ t -> t'")
    apply hyp_subst
    apply (mk_cases_tac "env |- Abs t : T => U")
    apply (rule subst_lemma)
      apply assumption
     prefer 2
     apply assumption
    apply (rule ext)
    apply (case_tac j)
     apply auto
  done

text {* additional lemmas *}

lemma app_last: "(t $$ ts) $ u = t $$ (ts @ [u])"
  apply simp
  done


lemma subst_Var_IT [rulify]: "r : IT ==> \<forall>i j. r[Var i/j] : IT"
  apply (erule IT.induct)
    txt {* Var *}
    apply (intro strip)
    apply (simp (no_asm) add: subst_Var)
    apply
    ((rule conjI impI)+,
      rule IT.VarI,
      erule lists.induct,
      simp (no_asm),
      rule lists.Nil,
      simp (no_asm),
      erule IntE,
      erule CollectE,
      rule lists.Cons,
      fast,
      assumption)+
   txt {* Lambda *}
   apply (intro strip)
   apply simp
   apply (rule IT.LambdaI)
   apply fast
  txt {* Beta *}
  apply (intro strip)
  apply (simp (no_asm_use) add: subst_subst [RS sym])
  apply (rule IT.BetaI)
   apply auto
  done

lemma Var_IT: "Var n \<in> IT"
proof -
  have "Var n $$ [] \<in> IT"
    apply (rule IT.VarI)
    apply (rule lists.Nil)
    done
  then show ?thesis by simp
qed


lemma app_Var_IT: "t : IT ==> t $ Var i : IT"
  apply (erule IT.induct)
    apply (subst app_last)
    apply (rule IT.VarI)
    apply simp
    apply (rule lists.Cons)
     apply (rule Var_IT)
    apply (rule lists.Nil)
   apply (rule IT.BetaI [where ?ss = "[]", unfold foldl_Nil [RS eq_reflection]])
    apply (erule subst_Var_IT)
   apply (rule Var_IT)
  apply (subst app_last)
  apply (rule IT.BetaI)
   apply (subst app_last [RS sym])
   apply assumption
  apply assumption
  done


text {* Well-typed substitution preserves termination. *}

lemma subst_type_IT [rulify]:
  "\<forall>t. t : IT --> (\<forall>e T u i.
    (\<lambda>j. if j < i then e j
          else if j = i then U
          else e (j - 1)) |- t : T -->
    u : IT --> e |- u : U --> t[u/i] : IT)"
  apply (rule_tac f = size and a = U in measure_induct)
  apply (rule allI)
  apply (rule impI)
  apply (erule IT.induct)
    txt {* Var *}
    apply (intro strip)
    apply (case_tac "n = i")
     txt {* n=i *}
     apply (case_tac rs)
      apply simp
     apply simp
     apply (drule list_app_typeD)
     apply (elim exE conjE)
     apply (mk_cases_tac "e |- t $ u : T")
     apply (mk_cases_tac "e |- Var i : T")
     apply (drule_tac s = "(?T::type) => ?U" in sym)
     apply simp
     apply (subgoal_tac "lift u 0 $ Var 0 : IT")
      prefer 2
      apply (rule app_Var_IT)
      apply (erule lift_IT)
     apply (subgoal_tac "(lift u 0 $ Var 0)[a[u/i]/0] : IT")
      apply (simp (no_asm_use))
      apply (subgoal_tac "(Var 0 $$ map (%t. lift t 0)
        (map (%t. t[u/i]) list))[(u $ a[u/i])/0] : IT")
       apply (simp (no_asm_use) del: map_compose add: map_compose [RS sym] o_def)
      apply (erule_tac x = "Ts =>> T" in allE)
      apply (erule impE)
       apply simp
      apply (erule_tac x = "Var 0 $$
        map (%t. lift t 0) (map (%t. t[u/i]) list)" in allE)
      apply (erule impE)
       apply (rule IT.VarI)
       apply (rule lifts_IT)
       apply (drule lists_types)
       apply
        (mk_cases_tac "x # xs : lists (Collect P)",
	 erule lists_IntI [RS lists.induct],
	 assumption)
	apply fastsimp
       apply fastsimp
       apply (erule_tac x = e in allE)
       apply (erule_tac x = T in allE)
       apply (erule_tac x = "u $ a[u/i]" in allE)
       apply (erule_tac x = 0 in allE)
       apply (force intro!: lift_types list_app_typeI substs_lemma subst_lemma)

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
by (rtac typing.APP 1);
by (etac lift_type' 1);
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

done





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

