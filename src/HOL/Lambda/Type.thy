(*  Title:      HOL/Lambda/Type.thy
    ID:         $Id$
    Author:     Stefan Berghofer
    Copyright   2000 TU Muenchen
*)

header {* Simply-typed lambda terms: subject reduction and strong
  normalization *}

theory Type = InductTermi:

text_raw {*
  \footnote{Formalization by Stefan Berghofer.  Partly based on a
  paper proof by Ralph Matthes.}
*}


subsection {* Types and typing rules *}

datatype type =
    Atom nat
  | Fun type type  (infixr "=>" 200)

consts
  typing :: "((nat => type) \<times> dB \<times> type) set"

syntax
  "_typing" :: "[nat => type, dB, type] => bool"  ("_ |- _ : _" [50,50,50] 50)
  "_funs" :: "[type list, type] => type"  (infixl "=>>" 150)
translations
  "env |- t : T" == "(env, t, T) \<in> typing"
  "Ts =>> T" == "foldr Fun Ts T"

inductive typing
  intros
    Var [intro!]: "env x = T ==> env |- Var x : T"
    Abs [intro!]: "(nat_case T env) |- t : U ==> env |- Abs t : (T => U)"
    App [intro!]: "env |- s : T => U ==> env |- t : T ==> env |- (s $ t) : U"

inductive_cases [elim!]:
  "e |- Var i : T"
  "e |- t $ u : T"
  "e |- Abs t : T"

consts
  "types" :: "[nat => type, dB list, type list] => bool"
primrec
  "types e [] Ts = (Ts = [])"
  "types e (t # ts) Ts =
    (case Ts of
      [] => False
    | T # Ts => e |- t : T \<and> types e ts Ts)"

inductive_cases [elim!]:
  "x # xs \<in> lists S"

declare IT.intros [intro!]


subsection {* Some examples *}

lemma "e |- Abs (Abs (Abs (Var 1 $ (Var # 2 $ Var 1 $ Var 0)))) : ?T"
  apply force
  done

lemma "e |- Abs (Abs (Abs (Var # 2 $ Var 0 $ (Var 1 $ Var 0)))) : ?T"
  apply force
  done


text {* Iterated function types *}

lemma list_app_typeD [rule_format]:
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
  apply (ind_cases "e |- t $ u : T")
  apply (rule_tac x = "Ta # Ts" in exI)
  apply simp
  done

lemma list_app_typeI [rule_format]:
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

lemma lists_types [rule_format]:
    "\<forall>Ts. types e ts Ts --> ts \<in> lists {t. \<exists>T. e |- t : T}"
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


subsection {* Lifting preserves termination and well-typedness *}

lemma lift_map [rule_format, simp]:
    "\<forall>t. lift (t $$ ts) i = lift t i $$ map (\<lambda>t. lift t i) ts"
  apply (induct_tac ts)
   apply simp_all
  done

lemma subst_map [rule_format, simp]:
  "\<forall>t. subst (t $$ ts) u i = subst t u i $$ map (\<lambda>t. subst t u i) ts"
  apply (induct_tac ts)
   apply simp_all
  done

lemma lift_IT [rule_format, intro!]:
    "t \<in> IT ==> \<forall>i. lift t i \<in> IT"
  apply (erule IT.induct)
    apply (rule allI)
    apply (simp (no_asm))
    apply (rule conjI)
     apply
      (rule impI,
       rule IT.Var,
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

lemma lifts_IT [rule_format]:
    "ts \<in> lists IT --> map (\<lambda>t. lift t 0) ts \<in> lists IT"
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

lemma lift_type' [rule_format]:
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

lemma lift_types [rule_format]:
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


subsection {* Substitution lemmas *}

lemma subst_lemma [rule_format]:
  "e |- t : T ==> \<forall>e' i U u.
    e = (\<lambda>j. if j < i then e' j
              else if j = i then U
              else e' (j - 1)) -->
    e' |- u : U --> e' |- t[u/i] : T"
  apply (erule typing.induct)
    apply (intro strip)
    apply (case_tac "x = i")
     apply simp
    apply (frule linorder_neq_iff [THEN iffD1])
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

lemma substs_lemma [rule_format]:
  "e |- u : T ==>
    \<forall>Ts. types (\<lambda>j. if j < i then e j
                     else if j = i then T else e (j - 1)) ts Ts -->
      types e (map (\<lambda>t. t[u/i]) ts) Ts"
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


subsection {* Subject reduction *}

lemma subject_reduction [rule_format]:
    "e |- t : T ==> \<forall>t'. t -> t' --> e |- t' : T"
  apply (erule typing.induct)
    apply blast
   apply blast
  apply (intro strip)
  apply (ind_cases "s $ t -> t'")
    apply hypsubst
    apply (ind_cases "env |- Abs t : T => U")
    apply (rule subst_lemma)
      apply assumption
     prefer 2
     apply assumption
    apply (rule ext)
    apply (case_tac j)
     apply auto
  done


subsection {* Additional lemmas *}

lemma app_last: "(t $$ ts) $ u = t $$ (ts @ [u])"
  apply simp
  done

lemma subst_Var_IT [rule_format]: "r \<in> IT ==> \<forall>i j. r[Var i/j] \<in> IT"
  apply (erule IT.induct)
    txt {* Case @{term Var}: *}
    apply (intro strip)
    apply (simp (no_asm) add: subst_Var)
    apply
    ((rule conjI impI)+,
      rule IT.Var,
      erule lists.induct,
      simp (no_asm),
      rule lists.Nil,
      simp (no_asm),
      erule IntE,
      erule CollectE,
      rule lists.Cons,
      fast,
      assumption)+
   txt {* Case @{term Lambda}: *}
   apply (intro strip)
   apply simp
   apply (rule IT.Lambda)
   apply fast
  txt {* Case @{term Beta}: *}
  apply (intro strip)
  apply (simp (no_asm_use) add: subst_subst [symmetric])
  apply (rule IT.Beta)
   apply auto
  done

lemma Var_IT: "Var n \<in> IT"
  apply (subgoal_tac "Var n $$ [] \<in> IT")
   apply simp
  apply (rule IT.Var)
  apply (rule lists.Nil)
  done

lemma app_Var_IT: "t \<in> IT ==> t $ Var i \<in> IT"
  apply (erule IT.induct)
    apply (subst app_last)
    apply (rule IT.Var)
    apply simp
    apply (rule lists.Cons)
     apply (rule Var_IT)
    apply (rule lists.Nil)
   apply (rule IT.Beta [where ?ss = "[]", unfolded foldl_Nil [THEN eq_reflection]])
    apply (erule subst_Var_IT)
   apply (rule Var_IT)
  apply (subst app_last)
  apply (rule IT.Beta)
   apply (subst app_last [symmetric])
   apply assumption
  apply assumption
  done


subsection {* Well-typed substitution preserves termination *}

lemma subst_type_IT [rule_format]:
  "\<forall>t. t \<in> IT --> (\<forall>e T u i.
    (\<lambda>j. if j < i then e j
          else if j = i then U
          else e (j - 1)) |- t : T -->
    u \<in> IT --> e |- u : U --> t[u/i] \<in> IT)"
  apply (rule_tac f = size and a = U in measure_induct)
  apply (rule allI)
  apply (rule impI)
  apply (erule IT.induct)
    txt {* Case @{term Var}: *}
    apply (intro strip)
    apply (case_tac "n = i")
     txt {* Case @{term "n = i"}: *}
     apply (case_tac rs)
      apply simp
     apply simp
     apply (drule list_app_typeD)
     apply (elim exE conjE)
     apply (ind_cases "e |- t $ u : T")
     apply (ind_cases "e |- Var i : T")
     apply (drule_tac s = "(?T::type) => ?U" in sym)
     apply simp
     apply (subgoal_tac "lift u 0 $ Var 0 \<in> IT")
      prefer 2
      apply (rule app_Var_IT)
      apply (erule lift_IT)
     apply (subgoal_tac "(lift u 0 $ Var 0)[a[u/i]/0] \<in> IT")
      apply (simp (no_asm_use))
      apply (subgoal_tac "(Var 0 $$ map (\<lambda>t. lift t 0)
        (map (\<lambda>t. t[u/i]) list))[(u $ a[u/i])/0] \<in> IT")
       apply (simp (no_asm_use) del: map_compose
	 add: map_compose [symmetric] o_def)
      apply (erule_tac x = "Ts =>> T" in allE)
      apply (erule impE)
       apply simp
      apply (erule_tac x = "Var 0 $$
        map (\<lambda>t. lift t 0) (map (\<lambda>t. t[u/i]) list)" in allE)
      apply (erule impE)
       apply (rule IT.Var)
       apply (rule lifts_IT)
       apply (drule lists_types)
       apply
        (ind_cases "x # xs \<in> lists (Collect P)",
         erule lists_IntI [THEN lists.induct],
         assumption)
        apply fastsimp
       apply fastsimp
      apply (erule_tac x = e in allE)
      apply (erule_tac x = T in allE)
      apply (erule_tac x = "u $ a[u/i]" in allE)
      apply (erule_tac x = 0 in allE)
      apply (fastsimp intro!: list_app_typeI lift_types subst_lemma substs_lemma)
     apply (erule_tac x = Ta in allE)
     apply (erule impE)
      apply simp
     apply (erule_tac x = "lift u 0 $ Var 0" in allE)
     apply (erule impE)
      apply assumption
     apply (erule_tac x = e in allE)
     apply (erule_tac x = "Ts =>> T" in allE)
     apply (erule_tac x = "a[u/i]" in allE)
     apply (erule_tac x = 0 in allE)
     apply (erule impE)
      apply (rule typing.App)
       apply (erule lift_type')
      apply (rule typing.Var)
      apply simp
     apply (fast intro!: subst_lemma)
    txt {* Case @{term "n ~= i"}: *}
    apply (drule list_app_typeD)
    apply (erule exE)
    apply (erule conjE)
    apply (drule lists_types)
    apply (subgoal_tac "map (\<lambda>x. x[u/i]) rs \<in> lists IT")
     apply (simp add: subst_Var)
     apply fast
    apply (erule lists_IntI [THEN lists.induct])
      apply assumption
     apply fastsimp
    apply fastsimp
   txt {* Case @{term Lambda}: *}
   apply fastsimp
  txt {* Case @{term Beta}: *}
  apply (intro strip)
  apply (simp (no_asm))
  apply (rule IT.Beta)
   apply (simp (no_asm) del: subst_map add: subst_subst subst_map [symmetric])
   apply (drule subject_reduction)
    apply (rule apps_preserves_beta)
    apply (rule beta.beta)
   apply fast
  apply (drule list_app_typeD)
  apply fast
  done


subsection {* Main theorem: well-typed terms are strongly normalizing *}

lemma type_implies_IT: "e |- t : T ==> t \<in> IT"
  apply (erule typing.induct)
    apply (rule Var_IT)
   apply (erule IT.Lambda)
  apply (subgoal_tac "(Var 0 $ lift t 0)[s/0] \<in> IT")
   apply simp
  apply (rule subst_type_IT)
  apply (rule lists.Nil
    [THEN [2] lists.Cons [THEN IT.Var], unfolded foldl_Nil [THEN eq_reflection]
      foldl_Cons [THEN eq_reflection]])
      apply (erule lift_IT)
     apply (rule typing.App)
     apply (rule typing.Var)
     apply simp
    apply (erule lift_type')
   apply assumption
  apply assumption
  done

theorem type_implies_termi: "e |- t : T ==> t \<in> termi beta"
  apply (rule IT_implies_termi)
  apply (erule type_implies_IT)
  done

end
