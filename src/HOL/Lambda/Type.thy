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

constdefs
  shift :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" ("_<_:_>" [50,0,0] 51)
  "e<i:a> == \<lambda>j. if j < i then e j else if j = i then a else e (j - 1)"

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

lemma "e |- Abs (Abs (Abs (Var 1 $ (Var 2 $ Var 1 $ Var 0)))) : ?T"
  by force

lemma "e |- Abs (Abs (Abs (Var 2 $ Var 0 $ (Var 1 $ Var 0)))) : ?T"
  by force


subsection {* @{text n}-ary function types *}

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

lemma list_app_typeE:
  "e |- t $$ ts : T \<Longrightarrow> (\<And>Ts. e |- t : Ts =>> T \<Longrightarrow> types e ts Ts \<Longrightarrow> C) \<Longrightarrow> C"
  by (insert list_app_typeD) fast

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

lemma lift_map [simp]:
    "\<And>t. lift (t $$ ts) i = lift t i $$ map (\<lambda>t. lift t i) ts"
  by (induct ts) simp_all

lemma subst_map [simp]:
    "\<And>t. subst (t $$ ts) u i = subst t u i $$ map (\<lambda>t. subst t u i) ts"
  by (induct ts) simp_all

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

lemma lifts_IT:
    "ts \<in> lists IT \<Longrightarrow> map (\<lambda>t. lift t 0) ts \<in> lists IT"
  by (induct ts) auto

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

lemma lift_type':
  "e |- t : T ==> e<i:U> |- lift t i : T"
proof -
  assume "e |- t : T"
  thus "\<And>i U. e<i:U> |- lift t i : T"
    by induct (auto simp add: shift_def)
qed

lemma lift_type [intro!]:
    "e |- t : T ==> nat_case U e |- lift t 0 : T"
  apply (subgoal_tac "nat_case U e = e<0:U>")
   apply (erule ssubst)
   apply (erule lift_type')
  apply (rule ext)
  apply (case_tac x)
   apply (simp_all add: shift_def)
  done

lemma lift_types [rule_format]:
  "\<forall>Ts. types e ts Ts --> types (e<i:U>) (map (\<lambda>t. lift t i) ts) Ts"
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
  "e |- t : T ==> \<forall>e' i U u. e' |- u : U -->
    e = e'<i:U> --> e' |- t[u/i] : T"
  apply (unfold shift_def)
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
  apply auto
  done

lemma substs_lemma [rule_format]:
  "e |- u : T ==> \<forall>Ts. types (e<i:T>) ts Ts -->
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
   apply assumption
  apply (rule refl)
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
     apply assumption
    apply (rule ext)
    apply (case_tac x)
     apply (auto simp add: shift_def)
  done


subsection {* Additional lemmas *}

lemma app_last: "(t $$ ts) $ u = t $$ (ts @ [u])"
  by simp

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

lemma type_induct [induct type]:
  "(\<And>T. (\<And>T1 T2. T = T1 => T2 \<Longrightarrow> P T1) \<Longrightarrow>
   (\<And>T1 T2. T = T1 => T2 \<Longrightarrow> P T2) \<Longrightarrow> P T) \<Longrightarrow> P T"
proof -
  case rule_context
  show ?thesis
  proof (induct T)
    case Atom
    show ?case by (rule rule_context) simp_all
  next
    case Fun
    show ?case  by (rule rule_context) (insert Fun, simp_all)
  qed
qed


subsection {* Well-typed substitution preserves termination *}

lemma subst_type_IT:
  "\<And>t e T u i. t \<in> IT \<Longrightarrow> e<i:U> |- t : T \<Longrightarrow>
    u \<in> IT \<Longrightarrow> e |- u : U \<Longrightarrow> t[u/i] \<in> IT"
  (is "PROP ?P U" is "\<And>t e T u i. _ \<Longrightarrow> PROP ?Q t e T u i U")
proof (induct U)
  fix T t
  assume MI1: "\<And>T1 T2. T = T1 => T2 \<Longrightarrow> PROP ?P T1"
  assume MI2: "\<And>T1 T2. T = T1 => T2 \<Longrightarrow> PROP ?P T2"
  assume "t \<in> IT"
  thus "\<And>e T' u i. PROP ?Q t e T' u i T"
  proof induct
    fix e T' u i
    assume uIT: "u : IT"
    assume uT: "e |- u : T"
    {
      case (Var n rs)
      assume nT: "e<i:T> |- Var n $$ rs : T'"
      let ?ty = "{t. \<exists>T'. e<i:T> |- t : T'}"
      let ?R = "\<lambda>t. \<forall>e T' u i.
	e<i:T> |- t : T' \<longrightarrow> u \<in> IT \<longrightarrow> e |- u : T \<longrightarrow> t[u/i] \<in> IT"
      show "(Var n $$ rs)[u/i] \<in> IT"
      proof (cases "n = i")
	case True
	show ?thesis
	proof (cases rs)
	  case Nil
	  with uIT True show ?thesis by simp
	next
	  case (Cons a as)
	  with nT have "e<i:T> |- Var n $ a $$ as : T'" by simp
	  then obtain Ts
	    where headT: "e<i:T> |- Var n $ a : Ts =>> T'"
	    and argsT: "types (e<i:T>) as Ts"
	    by (rule list_app_typeE)
	  from headT obtain T''
	    where varT: "e<i:T> |- Var n : T'' => (Ts =>> T')"
	    and argT: "e<i:T> |- a : T''"
	    by cases simp_all
	  from varT True have T: "T = T'' => (Ts =>> T')"
	    by cases (auto simp add: shift_def)
	  with uT have uT': "e |- u : T'' => (Ts =>> T')" by simp
	  from Var have SI: "?R a" by cases (simp_all add: Cons)
	  from T have "(Var 0 $$ map (\<lambda>t. lift t 0)
            (map (\<lambda>t. t[u/i]) as))[(u $ a[u/i])/0] \<in> IT"
	  proof (rule MI2)
	    from T have "(lift u 0 $ Var 0)[a[u/i]/0] \<in> IT"
	    proof (rule MI1)
	      have "lift u 0 : IT" by (rule lift_IT)
	      thus "lift u 0 $ Var 0 \<in> IT" by (rule app_Var_IT)
	      show "e<0:T''> |- lift u 0 $ Var 0 : Ts =>> T'"
	      proof (rule typing.App)
		show "e<0:T''> |- lift u 0 : T'' => (Ts =>> T')"
		  by (rule lift_type') (rule uT')
		show "e<0:T''> |- Var 0 : T''"
		  by (rule typing.Var) (simp add: shift_def)
	      qed
	      from argT uIT uT show "a[u/i] : IT"
		by (rule SI[rule_format])
	      from argT uT show "e |- a[u/i] : T''"
		by (rule subst_lemma) (simp add: shift_def)
	    qed
	    thus "u $ a[u/i] \<in> IT" by simp
	    from Var have "as : lists {t. ?R t}"
	      by cases (simp_all add: Cons)
	    moreover from argsT have "as : lists ?ty"
	      by (rule lists_types)
	    ultimately have "as : lists ({t. ?R t} \<inter> ?ty)"
	      by (rule lists_IntI)
	    hence "map (\<lambda>t. lift t 0) (map (\<lambda>t. t[u/i]) as) \<in> lists IT"
	      (is "(?ls as) \<in> _")
	    proof induct
	      case Nil
	      show ?case by fastsimp
	    next
	      case (Cons b bs)
	      hence I: "?R b" by simp
	      from Cons obtain U where "e<i:T> |- b : U" by fast
	      with uT uIT I have "b[u/i] : IT" by simp
	      hence "lift (b[u/i]) 0 : IT" by (rule lift_IT)
	      hence "lift (b[u/i]) 0 # ?ls bs \<in> lists IT"
		by (rule lists.Cons) (rule Cons)
	      thus ?case by simp
	    qed
	    thus "Var 0 $$ ?ls as \<in> IT" by (rule IT.Var)
	    have "e<0:Ts =>> T'> |- Var 0 : Ts =>> T'"
	      by (rule typing.Var) (simp add: shift_def)
	    moreover from uT argsT have "types e (map (\<lambda>t. t[u/i]) as) Ts"
	      by (rule substs_lemma)
	    hence "types (e<0:Ts =>> T'>) (?ls as) Ts"
	      by (rule lift_types)
	    ultimately show "e<0:Ts =>> T'> |- Var 0 $$ ?ls as : T'"
	      by (rule list_app_typeI)
	    from argT uT have "e |- a[u/i] : T''"
	      by (rule subst_lemma) (rule refl)
	    with uT' show "e |- u $ a[u/i] : Ts =>> T'"
	      by (rule typing.App)
	  qed
	  with Cons True show ?thesis
	    by (simp add: map_compose [symmetric] o_def)
	qed
      next
	case False
	from Var have "rs : lists {t. ?R t}" by simp
	moreover from nT obtain Ts where "types (e<i:T>) rs Ts"
	  by (rule list_app_typeE)
	hence "rs : lists ?ty" by (rule lists_types)
	ultimately have "rs : lists ({t. ?R t} \<inter> ?ty)"
	  by (rule lists_IntI)
	hence "map (\<lambda>x. x[u/i]) rs \<in> lists IT"
	proof induct
	  case Nil
	  show ?case by fastsimp
	next
	  case (Cons a as)
	  hence I: "?R a" by simp
	  from Cons obtain U where "e<i:T> |- a : U" by fast
	  with uT uIT I have "a[u/i] : IT" by simp
	  hence "a[u/i] # map (\<lambda>t. t[u/i]) as \<in> lists IT"
	    by (rule lists.Cons) (rule Cons)
	  thus ?case by simp
	qed
	with False show ?thesis by (auto simp add: subst_Var)
      qed
    next
      case (Lambda r)
      assume "e<i:T> |- Abs r : T'"
	and "\<And>e T' u i. PROP ?Q r e T' u i T"
      with uIT uT show "Abs r[u/i] \<in> IT"
	by (fastsimp simp add: shift_def)
    next
      case (Beta r a as)
      assume T: "e<i:T> |- Abs r $ a $$ as : T'"
      assume SI1: "\<And>e T' u i. PROP ?Q (r[a/0] $$ as) e T' u i T"
      assume SI2: "\<And>e T' u i. PROP ?Q a e T' u i T"
      have "Abs (r[lift u 0/Suc i]) $ a[u/i] $$ map (\<lambda>t. t[u/i]) as \<in> IT"
      proof (rule IT.Beta)
	have "Abs r $ a $$ as -> r[a/0] $$ as"
	  by (rule apps_preserves_beta) (rule beta.beta)
	with T have "e<i:T> |- r[a/0] $$ as : T'"
	  by (rule subject_reduction)
	hence "(r[a/0] $$ as)[u/i] \<in> IT"
	  by (rule SI1)
	thus "r[lift u 0/Suc i][a[u/i]/0] $$ map (\<lambda>t. t[u/i]) as \<in> IT"
	  by (simp del: subst_map add: subst_subst subst_map [symmetric])
	from T obtain U where "e<i:T> |- Abs r $ a : U"
	  by (rule list_app_typeE) fast
	then obtain T'' where "e<i:T> |- a : T''" by cases simp_all
	thus "a[u/i] \<in> IT" by (rule SI2)
      qed
      thus "(Abs r $ a $$ as)[u/i] \<in> IT" by simp
    }
  qed
qed

subsection {* Well-typed terms are strongly normalizing *}

lemma type_implies_IT: "e |- t : T ==> t \<in> IT"
proof -
  assume "e |- t : T"
  thus ?thesis
  proof induct
    case Var
    show ?case by (rule Var_IT)
  next
    case Abs
    show ?case by (rule IT.Lambda)
  next
    case (App T U e s t)
    have "(Var 0 $ lift t 0)[s/0] \<in> IT"
    proof (rule subst_type_IT)
      have "lift t 0 : IT" by (rule lift_IT)
      hence "[lift t 0] : lists IT" by (rule lists.Cons) (rule lists.Nil)
      hence "Var 0 $$ [lift t 0] : IT" by (rule IT.Var)
      also have "(Var 0 $$ [lift t 0]) = (Var 0 $ lift t 0)" by simp
      finally show "\<dots> : IT" .
      have "e<0:T => U> |- Var 0 : T => U"
	by (rule typing.Var) (simp add: shift_def)
      moreover have "e<0:T => U> |- lift t 0 : T"
	by (rule lift_type')
      ultimately show "e<0:T => U> |- Var 0 $ lift t 0 : U"
	by (rule typing.App)
    qed
    thus ?case by simp
  qed
qed

theorem type_implies_termi: "e |- t : T ==> t \<in> termi beta"
proof -
  assume "e |- t : T"
  hence "t \<in> IT" by (rule type_implies_IT)
  thus ?thesis by (rule IT_implies_termi)
qed

end
