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


subsection {* Environments *}

constdefs
  shift :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"    ("_<_:_>" [90, 0, 0] 91)
  "e<i:a> \<equiv> \<lambda>j. if j < i then e j else if j = i then a else e (j - 1)"
syntax (symbols)
  shift :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"    ("_\<langle>_:_\<rangle>" [90, 0, 0] 91)

lemma shift_eq [simp]: "i = j \<Longrightarrow> (e\<langle>i:T\<rangle>) j = T"
  by (simp add: shift_def)

lemma shift_gt [simp]: "j < i \<Longrightarrow> (e\<langle>i:T\<rangle>) j = e j"
  by (simp add: shift_def)

lemma shift_lt [simp]: "i < j \<Longrightarrow> (e\<langle>i:T\<rangle>) j = e (j - 1)"
  by (simp add: shift_def)

lemma shift_commute [simp]: "e\<langle>i:U\<rangle>\<langle>0:T\<rangle> = e\<langle>0:T\<rangle>\<langle>Suc i:U\<rangle>"
  apply (rule ext)
  apply (case_tac x)
   apply simp
  apply (case_tac nat)
   apply (simp_all add: shift_def)
  done


subsection {* Types and typing rules *}

datatype type =
    Atom nat
  | Fun type type    (infixr "\<Rightarrow>" 200)

consts
  typing :: "((nat \<Rightarrow> type) \<times> dB \<times> type) set"
  typings :: "(nat \<Rightarrow> type) \<Rightarrow> dB list \<Rightarrow> type list \<Rightarrow> bool"

syntax
  "_funs" :: "type list \<Rightarrow> type \<Rightarrow> type"    (infixr "=>>" 200)
  "_typing" :: "(nat \<Rightarrow> type) \<Rightarrow> dB \<Rightarrow> type \<Rightarrow> bool"    ("_ |- _ : _" [50, 50, 50] 50)
  "_typings" :: "(nat \<Rightarrow> type) \<Rightarrow> dB list \<Rightarrow> type list \<Rightarrow> bool"
    ("_ ||- _ : _" [50, 50, 50] 50)
syntax (symbols)
  "_typing" :: "(nat \<Rightarrow> type) \<Rightarrow> dB \<Rightarrow> type \<Rightarrow> bool"    ("_ \<turnstile> _ : _" [50, 50, 50] 50)
syntax (latex)
  "_funs" :: "type list \<Rightarrow> type \<Rightarrow> type"    (infixr "\<Rrightarrow>" 200)
  "_typings" :: "(nat \<Rightarrow> type) \<Rightarrow> dB list \<Rightarrow> type list \<Rightarrow> bool"
    ("_ \<tturnstile> _ : _" [50, 50, 50] 50)
translations
  "Ts \<Rrightarrow> T" \<rightleftharpoons> "foldr Fun Ts T"
  "env \<turnstile> t : T" \<rightleftharpoons> "(env, t, T) \<in> typing"
  "env \<tturnstile> ts : Ts" \<rightleftharpoons> "typings env ts Ts"

inductive typing
  intros
    Var [intro!]: "env x = T \<Longrightarrow> env \<turnstile> Var x : T"
    Abs [intro!]: "env\<langle>0:T\<rangle> \<turnstile> t : U \<Longrightarrow> env \<turnstile> Abs t : (T \<Rightarrow> U)"
    App [intro!]: "env \<turnstile> s : T \<Rightarrow> U \<Longrightarrow> env \<turnstile> t : T \<Longrightarrow> env \<turnstile> (s \<degree> t) : U"

inductive_cases typing_elims [elim!]:
  "e \<turnstile> Var i : T"
  "e \<turnstile> t \<degree> u : T"
  "e \<turnstile> Abs t : T"

primrec
  "(e \<tturnstile> [] : Ts) = (Ts = [])"
  "(e \<tturnstile> (t # ts) : Ts) =
    (case Ts of
      [] \<Rightarrow> False
    | T # Ts \<Rightarrow> e \<turnstile> t : T \<and> e \<tturnstile> ts : Ts)"


subsection {* Some examples *}

lemma "e \<turnstile> Abs (Abs (Abs (Var 1 \<degree> (Var 2 \<degree> Var 1 \<degree> Var 0)))) : ?T"
  by force

lemma "e \<turnstile> Abs (Abs (Abs (Var 2 \<degree> Var 0 \<degree> (Var 1 \<degree> Var 0)))) : ?T"
  by force


subsection {* n-ary function types *}

lemma list_app_typeD:
    "\<And>t T. e \<turnstile> t \<degree>\<degree> ts : T \<Longrightarrow> \<exists>Ts. e \<turnstile> t : Ts \<Rrightarrow> T \<and> e \<tturnstile> ts : Ts"
  apply (induct ts)
   apply simp
  apply atomize
  apply simp
  apply (erule_tac x = "t \<degree> a" in allE)
  apply (erule_tac x = T in allE)
  apply (erule impE)
   apply assumption
  apply (elim exE conjE)
  apply (ind_cases "e \<turnstile> t \<degree> u : T")
  apply (rule_tac x = "Ta # Ts" in exI)
  apply simp
  done

lemma list_app_typeE:
  "e \<turnstile> t \<degree>\<degree> ts : T \<Longrightarrow> (\<And>Ts. e \<turnstile> t : Ts \<Rrightarrow> T \<Longrightarrow> e \<tturnstile> ts : Ts \<Longrightarrow> C) \<Longrightarrow> C"
  by (insert list_app_typeD) fast

lemma list_app_typeI:
    "\<And>t T Ts. e \<turnstile> t : Ts \<Rrightarrow> T \<Longrightarrow> e \<tturnstile> ts : Ts \<Longrightarrow> e \<turnstile> t \<degree>\<degree> ts : T"
  apply (induct ts)
   apply simp
  apply atomize
  apply (case_tac Ts)
   apply simp
  apply simp
  apply (erule_tac x = "t \<degree> a" in allE)
  apply (erule_tac x = T in allE)
  apply (erule_tac x = lista in allE)
  apply (erule impE)
   apply (erule conjE)
   apply (erule typing.App)
   apply assumption
  apply blast
  done

lemma lists_typings:
    "\<And>Ts. e \<tturnstile> ts : Ts \<Longrightarrow> ts \<in> lists {t. \<exists>T. e \<turnstile> t : T}"
  apply (induct ts)
   apply (case_tac Ts)
     apply simp
     apply (rule lists.Nil)
    apply simp
  apply (case_tac Ts)
   apply simp
  apply simp
  apply (rule lists.Cons)
   apply blast
  apply blast
  done


subsection {* Lifting preserves termination and well-typedness *}

lemma lift_map [simp]:
    "\<And>t. lift (t \<degree>\<degree> ts) i = lift t i \<degree>\<degree> map (\<lambda>t. lift t i) ts"
  by (induct ts) simp_all

lemma subst_map [simp]:
    "\<And>t. subst (t \<degree>\<degree> ts) u i = subst t u i \<degree>\<degree> map (\<lambda>t. subst t u i) ts"
  by (induct ts) simp_all

lemma lift_IT [intro!]: "t \<in> IT \<Longrightarrow> (\<And>i. lift t i \<in> IT)"
  apply (induct set: IT)
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

lemma lifts_IT: "ts \<in> lists IT \<Longrightarrow> map (\<lambda>t. lift t 0) ts \<in> lists IT"
  by (induct ts) auto

lemma lift_type [intro!]: "e \<turnstile> t : T \<Longrightarrow> e\<langle>i:U\<rangle> \<turnstile> lift t i : T"
proof -
  assume "e \<turnstile> t : T"
  thus "\<And>i U. e\<langle>i:U\<rangle> \<turnstile> lift t i : T"
    by induct auto
qed

lemma lift_typings:
  "\<And>Ts. e \<tturnstile> ts : Ts \<Longrightarrow> e\<langle>i:U\<rangle> \<tturnstile> (map (\<lambda>t. lift t i) ts) : Ts"
  apply (induct ts)
   apply simp
  apply (case_tac Ts)
   apply auto
  done


subsection {* Substitution lemmas *}

lemma subst_lemma:
    "e \<turnstile> t : T \<Longrightarrow> (\<And>e' i U u. e' \<turnstile> u : U \<Longrightarrow> e = e'\<langle>i:U\<rangle> \<Longrightarrow> e' \<turnstile> t[u/i] : T)"
  apply (induct set: typing)
    apply (rule_tac x = x and y = i in linorder_cases)
      apply auto
  apply blast
  done

lemma substs_lemma:
  "\<And>Ts. e \<turnstile> u : T \<Longrightarrow> e\<langle>i:T\<rangle> \<tturnstile> ts : Ts \<Longrightarrow>
     e \<tturnstile> (map (\<lambda>t. t[u/i]) ts) : Ts"
  apply (induct ts)
   apply (case_tac Ts)
    apply simp
   apply simp
  apply atomize
  apply (case_tac Ts)
   apply simp
  apply simp
  apply (erule conjE)
  apply (erule (1) subst_lemma)
  apply (rule refl)
  done


subsection {* Subject reduction *}

lemma subject_reduction: "e \<turnstile> t : T \<Longrightarrow> (\<And>t'. t -> t' \<Longrightarrow> e \<turnstile> t' : T)"
  apply (induct set: typing)
    apply blast
   apply blast
  apply atomize
  apply (ind_cases "s \<degree> t -> t'")
    apply hypsubst
    apply (ind_cases "env \<turnstile> Abs t : T \<Rightarrow> U")
    apply (rule subst_lemma)
      apply assumption
     apply assumption
    apply (rule ext)
    apply (case_tac x)
     apply auto
  done


subsection {* Additional lemmas *}

lemma app_last: "(t \<degree>\<degree> ts) \<degree> u = t \<degree>\<degree> (ts @ [u])"
  by simp

lemma subst_Var_IT: "r \<in> IT \<Longrightarrow> (\<And>i j. r[Var i/j] \<in> IT)"
  apply (induct set: IT)
    txt {* Case @{term Var}: *}
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
   apply atomize
   apply simp
   apply (rule IT.Lambda)
   apply fast
  txt {* Case @{term Beta}: *}
  apply atomize
  apply (simp (no_asm_use) add: subst_subst [symmetric])
  apply (rule IT.Beta)
   apply auto
  done

lemma Var_IT: "Var n \<in> IT"
  apply (subgoal_tac "Var n \<degree>\<degree> [] \<in> IT")
   apply simp
  apply (rule IT.Var)
  apply (rule lists.Nil)
  done

lemma app_Var_IT: "t \<in> IT \<Longrightarrow> t \<degree> Var i \<in> IT"
  apply (induct set: IT)
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
  "(\<And>T. (\<And>T1 T2. T = T1 \<Rightarrow> T2 \<Longrightarrow> P T1) \<Longrightarrow>
   (\<And>T1 T2. T = T1 \<Rightarrow> T2 \<Longrightarrow> P T2) \<Longrightarrow> P T) \<Longrightarrow> P T"
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
  "\<And>t e T u i. t \<in> IT \<Longrightarrow> e\<langle>i:U\<rangle> \<turnstile> t : T \<Longrightarrow>
    u \<in> IT \<Longrightarrow> e \<turnstile> u : U \<Longrightarrow> t[u/i] \<in> IT"
  (is "PROP ?P U" is "\<And>t e T u i. _ \<Longrightarrow> PROP ?Q t e T u i U")
proof (induct U)
  fix T t
  assume MI1: "\<And>T1 T2. T = T1 \<Rightarrow> T2 \<Longrightarrow> PROP ?P T1"
  assume MI2: "\<And>T1 T2. T = T1 \<Rightarrow> T2 \<Longrightarrow> PROP ?P T2"
  assume "t \<in> IT"
  thus "\<And>e T' u i. PROP ?Q t e T' u i T"
  proof induct
    fix e T' u i
    assume uIT: "u \<in> IT"
    assume uT: "e \<turnstile> u : T"
    {
      case (Var n rs)
      assume nT: "e\<langle>i:T\<rangle> \<turnstile> Var n \<degree>\<degree> rs : T'"
      let ?ty = "{t. \<exists>T'. e\<langle>i:T\<rangle> \<turnstile> t : T'}"
      let ?R = "\<lambda>t. \<forall>e T' u i.
        e\<langle>i:T\<rangle> \<turnstile> t : T' \<longrightarrow> u \<in> IT \<longrightarrow> e \<turnstile> u : T \<longrightarrow> t[u/i] \<in> IT"
      show "(Var n \<degree>\<degree> rs)[u/i] \<in> IT"
      proof (cases "n = i")
        case True
        show ?thesis
        proof (cases rs)
          case Nil
          with uIT True show ?thesis by simp
        next
          case (Cons a as)
          with nT have "e\<langle>i:T\<rangle> \<turnstile> Var n \<degree> a \<degree>\<degree> as : T'" by simp
          then obtain Ts
              where headT: "e\<langle>i:T\<rangle> \<turnstile> Var n \<degree> a : Ts \<Rrightarrow> T'"
              and argsT: "e\<langle>i:T\<rangle> \<tturnstile> as : Ts"
            by (rule list_app_typeE)
          from headT obtain T''
              where varT: "e\<langle>i:T\<rangle> \<turnstile> Var n : T'' \<Rightarrow> Ts \<Rrightarrow> T'"
              and argT: "e\<langle>i:T\<rangle> \<turnstile> a : T''"
            by cases simp_all
          from varT True have T: "T = T'' \<Rightarrow> Ts \<Rrightarrow> T'"
            by cases auto
          with uT have uT': "e \<turnstile> u : T'' \<Rightarrow> Ts \<Rrightarrow> T'" by simp
          from T have "(Var 0 \<degree>\<degree> map (\<lambda>t. lift t 0)
            (map (\<lambda>t. t[u/i]) as))[(u \<degree> a[u/i])/0] \<in> IT"
          proof (rule MI2)
            from T have "(lift u 0 \<degree> Var 0)[a[u/i]/0] \<in> IT"
            proof (rule MI1)
              have "lift u 0 \<in> IT" by (rule lift_IT)
              thus "lift u 0 \<degree> Var 0 \<in> IT" by (rule app_Var_IT)
              show "e\<langle>0:T''\<rangle> \<turnstile> lift u 0 \<degree> Var 0 : Ts \<Rrightarrow> T'"
              proof (rule typing.App)
                show "e\<langle>0:T''\<rangle> \<turnstile> lift u 0 : T'' \<Rightarrow> Ts \<Rrightarrow> T'"
                  by (rule lift_type) (rule uT')
                show "e\<langle>0:T''\<rangle> \<turnstile> Var 0 : T''"
                  by (rule typing.Var) simp
              qed
              from Var have "?R a" by cases (simp_all add: Cons)
              with argT uIT uT show "a[u/i] \<in> IT" by simp
              from argT uT show "e \<turnstile> a[u/i] : T''"
                by (rule subst_lemma) simp
            qed
            thus "u \<degree> a[u/i] \<in> IT" by simp
            from Var have "as \<in> lists {t. ?R t}"
              by cases (simp_all add: Cons)
            moreover from argsT have "as \<in> lists ?ty"
              by (rule lists_typings)
            ultimately have "as \<in> lists ({t. ?R t} \<inter> ?ty)"
              by (rule lists_IntI)
            hence "map (\<lambda>t. lift t 0) (map (\<lambda>t. t[u/i]) as) \<in> lists IT"
              (is "(?ls as) \<in> _")
            proof induct
              case Nil
              show ?case by fastsimp
            next
              case (Cons b bs)
              hence I: "?R b" by simp
              from Cons obtain U where "e\<langle>i:T\<rangle> \<turnstile> b : U" by fast
              with uT uIT I have "b[u/i] \<in> IT" by simp
              hence "lift (b[u/i]) 0 \<in> IT" by (rule lift_IT)
              hence "lift (b[u/i]) 0 # ?ls bs \<in> lists IT"
                by (rule lists.Cons) (rule Cons)
              thus ?case by simp
            qed
            thus "Var 0 \<degree>\<degree> ?ls as \<in> IT" by (rule IT.Var)
            have "e\<langle>0:Ts \<Rrightarrow> T'\<rangle> \<turnstile> Var 0 : Ts \<Rrightarrow> T'"
              by (rule typing.Var) simp
            moreover from uT argsT have "e \<tturnstile> map (\<lambda>t. t[u/i]) as : Ts"
              by (rule substs_lemma)
            hence "e\<langle>0:Ts \<Rrightarrow> T'\<rangle> \<tturnstile> ?ls as : Ts"
              by (rule lift_typings)
            ultimately show "e\<langle>0:Ts \<Rrightarrow> T'\<rangle> \<turnstile> Var 0 \<degree>\<degree> ?ls as : T'"
              by (rule list_app_typeI)
            from argT uT have "e \<turnstile> a[u/i] : T''"
              by (rule subst_lemma) (rule refl)
            with uT' show "e \<turnstile> u \<degree> a[u/i] : Ts \<Rrightarrow> T'"
              by (rule typing.App)
          qed
          with Cons True show ?thesis
            by (simp add: map_compose [symmetric] o_def)
        qed
      next
        case False
        from Var have "rs \<in> lists {t. ?R t}" by simp
        moreover from nT obtain Ts where "e\<langle>i:T\<rangle> \<tturnstile> rs : Ts"
          by (rule list_app_typeE)
        hence "rs \<in> lists ?ty" by (rule lists_typings)
        ultimately have "rs \<in> lists ({t. ?R t} \<inter> ?ty)"
          by (rule lists_IntI)
        hence "map (\<lambda>x. x[u/i]) rs \<in> lists IT"
        proof induct
          case Nil
          show ?case by fastsimp
        next
          case (Cons a as)
          hence I: "?R a" by simp
          from Cons obtain U where "e\<langle>i:T\<rangle> \<turnstile> a : U" by fast
          with uT uIT I have "a[u/i] \<in> IT" by simp
          hence "(a[u/i] # map (\<lambda>t. t[u/i]) as) \<in> lists IT"
            by (rule lists.Cons) (rule Cons)
          thus ?case by simp
        qed
        with False show ?thesis by (auto simp add: subst_Var)
      qed
    next
      case (Lambda r)
      assume "e\<langle>i:T\<rangle> \<turnstile> Abs r : T'"
        and "\<And>e T' u i. PROP ?Q r e T' u i T"
      with uIT uT show "Abs r[u/i] \<in> IT"
        by fastsimp
    next
      case (Beta r a as)
      assume T: "e\<langle>i:T\<rangle> \<turnstile> Abs r \<degree> a \<degree>\<degree> as : T'"
      assume SI1: "\<And>e T' u i. PROP ?Q (r[a/0] \<degree>\<degree> as) e T' u i T"
      assume SI2: "\<And>e T' u i. PROP ?Q a e T' u i T"
      have "Abs (r[lift u 0/Suc i]) \<degree> a[u/i] \<degree>\<degree> map (\<lambda>t. t[u/i]) as \<in> IT"
      proof (rule IT.Beta)
        have "Abs r \<degree> a \<degree>\<degree> as -> r[a/0] \<degree>\<degree> as"
          by (rule apps_preserves_beta) (rule beta.beta)
        with T have "e\<langle>i:T\<rangle> \<turnstile> r[a/0] \<degree>\<degree> as : T'"
          by (rule subject_reduction)
        hence "(r[a/0] \<degree>\<degree> as)[u/i] \<in> IT"
          by (rule SI1)
        thus "r[lift u 0/Suc i][a[u/i]/0] \<degree>\<degree> map (\<lambda>t. t[u/i]) as \<in> IT"
          by (simp del: subst_map add: subst_subst subst_map [symmetric])
        from T obtain U where "e\<langle>i:T\<rangle> \<turnstile> Abs r \<degree> a : U"
          by (rule list_app_typeE) fast
        then obtain T'' where "e\<langle>i:T\<rangle> \<turnstile> a : T''" by cases simp_all
        thus "a[u/i] \<in> IT" by (rule SI2)
      qed
      thus "(Abs r \<degree> a \<degree>\<degree> as)[u/i] \<in> IT" by simp
    }
  qed
qed

subsection {* Well-typed terms are strongly normalizing *}

lemma type_implies_IT: "e \<turnstile> t : T \<Longrightarrow> t \<in> IT"
proof -
  assume "e \<turnstile> t : T"
  thus ?thesis
  proof induct
    case Var
    show ?case by (rule Var_IT)
  next
    case Abs
    show ?case by (rule IT.Lambda)
  next
    case (App T U e s t)
    have "(Var 0 \<degree> lift t 0)[s/0] \<in> IT"
    proof (rule subst_type_IT)
      have "lift t 0 \<in> IT" by (rule lift_IT)
      hence "[lift t 0] \<in> lists IT" by (rule lists.Cons) (rule lists.Nil)
      hence "Var 0 \<degree>\<degree> [lift t 0] \<in> IT" by (rule IT.Var)
      also have "Var 0 \<degree>\<degree> [lift t 0] = Var 0 \<degree> lift t 0" by simp
      finally show "\<dots> \<in> IT" .
      have "e\<langle>0:T \<Rightarrow> U\<rangle> \<turnstile> Var 0 : T \<Rightarrow> U"
        by (rule typing.Var) simp
      moreover have "e\<langle>0:T \<Rightarrow> U\<rangle> \<turnstile> lift t 0 : T"
        by (rule lift_type)
      ultimately show "e\<langle>0:T \<Rightarrow> U\<rangle> \<turnstile> Var 0 \<degree> lift t 0 : U"
        by (rule typing.App)
    qed
    thus ?case by simp
  qed
qed

theorem type_implies_termi: "e \<turnstile> t : T \<Longrightarrow> t \<in> termi beta"
proof -
  assume "e \<turnstile> t : T"
  hence "t \<in> IT" by (rule type_implies_IT)
  thus ?thesis by (rule IT_implies_termi)
qed

end
