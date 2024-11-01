(*  Title:      HOL/Proofs/Lambda/LambdaType.thy
    Author:     Stefan Berghofer
    Copyright   2000 TU Muenchen
*)

section \<open>Simply-typed lambda terms\<close>

theory LambdaType imports ListApplication begin


subsection \<open>Environments\<close>

definition
  shift :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"  (\<open>_\<langle>_:_\<rangle>\<close> [90, 0, 0] 91) where
  "e\<langle>i:a\<rangle> = (\<lambda>j. if j < i then e j else if j = i then a else e (j - 1))"

lemma shift_eq [simp]: "i = j \<Longrightarrow> (e\<langle>i:T\<rangle>) j = T"
  by (simp add: shift_def)

lemma shift_gt [simp]: "j < i \<Longrightarrow> (e\<langle>i:T\<rangle>) j = e j"
  by (simp add: shift_def)

lemma shift_lt [simp]: "i < j \<Longrightarrow> (e\<langle>i:T\<rangle>) j = e (j - 1)"
  by (simp add: shift_def)

lemma shift_commute [simp]: "e\<langle>i:U\<rangle>\<langle>0:T\<rangle> = e\<langle>0:T\<rangle>\<langle>Suc i:U\<rangle>"
  by (rule ext) (simp_all add: shift_def split: nat.split)


subsection \<open>Types and typing rules\<close>

datatype type =
    Atom nat
  | Fun type type    (infixr \<open>\<Rightarrow>\<close> 200)

inductive typing :: "(nat \<Rightarrow> type) \<Rightarrow> dB \<Rightarrow> type \<Rightarrow> bool"  (\<open>_ \<turnstile> _ : _\<close> [50, 50, 50] 50)
  where
    Var [intro!]: "env x = T \<Longrightarrow> env \<turnstile> Var x : T"
  | Abs [intro!]: "env\<langle>0:T\<rangle> \<turnstile> t : U \<Longrightarrow> env \<turnstile> Abs t : (T \<Rightarrow> U)"
  | App [intro!]: "env \<turnstile> s : T \<Rightarrow> U \<Longrightarrow> env \<turnstile> t : T \<Longrightarrow> env \<turnstile> (s \<degree> t) : U"

inductive_cases typing_elims [elim!]:
  "e \<turnstile> Var i : T"
  "e \<turnstile> t \<degree> u : T"
  "e \<turnstile> Abs t : T"

primrec
  typings :: "(nat \<Rightarrow> type) \<Rightarrow> dB list \<Rightarrow> type list \<Rightarrow> bool"
where
    "typings e [] Ts = (Ts = [])"
  | "typings e (t # ts) Ts =
      (case Ts of
        [] \<Rightarrow> False
      | T # Ts \<Rightarrow> e \<turnstile> t : T \<and> typings e ts Ts)"

abbreviation
  typings_rel :: "(nat \<Rightarrow> type) \<Rightarrow> dB list \<Rightarrow> type list \<Rightarrow> bool"
    (\<open>_ \<tturnstile> _ : _\<close> [50, 50, 50] 50) where
  "env \<tturnstile> ts : Ts == typings env ts Ts"

abbreviation
  funs :: "type list \<Rightarrow> type \<Rightarrow> type"  (infixr \<open>\<Rrightarrow>\<close> 200) where
  "Ts \<Rrightarrow> T == foldr Fun Ts T"


subsection \<open>Some examples\<close>

schematic_goal "e \<turnstile> Abs (Abs (Abs (Var 1 \<degree> (Var 2 \<degree> Var 1 \<degree> Var 0)))) : ?T"
  by force

schematic_goal "e \<turnstile> Abs (Abs (Abs (Var 2 \<degree> Var 0 \<degree> (Var 1 \<degree> Var 0)))) : ?T"
  by force


subsection \<open>Lists of types\<close>

lemma lists_typings:
    "e \<tturnstile> ts : Ts \<Longrightarrow> listsp (\<lambda>t. \<exists>T. e \<turnstile> t : T) ts"
proof (induct ts arbitrary: Ts)
  case Nil
  then show ?case
    by simp
next
  case c: (Cons a ts)
  show ?case
  proof (cases Ts)
    case Nil
    with c show ?thesis
      by simp
  next
    case (Cons T list)
    with c show ?thesis  by force
  qed
qed

lemma types_snoc: "e \<tturnstile> ts : Ts \<Longrightarrow> e \<turnstile> t : T \<Longrightarrow> e \<tturnstile> ts @ [t] : Ts @ [T]"
  by (induct ts arbitrary: Ts) (auto split: list.split_asm)

lemma types_snoc_eq: "e \<tturnstile> ts @ [t] : Ts @ [T] =
  (e \<tturnstile> ts : Ts \<and> e \<turnstile> t : T)"
proof (induct ts arbitrary: Ts)
  case Nil
  then show ?case
    by (auto split: list.split)
next
  case (Cons a ts)
  have "\<not> e \<tturnstile> ts @ [t] : []"
  by (cases "ts @ [t]"; simp) 
  with Cons show ?case 
    by (auto split: list.split)
qed

text \<open>Cannot use \<open>rev_exhaust\<close> from the \<open>List\<close> theory, since it is not constructive\<close>
lemma rev_exhaust2 [extraction_expand]:
  obtains (Nil) "xs = []"  |  (snoc) ys y where "xs = ys @ [y]"
proof -
  have \<section>: "xs = rev ys \<Longrightarrow> thesis" for ys
    by (cases ys) (simp_all add: local.Nil snoc)
  show thesis
    using \<section> [of "rev xs"] by simp
qed

lemma types_snocE:
  assumes \<open>e \<tturnstile> ts @ [t] : Ts\<close>
  obtains Us and U where \<open>Ts = Us @ [U]\<close> \<open>e \<tturnstile> ts : Us\<close> \<open>e \<turnstile> t : U\<close>
proof (cases Ts rule: rev_exhaust2)
  case Nil
  with assms show ?thesis
    by (cases "ts @ [t]") simp_all
next
  case (snoc Us U)
  with assms have "e \<tturnstile> ts @ [t] : Us @ [U]" by simp
  then have "e \<tturnstile> ts : Us" "e \<turnstile> t : U" by (simp_all add: types_snoc_eq)
  with snoc show ?thesis by (rule that)
qed


subsection \<open>n-ary function types\<close>

lemma list_app_typeD:
    "e \<turnstile> t \<degree>\<degree> ts : T \<Longrightarrow> \<exists>Ts. e \<turnstile> t : Ts \<Rrightarrow> T \<and> e \<tturnstile> ts : Ts"
proof (induct ts arbitrary: t T)
  case Nil
  then show ?case by auto
next
  case (Cons a b t T)
  then show ?case
    by (auto simp: split: list.split)
qed

lemma list_app_typeE:
  "e \<turnstile> t \<degree>\<degree> ts : T \<Longrightarrow> (\<And>Ts. e \<turnstile> t : Ts \<Rrightarrow> T \<Longrightarrow> e \<tturnstile> ts : Ts \<Longrightarrow> C) \<Longrightarrow> C"
  using list_app_typeD by iprover

lemma list_app_typeI:
    "e \<turnstile> t : Ts \<Rrightarrow> T \<Longrightarrow> e \<tturnstile> ts : Ts \<Longrightarrow> e \<turnstile> t \<degree>\<degree> ts : T"
  by (induct ts arbitrary: t  Ts) (auto simp add: split: list.split_asm)

text \<open>
For the specific case where the head of the term is a variable,
the following theorems allow to infer the types of the arguments
without analyzing the typing derivation. This is crucial
for program extraction.
\<close>

theorem var_app_type_eq:
  "e \<turnstile> Var i \<degree>\<degree> ts : T \<Longrightarrow> e \<turnstile> Var i \<degree>\<degree> ts : U \<Longrightarrow> T = U"
  by (induct ts arbitrary: T U rule: rev_induct) auto

lemma var_app_types: "e \<turnstile> Var i \<degree>\<degree> ts \<degree>\<degree> us : T \<Longrightarrow> e \<tturnstile> ts : Ts \<Longrightarrow>
  e \<turnstile> Var i \<degree>\<degree> ts : U \<Longrightarrow> \<exists>Us. U = Us \<Rrightarrow> T \<and> e \<tturnstile> us : Us"
proof (induct us arbitrary: ts Ts U)
  case Nil
  then show ?case
    by (simp add: var_app_type_eq)
next
  case (Cons a b ts Ts U)
  then show ?case
    apply atomize
    apply (case_tac U)
     apply (rule FalseE)
     apply simp
     apply (erule list_app_typeE)
     apply (ind_cases "e \<turnstile> t \<degree> u : T" for t u T)
     apply (rename_tac nat Ts' T')
     apply (drule_tac T="Atom nat" and U="T' \<Rightarrow> Ts' \<Rrightarrow> T" in var_app_type_eq)
      apply assumption
     apply simp
    apply (rename_tac type1 type2)
    apply (erule_tac x="ts @ [a]" in allE)
    apply (erule_tac x="Ts @ [type1]" in allE)
    apply (erule_tac x="type2" in allE)
    apply simp
    apply (erule impE)
     apply (rule types_snoc)
      apply assumption
     apply (erule list_app_typeE)
     apply (ind_cases "e \<turnstile> t \<degree> u : T" for t u T)
    using var_app_type_eq apply fastforce
    apply (erule impE)
     apply (rule typing.App)
      apply assumption
     apply (erule list_app_typeE)
     apply (ind_cases "e \<turnstile> t \<degree> u : T" for t u T)
    using var_app_type_eq apply fastforce
    apply (erule exE)
    apply (rule_tac x="type1 # Us" in exI)
    apply simp
    apply (erule list_app_typeE)
    apply (ind_cases "e \<turnstile> t \<degree> u : T" for t u T)
    using var_app_type_eq by fastforce
qed

lemma var_app_typesE: "e \<turnstile> Var i \<degree>\<degree> ts : T \<Longrightarrow>
  (\<And>Ts. e \<turnstile> Var i : Ts \<Rrightarrow> T \<Longrightarrow> e \<tturnstile> ts : Ts \<Longrightarrow> P) \<Longrightarrow> P"
  by (iprover intro: typing.Var dest: var_app_types [of _ _ "[]", simplified])

lemma abs_typeE:
  assumes "e \<turnstile> Abs t : T" "\<And>U V. e\<langle>0:U\<rangle> \<turnstile> t : V \<Longrightarrow> P"
  shows "P"
proof (cases T)
  case (Atom x1)
  with assms(1) show ?thesis
    apply-
    apply (rule FalseE)
    apply (erule typing.cases)
      apply simp_all
    done
next
  case (Fun type1 type2)
  with assms show ?thesis
    apply atomize
    apply (erule_tac x="type1" in allE)
    apply (erule_tac x="type2" in allE)
    apply (erule mp)
    apply (erule typing.cases)
      apply simp_all
    done
qed


subsection \<open>Lifting preserves well-typedness\<close>

lemma lift_type [intro!]: "e \<turnstile> t : T \<Longrightarrow> e\<langle>i:U\<rangle> \<turnstile> lift t i : T"
  by (induct arbitrary: i U set: typing) auto

lemma lift_types:
  "e \<tturnstile> ts : Ts \<Longrightarrow> e\<langle>i:U\<rangle> \<tturnstile> (map (\<lambda>t. lift t i) ts) : Ts"
  by (induct ts arbitrary: Ts) (auto split: list.split)


subsection \<open>Substitution lemmas\<close>

lemma subst_lemma:
    "e \<turnstile> t : T \<Longrightarrow> e' \<turnstile> u : U \<Longrightarrow> e = e'\<langle>i:U\<rangle> \<Longrightarrow> e' \<turnstile> t[u/i] : T"
proof (induct arbitrary: e' i U u set: typing)
  case (Var env x T)
  then show ?case
    by (force simp add: shift_def)
next
  case (Abs env T t U)
  then show ?case by force
qed auto

lemma substs_lemma:
  "e \<turnstile> u : T \<Longrightarrow> e\<langle>i:T\<rangle> \<tturnstile> ts : Ts \<Longrightarrow>
     e \<tturnstile> (map (\<lambda>t. t[u/i]) ts) : Ts"
proof (induct ts arbitrary: Ts)
  case Nil
  then show ?case
    by auto
next
  case (Cons a ts)
  with subst_lemma show ?case
    by (auto split: list.split)
qed


subsection \<open>Subject reduction\<close>

lemma subject_reduction: "e \<turnstile> t : T \<Longrightarrow> t \<rightarrow>\<^sub>\<beta> t' \<Longrightarrow> e \<turnstile> t' : T"
proof (induct arbitrary: t' set: typing)
  case (App env s T U t)
  with subst_lemma show ?case
    by auto
qed auto

theorem subject_reduction': "t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<Longrightarrow> e \<turnstile> t : T \<Longrightarrow> e \<turnstile> t' : T"
  by (induct set: rtranclp) (iprover intro: subject_reduction)+


subsection \<open>Alternative induction rule for types\<close>

lemma type_induct [induct type]:
  assumes
  "(\<And>T. (\<And>T1 T2. T = T1 \<Rightarrow> T2 \<Longrightarrow> P T1) \<Longrightarrow>
    (\<And>T1 T2. T = T1 \<Rightarrow> T2 \<Longrightarrow> P T2) \<Longrightarrow> P T)"
  shows "P T"
proof (induct T)
  case Atom
  show ?case by (rule assms) simp_all
next
  case Fun
  show ?case by (rule assms) (insert Fun, simp_all)
qed

end
