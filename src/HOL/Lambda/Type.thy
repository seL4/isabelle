(*  Title:      HOL/Lambda/Type.thy
    ID:         $Id$
    Author:     Stefan Berghofer
    Copyright   2000 TU Muenchen
*)

header {* Simply-typed lambda terms *}

theory Type = ListApplication:


subsection {* Environments *}

constdefs
  shift :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"    ("_<_:_>" [90, 0, 0] 91)
  "e<i:a> \<equiv> \<lambda>j. if j < i then e j else if j = i then a else e (j - 1)"
syntax (xsymbols)
  shift :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"    ("_\<langle>_:_\<rangle>" [90, 0, 0] 91)
syntax (HTML output)
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
syntax (xsymbols)
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


subsection {* Lists of types *}

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

lemma types_snoc: "\<And>Ts. e \<tturnstile> ts : Ts \<Longrightarrow> e \<turnstile> t : T \<Longrightarrow> e \<tturnstile> ts @ [t] : Ts @ [T]"
  apply (induct ts)
  apply simp
  apply (case_tac Ts)
  apply simp+
  done

lemma types_snoc_eq: "\<And>Ts. e \<tturnstile> ts @ [t] : Ts @ [T] =
  (e \<tturnstile> ts : Ts \<and> e \<turnstile> t : T)"
  apply (induct ts)
  apply (case_tac Ts)
  apply simp+
  apply (case_tac Ts)
  apply (case_tac "list @ [t]")
  apply simp+
  done

lemma rev_exhaust2 [case_names Nil snoc, extraction_expand]:
  "(xs = [] \<Longrightarrow> P) \<Longrightarrow> (\<And>ys y. xs = ys @ [y] \<Longrightarrow> P) \<Longrightarrow> P"
  -- {* Cannot use @{text rev_exhaust} from the @{text List}
    theory, since it is not constructive *}
  apply (subgoal_tac "\<forall>ys. xs = rev ys \<longrightarrow> P")
  apply (erule_tac x="rev xs" in allE)
  apply simp
  apply (rule allI)
  apply (rule impI)
  apply (case_tac ys)
  apply simp
  apply simp
  apply atomize
  apply (erule allE)+
  apply (erule mp, rule conjI)
  apply (rule refl)+
  done

lemma types_snocE: "e \<tturnstile> ts @ [t] : Ts \<Longrightarrow>
  (\<And>Us U. Ts = Us @ [U] \<Longrightarrow> e \<tturnstile> ts : Us \<Longrightarrow> e \<turnstile> t : U \<Longrightarrow> P) \<Longrightarrow> P"
  apply (cases Ts rule: rev_exhaust2)
  apply simp
  apply (case_tac "ts @ [t]")
  apply (simp add: types_snoc_eq)+
  apply rules
  done


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

text {*
For the specific case where the head of the term is a variable,
the following theorems allow to infer the types of the arguments
without analyzing the typing derivation. This is crucial
for program extraction.
*}

theorem var_app_type_eq:
  "\<And>T U. e \<turnstile> Var i \<degree>\<degree> ts : T \<Longrightarrow> e \<turnstile> Var i \<degree>\<degree> ts : U \<Longrightarrow> T = U"
  apply (induct ts rule: rev_induct)
  apply simp
  apply (ind_cases "e \<turnstile> Var i : T")
  apply (ind_cases "e \<turnstile> Var i : T")
  apply simp
  apply simp
  apply (ind_cases "e \<turnstile> t \<degree> u : T")
  apply (ind_cases "e \<turnstile> t \<degree> u : T")
  apply atomize
  apply (erule_tac x="Ta \<Rightarrow> T" in allE)
  apply (erule_tac x="Tb \<Rightarrow> U" in allE)
  apply (erule impE)
  apply assumption
  apply (erule impE)
  apply assumption
  apply simp
  done

lemma var_app_types: "\<And>ts Ts U. e \<turnstile> Var i \<degree>\<degree> ts \<degree>\<degree> us : T \<Longrightarrow> e \<tturnstile> ts : Ts \<Longrightarrow>
  e \<turnstile> Var i \<degree>\<degree> ts : U \<Longrightarrow> \<exists>Us. U = Us \<Rrightarrow> T \<and> e \<tturnstile> us : Us"
  apply (induct us)
  apply simp
  apply (erule var_app_type_eq)
  apply assumption
  apply simp
  apply atomize
  apply (case_tac U)
  apply (rule FalseE)
  apply simp
  apply (erule list_app_typeE)
  apply (ind_cases "e \<turnstile> t \<degree> u : T")
  apply (drule_tac T="Atom nat" and U="Ta \<Rightarrow> Tsa \<Rrightarrow> T" in var_app_type_eq)
  apply assumption
  apply simp
  apply (erule_tac x="ts @ [a]" in allE)
  apply (erule_tac x="Ts @ [type1]" in allE)
  apply (erule_tac x="type2" in allE)
  apply simp
  apply (erule impE)
  apply (rule types_snoc)
  apply assumption
  apply (erule list_app_typeE)
  apply (ind_cases "e \<turnstile> t \<degree> u : T")
  apply (drule_tac T="type1 \<Rightarrow> type2" and U="Ta \<Rightarrow> Tsa \<Rrightarrow> T" in var_app_type_eq)
  apply assumption
  apply simp
  apply (erule impE)
  apply (rule typing.App)
  apply assumption
  apply (erule list_app_typeE)
  apply (ind_cases "e \<turnstile> t \<degree> u : T")
  apply (frule_tac T="type1 \<Rightarrow> type2" and U="Ta \<Rightarrow> Tsa \<Rrightarrow> T" in var_app_type_eq)
  apply assumption
  apply simp
  apply (erule exE)
  apply (rule_tac x="type1 # Us" in exI)
  apply simp
  apply (erule list_app_typeE)
  apply (ind_cases "e \<turnstile> t \<degree> u : T")
  apply (frule_tac T="type1 \<Rightarrow> Us \<Rrightarrow> T" and U="Ta \<Rightarrow> Tsa \<Rrightarrow> T" in var_app_type_eq)
  apply assumption
  apply simp
  done

lemma var_app_typesE: "e \<turnstile> Var i \<degree>\<degree> ts : T \<Longrightarrow>
  (\<And>Ts. e \<turnstile> Var i : Ts \<Rrightarrow> T \<Longrightarrow> e \<tturnstile> ts : Ts \<Longrightarrow> P) \<Longrightarrow> P"
  apply (drule var_app_types [of _ _ "[]", simplified])
  apply (rules intro: typing.Var)+
  done

lemma abs_typeE: "e \<turnstile> Abs t : T \<Longrightarrow> (\<And>U V. e\<langle>0:U\<rangle> \<turnstile> t : V \<Longrightarrow> P) \<Longrightarrow> P"
  apply (cases T)
  apply (rule FalseE)
  apply (erule typing.elims)
  apply simp_all
  apply atomize
  apply (erule_tac x="type1" in allE)
  apply (erule_tac x="type2" in allE)
  apply (erule mp)
  apply (erule typing.elims)
  apply simp_all
  done


subsection {* Lifting preserves well-typedness *}

lemma lift_type [intro!]: "e \<turnstile> t : T \<Longrightarrow> (\<And>i U. e\<langle>i:U\<rangle> \<turnstile> lift t i : T)"
  by (induct set: typing) auto

lemma lift_types:
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

theorem subject_reduction': "t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<Longrightarrow> e \<turnstile> t : T \<Longrightarrow> e \<turnstile> t' : T"
  by (induct set: rtrancl) (rules intro: subject_reduction)+


subsection {* Alternative induction rule for types *}

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

end
