(*  Title:      HOL/Predicate.thy
    Author:     Stefan Berghofer and Lukas Bulwahn and Florian Haftmann, TU Muenchen
*)

header {* Predicates as relations and enumerations *}

theory Predicate
imports Inductive Relation
begin

notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf (infixl "\<sqinter>" 70) and
  sup (infixl "\<squnion>" 65) and
  Inf ("\<Sqinter>_" [900] 900) and
  Sup ("\<Squnion>_" [900] 900)

syntax (xsymbols)
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)


subsection {* Predicates as (complete) lattices *}

text {*
  Handy introduction and elimination rules for @{text "\<le>"}
  on unary and binary predicates
*}

lemma predicate1I:
  assumes PQ: "\<And>x. P x \<Longrightarrow> Q x"
  shows "P \<le> Q"
  apply (rule le_funI)
  apply (rule le_boolI)
  apply (rule PQ)
  apply assumption
  done

lemma predicate1D [Pure.dest?, dest?]:
  "P \<le> Q \<Longrightarrow> P x \<Longrightarrow> Q x"
  apply (erule le_funE)
  apply (erule le_boolE)
  apply assumption+
  done

lemma rev_predicate1D:
  "P x \<Longrightarrow> P \<le> Q \<Longrightarrow> Q x"
  by (rule predicate1D)

lemma predicate2I [Pure.intro!, intro!]:
  assumes PQ: "\<And>x y. P x y \<Longrightarrow> Q x y"
  shows "P \<le> Q"
  apply (rule le_funI)+
  apply (rule le_boolI)
  apply (rule PQ)
  apply assumption
  done

lemma predicate2D [Pure.dest, dest]:
  "P \<le> Q \<Longrightarrow> P x y \<Longrightarrow> Q x y"
  apply (erule le_funE)+
  apply (erule le_boolE)
  apply assumption+
  done

lemma rev_predicate2D:
  "P x y \<Longrightarrow> P \<le> Q \<Longrightarrow> Q x y"
  by (rule predicate2D)


subsubsection {* Equality *}

lemma pred_equals_eq: "((\<lambda>x. x \<in> R) = (\<lambda>x. x \<in> S)) \<longleftrightarrow> (R = S)"
  by (simp add: set_eq_iff fun_eq_iff mem_def)

lemma pred_equals_eq2 [pred_set_conv]: "((\<lambda>x y. (x, y) \<in> R) = (\<lambda>x y. (x, y) \<in> S)) \<longleftrightarrow> (R = S)"
  by (simp add: set_eq_iff fun_eq_iff mem_def)


subsubsection {* Order relation *}

lemma pred_subset_eq: "((\<lambda>x. x \<in> R) \<le> (\<lambda>x. x \<in> S)) \<longleftrightarrow> (R \<subseteq> S)"
  by (simp add: subset_iff le_fun_def mem_def)

lemma pred_subset_eq2 [pred_set_conv]: "((\<lambda>x y. (x, y) \<in> R) \<le> (\<lambda>x y. (x, y) \<in> S)) \<longleftrightarrow> (R \<subseteq> S)"
  by (simp add: subset_iff le_fun_def mem_def)


subsubsection {* Top and bottom elements *}

lemma bot1E [no_atp, elim!]: "\<bottom> x \<Longrightarrow> P"
  by (simp add: bot_fun_def)

lemma bot2E [elim!]: "\<bottom> x y \<Longrightarrow> P"
  by (simp add: bot_fun_def)

lemma bot_empty_eq: "\<bottom> = (\<lambda>x. x \<in> {})"
  by (auto simp add: fun_eq_iff)

lemma bot_empty_eq2: "\<bottom> = (\<lambda>x y. (x, y) \<in> {})"
  by (auto simp add: fun_eq_iff)

lemma top1I [intro!]: "\<top> x"
  by (simp add: top_fun_def)

lemma top2I [intro!]: "\<top> x y"
  by (simp add: top_fun_def)


subsubsection {* Binary intersection *}

lemma inf1I [intro!]: "A x \<Longrightarrow> B x \<Longrightarrow> (A \<sqinter> B) x"
  by (simp add: inf_fun_def)

lemma inf2I [intro!]: "A x y \<Longrightarrow> B x y \<Longrightarrow> (A \<sqinter> B) x y"
  by (simp add: inf_fun_def)

lemma inf1E [elim!]: "(A \<sqinter> B) x \<Longrightarrow> (A x \<Longrightarrow> B x \<Longrightarrow> P) \<Longrightarrow> P"
  by (simp add: inf_fun_def)

lemma inf2E [elim!]: "(A \<sqinter> B) x y \<Longrightarrow> (A x y \<Longrightarrow> B x y \<Longrightarrow> P) \<Longrightarrow> P"
  by (simp add: inf_fun_def)

lemma inf1D1: "(A \<sqinter> B) x \<Longrightarrow> A x"
  by (simp add: inf_fun_def)

lemma inf2D1: "(A \<sqinter> B) x y \<Longrightarrow> A x y"
  by (simp add: inf_fun_def)

lemma inf1D2: "(A \<sqinter> B) x \<Longrightarrow> B x"
  by (simp add: inf_fun_def)

lemma inf2D2: "(A \<sqinter> B) x y \<Longrightarrow> B x y"
  by (simp add: inf_fun_def)

lemma inf_Int_eq: "(\<lambda>x. x \<in> R) \<sqinter> (\<lambda>x. x \<in> S) = (\<lambda>x. x \<in> R \<inter> S)"
  by (simp add: inf_fun_def mem_def)

lemma inf_Int_eq2 [pred_set_conv]: "(\<lambda>x y. (x, y) \<in> R) \<sqinter> (\<lambda>x y. (x, y) \<in> S) = (\<lambda>x y. (x, y) \<in> R \<inter> S)"
  by (simp add: inf_fun_def mem_def)


subsubsection {* Binary union *}

lemma sup1I1 [intro?]: "A x \<Longrightarrow> (A \<squnion> B) x"
  by (simp add: sup_fun_def)

lemma sup2I1 [intro?]: "A x y \<Longrightarrow> (A \<squnion> B) x y"
  by (simp add: sup_fun_def)

lemma sup1I2 [intro?]: "B x \<Longrightarrow> (A \<squnion> B) x"
  by (simp add: sup_fun_def)

lemma sup2I2 [intro?]: "B x y \<Longrightarrow> (A \<squnion> B) x y"
  by (simp add: sup_fun_def)

lemma sup1E [elim!]: "(A \<squnion> B) x \<Longrightarrow> (A x \<Longrightarrow> P) \<Longrightarrow> (B x \<Longrightarrow> P) \<Longrightarrow> P"
  by (simp add: sup_fun_def) iprover

lemma sup2E [elim!]: "(A \<squnion> B) x y \<Longrightarrow> (A x y \<Longrightarrow> P) \<Longrightarrow> (B x y \<Longrightarrow> P) \<Longrightarrow> P"
  by (simp add: sup_fun_def) iprover

text {*
  \medskip Classical introduction rule: no commitment to @{text A} vs
  @{text B}.
*}

lemma sup1CI [intro!]: "(\<not> B x \<Longrightarrow> A x) \<Longrightarrow> (A \<squnion> B) x"
  by (auto simp add: sup_fun_def)

lemma sup2CI [intro!]: "(\<not> B x y \<Longrightarrow> A x y) \<Longrightarrow> (A \<squnion> B) x y"
  by (auto simp add: sup_fun_def)

lemma sup_Un_eq: "(\<lambda>x. x \<in> R) \<squnion> (\<lambda>x. x \<in> S) = (\<lambda>x. x \<in> R \<union> S)"
  by (simp add: sup_fun_def mem_def)

lemma sup_Un_eq2 [pred_set_conv]: "(\<lambda>x y. (x, y) \<in> R) \<squnion> (\<lambda>x y. (x, y) \<in> S) = (\<lambda>x y. (x, y) \<in> R \<union> S)"
  by (simp add: sup_fun_def mem_def)


subsubsection {* Intersections of families *}

lemma INF1_iff: "(\<Sqinter>x\<in>A. B x) b = (\<forall>x\<in>A. B x b)"
  by (simp add: INF_apply)

lemma INF2_iff: "(\<Sqinter>x\<in>A. B x) b c = (\<forall>x\<in>A. B x b c)"
  by (simp add: INF_apply)

lemma INF1_I [intro!]: "(\<And>x. x \<in> A \<Longrightarrow> B x b) \<Longrightarrow> (\<Sqinter>x\<in>A. B x) b"
  by (auto simp add: INF_apply)

lemma INF2_I [intro!]: "(\<And>x. x \<in> A \<Longrightarrow> B x b c) \<Longrightarrow> (\<Sqinter>x\<in>A. B x) b c"
  by (auto simp add: INF_apply)

lemma INF1_D [elim]: "(\<Sqinter>x\<in>A. B x) b \<Longrightarrow> a \<in> A \<Longrightarrow> B a b"
  by (auto simp add: INF_apply)

lemma INF2_D [elim]: "(\<Sqinter>x\<in>A. B x) b c \<Longrightarrow> a \<in> A \<Longrightarrow> B a b c"
  by (auto simp add: INF_apply)

lemma INF1_E [elim]: "(\<Sqinter>x\<in>A. B x) b \<Longrightarrow> (B a b \<Longrightarrow> R) \<Longrightarrow> (a \<notin> A \<Longrightarrow> R) \<Longrightarrow> R"
  by (auto simp add: INF_apply)

lemma INF2_E [elim]: "(\<Sqinter>x\<in>A. B x) b c \<Longrightarrow> (B a b c \<Longrightarrow> R) \<Longrightarrow> (a \<notin> A \<Longrightarrow> R) \<Longrightarrow> R"
  by (auto simp add: INF_apply)

lemma INF_INT_eq: "(\<Sqinter>i. (\<lambda>x. x \<in> r i)) = (\<lambda>x. x \<in> (\<Sqinter>i. r i))"
  by (simp add: INF_apply fun_eq_iff)

lemma INF_INT_eq2: "(\<Sqinter>i. (\<lambda>x y. (x, y) \<in> r i)) = (\<lambda>x y. (x, y) \<in> (\<Sqinter>i. r i))"
  by (simp add: INF_apply fun_eq_iff)


subsubsection {* Unions of families *}

lemma SUP1_iff: "(\<Squnion>x\<in>A. B x) b = (\<exists>x\<in>A. B x b)"
  by (simp add: SUP_apply)

lemma SUP2_iff: "(\<Squnion>x\<in>A. B x) b c = (\<exists>x\<in>A. B x b c)"
  by (simp add: SUP_apply)

lemma SUP1_I [intro]: "a \<in> A \<Longrightarrow> B a b \<Longrightarrow> (\<Squnion>x\<in>A. B x) b"
  by (auto simp add: SUP_apply)

lemma SUP2_I [intro]: "a \<in> A \<Longrightarrow> B a b c \<Longrightarrow> (\<Squnion>x\<in>A. B x) b c"
  by (auto simp add: SUP_apply)

lemma SUP1_E [elim!]: "(\<Squnion>x\<in>A. B x) b \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> B x b \<Longrightarrow> R) \<Longrightarrow> R"
  by (auto simp add: SUP_apply)

lemma SUP2_E [elim!]: "(\<Squnion>x\<in>A. B x) b c \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> B x b c \<Longrightarrow> R) \<Longrightarrow> R"
  by (auto simp add: SUP_apply)

lemma SUP_UN_eq: "(\<Squnion>i. (\<lambda>x. x \<in> r i)) = (\<lambda>x. x \<in> (\<Union>i. r i))"
  by (simp add: SUP_apply fun_eq_iff)

lemma SUP_UN_eq2: "(\<Squnion>i. (\<lambda>x y. (x, y) \<in> r i)) = (\<lambda>x y. (x, y) \<in> (\<Union>i. r i))"
  by (simp add: SUP_apply fun_eq_iff)


subsection {* Predicates as relations *}

subsubsection {* Composition  *}

inductive pred_comp  :: "['a \<Rightarrow> 'b \<Rightarrow> bool, 'b \<Rightarrow> 'c \<Rightarrow> bool] \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> bool" (infixr "OO" 75)
  for r :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and s :: "'b \<Rightarrow> 'c \<Rightarrow> bool" where
  pred_compI [intro]: "r a b \<Longrightarrow> s b c \<Longrightarrow> (r OO s) a c"

inductive_cases pred_compE [elim!]: "(r OO s) a c"

lemma pred_comp_rel_comp_eq [pred_set_conv]:
  "((\<lambda>x y. (x, y) \<in> r) OO (\<lambda>x y. (x, y) \<in> s)) = (\<lambda>x y. (x, y) \<in> r O s)"
  by (auto simp add: fun_eq_iff)


subsubsection {* Converse *}

inductive conversep :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool" ("(_^--1)" [1000] 1000)
  for r :: "'a \<Rightarrow> 'b \<Rightarrow> bool" where
  conversepI: "r a b \<Longrightarrow> r^--1 b a"

notation (xsymbols)
  conversep  ("(_\<inverse>\<inverse>)" [1000] 1000)

lemma conversepD:
  assumes ab: "r^--1 a b"
  shows "r b a" using ab
  by cases simp

lemma conversep_iff [iff]: "r^--1 a b = r b a"
  by (iprover intro: conversepI dest: conversepD)

lemma conversep_converse_eq [pred_set_conv]:
  "(\<lambda>x y. (x, y) \<in> r)^--1 = (\<lambda>x y. (x, y) \<in> r^-1)"
  by (auto simp add: fun_eq_iff)

lemma conversep_conversep [simp]: "(r^--1)^--1 = r"
  by (iprover intro: order_antisym conversepI dest: conversepD)

lemma converse_pred_comp: "(r OO s)^--1 = s^--1 OO r^--1"
  by (iprover intro: order_antisym conversepI pred_compI
    elim: pred_compE dest: conversepD)

lemma converse_meet: "(r \<sqinter> s)^--1 = r^--1 \<sqinter> s^--1"
  by (simp add: inf_fun_def) (iprover intro: conversepI ext dest: conversepD)

lemma converse_join: "(r \<squnion> s)^--1 = r^--1 \<squnion> s^--1"
  by (simp add: sup_fun_def) (iprover intro: conversepI ext dest: conversepD)

lemma conversep_noteq [simp]: "(op \<noteq>)^--1 = op \<noteq>"
  by (auto simp add: fun_eq_iff)

lemma conversep_eq [simp]: "(op =)^--1 = op ="
  by (auto simp add: fun_eq_iff)


subsubsection {* Domain *}

inductive DomainP :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  for r :: "'a \<Rightarrow> 'b \<Rightarrow> bool" where
  DomainPI [intro]: "r a b \<Longrightarrow> DomainP r a"

inductive_cases DomainPE [elim!]: "DomainP r a"

lemma DomainP_Domain_eq [pred_set_conv]: "DomainP (\<lambda>x y. (x, y) \<in> r) = (\<lambda>x. x \<in> Domain r)"
  by (blast intro!: Orderings.order_antisym predicate1I)


subsubsection {* Range *}

inductive RangeP :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> bool"
  for r :: "'a \<Rightarrow> 'b \<Rightarrow> bool" where
  RangePI [intro]: "r a b \<Longrightarrow> RangeP r b"

inductive_cases RangePE [elim!]: "RangeP r b"

lemma RangeP_Range_eq [pred_set_conv]: "RangeP (\<lambda>x y. (x, y) \<in> r) = (\<lambda>x. x \<in> Range r)"
  by (blast intro!: Orderings.order_antisym predicate1I)


subsubsection {* Inverse image *}

definition inv_imagep :: "('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "inv_imagep r f = (\<lambda>x y. r (f x) (f y))"

lemma [pred_set_conv]: "inv_imagep (\<lambda>x y. (x, y) \<in> r) f = (\<lambda>x y. (x, y) \<in> inv_image r f)"
  by (simp add: inv_image_def inv_imagep_def)

lemma in_inv_imagep [simp]: "inv_imagep r f x y = r (f x) (f y)"
  by (simp add: inv_imagep_def)


subsubsection {* Powerset *}

definition Powp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "Powp A = (\<lambda>B. \<forall>x \<in> B. A x)"

lemma Powp_Pow_eq [pred_set_conv]: "Powp (\<lambda>x. x \<in> A) = (\<lambda>x. x \<in> Pow A)"
  by (auto simp add: Powp_def fun_eq_iff)

lemmas Powp_mono [mono] = Pow_mono [to_pred pred_subset_eq]


subsubsection {* Properties of relations *}

abbreviation antisymP :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "antisymP r \<equiv> antisym {(x, y). r x y}"

abbreviation transP :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "transP r \<equiv> trans {(x, y). r x y}"

abbreviation single_valuedP :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool" where
  "single_valuedP r \<equiv> single_valued {(x, y). r x y}"

(*FIXME inconsistencies: abbreviations vs. definitions, suffix `P` vs. suffix `p`*)

definition reflp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "reflp r \<longleftrightarrow> refl {(x, y). r x y}"

definition symp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "symp r \<longleftrightarrow> sym {(x, y). r x y}"

definition transp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "transp r \<longleftrightarrow> trans {(x, y). r x y}"

lemma reflpI:
  "(\<And>x. r x x) \<Longrightarrow> reflp r"
  by (auto intro: refl_onI simp add: reflp_def)

lemma reflpE:
  assumes "reflp r"
  obtains "r x x"
  using assms by (auto dest: refl_onD simp add: reflp_def)

lemma sympI:
  "(\<And>x y. r x y \<Longrightarrow> r y x) \<Longrightarrow> symp r"
  by (auto intro: symI simp add: symp_def)

lemma sympE:
  assumes "symp r" and "r x y"
  obtains "r y x"
  using assms by (auto dest: symD simp add: symp_def)

lemma transpI:
  "(\<And>x y z. r x y \<Longrightarrow> r y z \<Longrightarrow> r x z) \<Longrightarrow> transp r"
  by (auto intro: transI simp add: transp_def)
  
lemma transpE:
  assumes "transp r" and "r x y" and "r y z"
  obtains "r x z"
  using assms by (auto dest: transD simp add: transp_def)


subsection {* Predicates as enumerations *}

subsubsection {* The type of predicate enumerations (a monad) *}

datatype 'a pred = Pred "'a \<Rightarrow> bool"

primrec eval :: "'a pred \<Rightarrow> 'a \<Rightarrow> bool" where
  eval_pred: "eval (Pred f) = f"

lemma Pred_eval [simp]:
  "Pred (eval x) = x"
  by (cases x) simp

lemma pred_eqI:
  "(\<And>w. eval P w \<longleftrightarrow> eval Q w) \<Longrightarrow> P = Q"
  by (cases P, cases Q) (auto simp add: fun_eq_iff)

instantiation pred :: (type) complete_lattice
begin

definition
  "P \<le> Q \<longleftrightarrow> eval P \<le> eval Q"

definition
  "P < Q \<longleftrightarrow> eval P < eval Q"

definition
  "\<bottom> = Pred \<bottom>"

lemma eval_bot [simp]:
  "eval \<bottom>  = \<bottom>"
  by (simp add: bot_pred_def)

definition
  "\<top> = Pred \<top>"

lemma eval_top [simp]:
  "eval \<top>  = \<top>"
  by (simp add: top_pred_def)

definition
  "P \<sqinter> Q = Pred (eval P \<sqinter> eval Q)"

lemma eval_inf [simp]:
  "eval (P \<sqinter> Q) = eval P \<sqinter> eval Q"
  by (simp add: inf_pred_def)

definition
  "P \<squnion> Q = Pred (eval P \<squnion> eval Q)"

lemma eval_sup [simp]:
  "eval (P \<squnion> Q) = eval P \<squnion> eval Q"
  by (simp add: sup_pred_def)

definition
  "\<Sqinter>A = Pred (INFI A eval)"

lemma eval_Inf [simp]:
  "eval (\<Sqinter>A) = INFI A eval"
  by (simp add: Inf_pred_def)

definition
  "\<Squnion>A = Pred (SUPR A eval)"

lemma eval_Sup [simp]:
  "eval (\<Squnion>A) = SUPR A eval"
  by (simp add: Sup_pred_def)

instance proof
qed (auto intro!: pred_eqI simp add: less_eq_pred_def less_pred_def le_fun_def less_fun_def)

end

lemma eval_INFI [simp]:
  "eval (INFI A f) = INFI A (eval \<circ> f)"
  by (simp only: INF_def eval_Inf image_compose)

lemma eval_SUPR [simp]:
  "eval (SUPR A f) = SUPR A (eval \<circ> f)"
  by (simp only: SUP_def eval_Sup image_compose)

instantiation pred :: (type) complete_boolean_algebra
begin

definition
  "- P = Pred (- eval P)"

lemma eval_compl [simp]:
  "eval (- P) = - eval P"
  by (simp add: uminus_pred_def)

definition
  "P - Q = Pred (eval P - eval Q)"

lemma eval_minus [simp]:
  "eval (P - Q) = eval P - eval Q"
  by (simp add: minus_pred_def)

instance proof
qed (auto intro!: pred_eqI simp add: uminus_apply minus_apply INF_apply SUP_apply)

end

definition single :: "'a \<Rightarrow> 'a pred" where
  "single x = Pred ((op =) x)"

lemma eval_single [simp]:
  "eval (single x) = (op =) x"
  by (simp add: single_def)

definition bind :: "'a pred \<Rightarrow> ('a \<Rightarrow> 'b pred) \<Rightarrow> 'b pred" (infixl "\<guillemotright>=" 70) where
  "P \<guillemotright>= f = (SUPR {x. eval P x} f)"

lemma eval_bind [simp]:
  "eval (P \<guillemotright>= f) = eval (SUPR {x. eval P x} f)"
  by (simp add: bind_def)

lemma bind_bind:
  "(P \<guillemotright>= Q) \<guillemotright>= R = P \<guillemotright>= (\<lambda>x. Q x \<guillemotright>= R)"
  by (rule pred_eqI) (auto simp add: SUP_apply)

lemma bind_single:
  "P \<guillemotright>= single = P"
  by (rule pred_eqI) auto

lemma single_bind:
  "single x \<guillemotright>= P = P x"
  by (rule pred_eqI) auto

lemma bottom_bind:
  "\<bottom> \<guillemotright>= P = \<bottom>"
  by (rule pred_eqI) auto

lemma sup_bind:
  "(P \<squnion> Q) \<guillemotright>= R = P \<guillemotright>= R \<squnion> Q \<guillemotright>= R"
  by (rule pred_eqI) auto

lemma Sup_bind:
  "(\<Squnion>A \<guillemotright>= f) = \<Squnion>((\<lambda>x. x \<guillemotright>= f) ` A)"
  by (rule pred_eqI) (auto simp add: SUP_apply)

lemma pred_iffI:
  assumes "\<And>x. eval A x \<Longrightarrow> eval B x"
  and "\<And>x. eval B x \<Longrightarrow> eval A x"
  shows "A = B"
  using assms by (auto intro: pred_eqI)
  
lemma singleI: "eval (single x) x"
  by simp

lemma singleI_unit: "eval (single ()) x"
  by simp

lemma singleE: "eval (single x) y \<Longrightarrow> (y = x \<Longrightarrow> P) \<Longrightarrow> P"
  by simp

lemma singleE': "eval (single x) y \<Longrightarrow> (x = y \<Longrightarrow> P) \<Longrightarrow> P"
  by simp

lemma bindI: "eval P x \<Longrightarrow> eval (Q x) y \<Longrightarrow> eval (P \<guillemotright>= Q) y"
  by auto

lemma bindE: "eval (R \<guillemotright>= Q) y \<Longrightarrow> (\<And>x. eval R x \<Longrightarrow> eval (Q x) y \<Longrightarrow> P) \<Longrightarrow> P"
  by auto

lemma botE: "eval \<bottom> x \<Longrightarrow> P"
  by auto

lemma supI1: "eval A x \<Longrightarrow> eval (A \<squnion> B) x"
  by auto

lemma supI2: "eval B x \<Longrightarrow> eval (A \<squnion> B) x" 
  by auto

lemma supE: "eval (A \<squnion> B) x \<Longrightarrow> (eval A x \<Longrightarrow> P) \<Longrightarrow> (eval B x \<Longrightarrow> P) \<Longrightarrow> P"
  by auto

lemma single_not_bot [simp]:
  "single x \<noteq> \<bottom>"
  by (auto simp add: single_def bot_pred_def fun_eq_iff)

lemma not_bot:
  assumes "A \<noteq> \<bottom>"
  obtains x where "eval A x"
  using assms by (cases A) (auto simp add: bot_pred_def, simp add: mem_def)
  

subsubsection {* Emptiness check and definite choice *}

definition is_empty :: "'a pred \<Rightarrow> bool" where
  "is_empty A \<longleftrightarrow> A = \<bottom>"

lemma is_empty_bot:
  "is_empty \<bottom>"
  by (simp add: is_empty_def)

lemma not_is_empty_single:
  "\<not> is_empty (single x)"
  by (auto simp add: is_empty_def single_def bot_pred_def fun_eq_iff)

lemma is_empty_sup:
  "is_empty (A \<squnion> B) \<longleftrightarrow> is_empty A \<and> is_empty B"
  by (auto simp add: is_empty_def)

definition singleton :: "(unit \<Rightarrow> 'a) \<Rightarrow> 'a pred \<Rightarrow> 'a" where
  "singleton dfault A = (if \<exists>!x. eval A x then THE x. eval A x else dfault ())"

lemma singleton_eqI:
  "\<exists>!x. eval A x \<Longrightarrow> eval A x \<Longrightarrow> singleton dfault A = x"
  by (auto simp add: singleton_def)

lemma eval_singletonI:
  "\<exists>!x. eval A x \<Longrightarrow> eval A (singleton dfault A)"
proof -
  assume assm: "\<exists>!x. eval A x"
  then obtain x where "eval A x" ..
  moreover with assm have "singleton dfault A = x" by (rule singleton_eqI)
  ultimately show ?thesis by simp 
qed

lemma single_singleton:
  "\<exists>!x. eval A x \<Longrightarrow> single (singleton dfault A) = A"
proof -
  assume assm: "\<exists>!x. eval A x"
  then have "eval A (singleton dfault A)"
    by (rule eval_singletonI)
  moreover from assm have "\<And>x. eval A x \<Longrightarrow> singleton dfault A = x"
    by (rule singleton_eqI)
  ultimately have "eval (single (singleton dfault A)) = eval A"
    by (simp (no_asm_use) add: single_def fun_eq_iff) blast
  then have "\<And>x. eval (single (singleton dfault A)) x = eval A x"
    by simp
  then show ?thesis by (rule pred_eqI)
qed

lemma singleton_undefinedI:
  "\<not> (\<exists>!x. eval A x) \<Longrightarrow> singleton dfault A = dfault ()"
  by (simp add: singleton_def)

lemma singleton_bot:
  "singleton dfault \<bottom> = dfault ()"
  by (auto simp add: bot_pred_def intro: singleton_undefinedI)

lemma singleton_single:
  "singleton dfault (single x) = x"
  by (auto simp add: intro: singleton_eqI singleI elim: singleE)

lemma singleton_sup_single_single:
  "singleton dfault (single x \<squnion> single y) = (if x = y then x else dfault ())"
proof (cases "x = y")
  case True then show ?thesis by (simp add: singleton_single)
next
  case False
  have "eval (single x \<squnion> single y) x"
    and "eval (single x \<squnion> single y) y"
  by (auto intro: supI1 supI2 singleI)
  with False have "\<not> (\<exists>!z. eval (single x \<squnion> single y) z)"
    by blast
  then have "singleton dfault (single x \<squnion> single y) = dfault ()"
    by (rule singleton_undefinedI)
  with False show ?thesis by simp
qed

lemma singleton_sup_aux:
  "singleton dfault (A \<squnion> B) = (if A = \<bottom> then singleton dfault B
    else if B = \<bottom> then singleton dfault A
    else singleton dfault
      (single (singleton dfault A) \<squnion> single (singleton dfault B)))"
proof (cases "(\<exists>!x. eval A x) \<and> (\<exists>!y. eval B y)")
  case True then show ?thesis by (simp add: single_singleton)
next
  case False
  from False have A_or_B:
    "singleton dfault A = dfault () \<or> singleton dfault B = dfault ()"
    by (auto intro!: singleton_undefinedI)
  then have rhs: "singleton dfault
    (single (singleton dfault A) \<squnion> single (singleton dfault B)) = dfault ()"
    by (auto simp add: singleton_sup_single_single singleton_single)
  from False have not_unique:
    "\<not> (\<exists>!x. eval A x) \<or> \<not> (\<exists>!y. eval B y)" by simp
  show ?thesis proof (cases "A \<noteq> \<bottom> \<and> B \<noteq> \<bottom>")
    case True
    then obtain a b where a: "eval A a" and b: "eval B b"
      by (blast elim: not_bot)
    with True not_unique have "\<not> (\<exists>!x. eval (A \<squnion> B) x)"
      by (auto simp add: sup_pred_def bot_pred_def)
    then have "singleton dfault (A \<squnion> B) = dfault ()" by (rule singleton_undefinedI)
    with True rhs show ?thesis by simp
  next
    case False then show ?thesis by auto
  qed
qed

lemma singleton_sup:
  "singleton dfault (A \<squnion> B) = (if A = \<bottom> then singleton dfault B
    else if B = \<bottom> then singleton dfault A
    else if singleton dfault A = singleton dfault B then singleton dfault A else dfault ())"
using singleton_sup_aux [of dfault A B] by (simp only: singleton_sup_single_single)


subsubsection {* Derived operations *}

definition if_pred :: "bool \<Rightarrow> unit pred" where
  if_pred_eq: "if_pred b = (if b then single () else \<bottom>)"

definition holds :: "unit pred \<Rightarrow> bool" where
  holds_eq: "holds P = eval P ()"

definition not_pred :: "unit pred \<Rightarrow> unit pred" where
  not_pred_eq: "not_pred P = (if eval P () then \<bottom> else single ())"

lemma if_predI: "P \<Longrightarrow> eval (if_pred P) ()"
  unfolding if_pred_eq by (auto intro: singleI)

lemma if_predE: "eval (if_pred b) x \<Longrightarrow> (b \<Longrightarrow> x = () \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding if_pred_eq by (cases b) (auto elim: botE)

lemma not_predI: "\<not> P \<Longrightarrow> eval (not_pred (Pred (\<lambda>u. P))) ()"
  unfolding not_pred_eq eval_pred by (auto intro: singleI)

lemma not_predI': "\<not> eval P () \<Longrightarrow> eval (not_pred P) ()"
  unfolding not_pred_eq by (auto intro: singleI)

lemma not_predE: "eval (not_pred (Pred (\<lambda>u. P))) x \<Longrightarrow> (\<not> P \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  unfolding not_pred_eq
  by (auto split: split_if_asm elim: botE)

lemma not_predE': "eval (not_pred P) x \<Longrightarrow> (\<not> eval P x \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  unfolding not_pred_eq
  by (auto split: split_if_asm elim: botE)
lemma "f () = False \<or> f () = True"
by simp

lemma closure_of_bool_cases [no_atp]:
  fixes f :: "unit \<Rightarrow> bool"
  assumes "f = (\<lambda>u. False) \<Longrightarrow> P f"
  assumes "f = (\<lambda>u. True) \<Longrightarrow> P f"
  shows "P f"
proof -
  have "f = (\<lambda>u. False) \<or> f = (\<lambda>u. True)"
    apply (cases "f ()")
    apply (rule disjI2)
    apply (rule ext)
    apply (simp add: unit_eq)
    apply (rule disjI1)
    apply (rule ext)
    apply (simp add: unit_eq)
    done
  from this assms show ?thesis by blast
qed

lemma unit_pred_cases:
  assumes "P \<bottom>"
  assumes "P (single ())"
  shows "P Q"
using assms unfolding bot_pred_def bot_fun_def bot_bool_def empty_def single_def proof (cases Q)
  fix f
  assume "P (Pred (\<lambda>u. False))" "P (Pred (\<lambda>u. () = u))"
  then have "P (Pred f)" 
    by (cases _ f rule: closure_of_bool_cases) simp_all
  moreover assume "Q = Pred f"
  ultimately show "P Q" by simp
qed
  
lemma holds_if_pred:
  "holds (if_pred b) = b"
unfolding if_pred_eq holds_eq
by (cases b) (auto intro: singleI elim: botE)

lemma if_pred_holds:
  "if_pred (holds P) = P"
unfolding if_pred_eq holds_eq
by (rule unit_pred_cases) (auto intro: singleI elim: botE)

lemma is_empty_holds:
  "is_empty P \<longleftrightarrow> \<not> holds P"
unfolding is_empty_def holds_eq
by (rule unit_pred_cases) (auto elim: botE intro: singleI)

definition map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a pred \<Rightarrow> 'b pred" where
  "map f P = P \<guillemotright>= (single o f)"

lemma eval_map [simp]:
  "eval (map f P) = (\<Squnion>x\<in>{x. eval P x}. (\<lambda>y. f x = y))"
  by (auto simp add: map_def comp_def)

enriched_type map: map
  by (rule ext, rule pred_eqI, auto)+


subsubsection {* Implementation *}

datatype 'a seq = Empty | Insert "'a" "'a pred" | Join "'a pred" "'a seq"

primrec pred_of_seq :: "'a seq \<Rightarrow> 'a pred" where
  "pred_of_seq Empty = \<bottom>"
| "pred_of_seq (Insert x P) = single x \<squnion> P"
| "pred_of_seq (Join P xq) = P \<squnion> pred_of_seq xq"

definition Seq :: "(unit \<Rightarrow> 'a seq) \<Rightarrow> 'a pred" where
  "Seq f = pred_of_seq (f ())"

code_datatype Seq

primrec member :: "'a seq \<Rightarrow> 'a \<Rightarrow> bool"  where
  "member Empty x \<longleftrightarrow> False"
| "member (Insert y P) x \<longleftrightarrow> x = y \<or> eval P x"
| "member (Join P xq) x \<longleftrightarrow> eval P x \<or> member xq x"

lemma eval_member:
  "member xq = eval (pred_of_seq xq)"
proof (induct xq)
  case Empty show ?case
  by (auto simp add: fun_eq_iff elim: botE)
next
  case Insert show ?case
  by (auto simp add: fun_eq_iff elim: supE singleE intro: supI1 supI2 singleI)
next
  case Join then show ?case
  by (auto simp add: fun_eq_iff elim: supE intro: supI1 supI2)
qed

lemma eval_code [code]: "eval (Seq f) = member (f ())"
  unfolding Seq_def by (rule sym, rule eval_member)

lemma single_code [code]:
  "single x = Seq (\<lambda>u. Insert x \<bottom>)"
  unfolding Seq_def by simp

primrec "apply" :: "('a \<Rightarrow> 'b pred) \<Rightarrow> 'a seq \<Rightarrow> 'b seq" where
  "apply f Empty = Empty"
| "apply f (Insert x P) = Join (f x) (Join (P \<guillemotright>= f) Empty)"
| "apply f (Join P xq) = Join (P \<guillemotright>= f) (apply f xq)"

lemma apply_bind:
  "pred_of_seq (apply f xq) = pred_of_seq xq \<guillemotright>= f"
proof (induct xq)
  case Empty show ?case
    by (simp add: bottom_bind)
next
  case Insert show ?case
    by (simp add: single_bind sup_bind)
next
  case Join then show ?case
    by (simp add: sup_bind)
qed
  
lemma bind_code [code]:
  "Seq g \<guillemotright>= f = Seq (\<lambda>u. apply f (g ()))"
  unfolding Seq_def by (rule sym, rule apply_bind)

lemma bot_set_code [code]:
  "\<bottom> = Seq (\<lambda>u. Empty)"
  unfolding Seq_def by simp

primrec adjunct :: "'a pred \<Rightarrow> 'a seq \<Rightarrow> 'a seq" where
  "adjunct P Empty = Join P Empty"
| "adjunct P (Insert x Q) = Insert x (Q \<squnion> P)"
| "adjunct P (Join Q xq) = Join Q (adjunct P xq)"

lemma adjunct_sup:
  "pred_of_seq (adjunct P xq) = P \<squnion> pred_of_seq xq"
  by (induct xq) (simp_all add: sup_assoc sup_commute sup_left_commute)

lemma sup_code [code]:
  "Seq f \<squnion> Seq g = Seq (\<lambda>u. case f ()
    of Empty \<Rightarrow> g ()
     | Insert x P \<Rightarrow> Insert x (P \<squnion> Seq g)
     | Join P xq \<Rightarrow> adjunct (Seq g) (Join P xq))"
proof (cases "f ()")
  case Empty
  thus ?thesis
    unfolding Seq_def by (simp add: sup_commute [of "\<bottom>"])
next
  case Insert
  thus ?thesis
    unfolding Seq_def by (simp add: sup_assoc)
next
  case Join
  thus ?thesis
    unfolding Seq_def
    by (simp add: adjunct_sup sup_assoc sup_commute sup_left_commute)
qed

primrec contained :: "'a seq \<Rightarrow> 'a pred \<Rightarrow> bool" where
  "contained Empty Q \<longleftrightarrow> True"
| "contained (Insert x P) Q \<longleftrightarrow> eval Q x \<and> P \<le> Q"
| "contained (Join P xq) Q \<longleftrightarrow> P \<le> Q \<and> contained xq Q"

lemma single_less_eq_eval:
  "single x \<le> P \<longleftrightarrow> eval P x"
  by (auto simp add: less_eq_pred_def le_fun_def)

lemma contained_less_eq:
  "contained xq Q \<longleftrightarrow> pred_of_seq xq \<le> Q"
  by (induct xq) (simp_all add: single_less_eq_eval)

lemma less_eq_pred_code [code]:
  "Seq f \<le> Q = (case f ()
   of Empty \<Rightarrow> True
    | Insert x P \<Rightarrow> eval Q x \<and> P \<le> Q
    | Join P xq \<Rightarrow> P \<le> Q \<and> contained xq Q)"
  by (cases "f ()")
    (simp_all add: Seq_def single_less_eq_eval contained_less_eq)

lemma eq_pred_code [code]:
  fixes P Q :: "'a pred"
  shows "HOL.equal P Q \<longleftrightarrow> P \<le> Q \<and> Q \<le> P"
  by (auto simp add: equal)

lemma [code nbe]:
  "HOL.equal (x :: 'a pred) x \<longleftrightarrow> True"
  by (fact equal_refl)

lemma [code]:
  "pred_case f P = f (eval P)"
  by (cases P) simp

lemma [code]:
  "pred_rec f P = f (eval P)"
  by (cases P) simp

inductive eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where "eq x x"

lemma eq_is_eq: "eq x y \<equiv> (x = y)"
  by (rule eq_reflection) (auto intro: eq.intros elim: eq.cases)

primrec null :: "'a seq \<Rightarrow> bool" where
  "null Empty \<longleftrightarrow> True"
| "null (Insert x P) \<longleftrightarrow> False"
| "null (Join P xq) \<longleftrightarrow> is_empty P \<and> null xq"

lemma null_is_empty:
  "null xq \<longleftrightarrow> is_empty (pred_of_seq xq)"
  by (induct xq) (simp_all add: is_empty_bot not_is_empty_single is_empty_sup)

lemma is_empty_code [code]:
  "is_empty (Seq f) \<longleftrightarrow> null (f ())"
  by (simp add: null_is_empty Seq_def)

primrec the_only :: "(unit \<Rightarrow> 'a) \<Rightarrow> 'a seq \<Rightarrow> 'a" where
  [code del]: "the_only dfault Empty = dfault ()"
| "the_only dfault (Insert x P) = (if is_empty P then x else let y = singleton dfault P in if x = y then x else dfault ())"
| "the_only dfault (Join P xq) = (if is_empty P then the_only dfault xq else if null xq then singleton dfault P
       else let x = singleton dfault P; y = the_only dfault xq in
       if x = y then x else dfault ())"

lemma the_only_singleton:
  "the_only dfault xq = singleton dfault (pred_of_seq xq)"
  by (induct xq)
    (auto simp add: singleton_bot singleton_single is_empty_def
    null_is_empty Let_def singleton_sup)

lemma singleton_code [code]:
  "singleton dfault (Seq f) = (case f ()
   of Empty \<Rightarrow> dfault ()
    | Insert x P \<Rightarrow> if is_empty P then x
        else let y = singleton dfault P in
          if x = y then x else dfault ()
    | Join P xq \<Rightarrow> if is_empty P then the_only dfault xq
        else if null xq then singleton dfault P
        else let x = singleton dfault P; y = the_only dfault xq in
          if x = y then x else dfault ())"
  by (cases "f ()")
   (auto simp add: Seq_def the_only_singleton is_empty_def
      null_is_empty singleton_bot singleton_single singleton_sup Let_def)

definition the :: "'a pred \<Rightarrow> 'a" where
  "the A = (THE x. eval A x)"

lemma the_eqI:
  "(THE x. eval P x) = x \<Longrightarrow> the P = x"
  by (simp add: the_def)

definition not_unique :: "'a pred \<Rightarrow> 'a" where
  [code del]: "not_unique A = (THE x. eval A x)"

code_abort not_unique

lemma the_eq [code]: "the A = singleton (\<lambda>x. not_unique A) A"
  by (rule the_eqI) (simp add: singleton_def not_unique_def)

code_reflect Predicate
  datatypes pred = Seq and seq = Empty | Insert | Join
  functions map

ML {*
signature PREDICATE =
sig
  datatype 'a pred = Seq of (unit -> 'a seq)
  and 'a seq = Empty | Insert of 'a * 'a pred | Join of 'a pred * 'a seq
  val yield: 'a pred -> ('a * 'a pred) option
  val yieldn: int -> 'a pred -> 'a list * 'a pred
  val map: ('a -> 'b) -> 'a pred -> 'b pred
end;

structure Predicate : PREDICATE =
struct

datatype pred = datatype Predicate.pred
datatype seq = datatype Predicate.seq

fun map f = Predicate.map f;

fun yield (Seq f) = next (f ())
and next Empty = NONE
  | next (Insert (x, P)) = SOME (x, P)
  | next (Join (P, xq)) = (case yield P
     of NONE => next xq
      | SOME (x, Q) => SOME (x, Seq (fn _ => Join (Q, xq))));

fun anamorph f k x = (if k = 0 then ([], x)
  else case f x
   of NONE => ([], x)
    | SOME (v, y) => let
        val (vs, z) = anamorph f (k - 1) y
      in (v :: vs, z) end);

fun yieldn P = anamorph yield P;

end;
*}

lemma eval_mem [simp]:
  "x \<in> eval P \<longleftrightarrow> eval P x"
  by (simp add: mem_def)

lemma eq_mem [simp]:
  "x \<in> (op =) y \<longleftrightarrow> x = y"
  by (auto simp add: mem_def)

no_notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf (infixl "\<sqinter>" 70) and
  sup (infixl "\<squnion>" 65) and
  Inf ("\<Sqinter>_" [900] 900) and
  Sup ("\<Squnion>_" [900] 900) and
  bind (infixl "\<guillemotright>=" 70)

no_syntax (xsymbols)
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)

hide_type (open) pred seq
hide_const (open) Pred eval single bind is_empty singleton if_pred not_pred holds
  Empty Insert Join Seq member pred_of_seq "apply" adjunct null the_only eq map not_unique the

end
