(*  Title:      HOL/Predicate.thy
    Author:     Stefan Berghofer and Lukas Bulwahn and Florian Haftmann, TU Muenchen
*)

header {* Predicates as relations and enumerations *}

theory Predicate
imports Inductive Relation
begin

notation
  inf (infixl "\<sqinter>" 70) and
  sup (infixl "\<squnion>" 65) and
  Inf ("\<Sqinter>_" [900] 900) and
  Sup ("\<Squnion>_" [900] 900) and
  top ("\<top>") and
  bot ("\<bottom>")


subsection {* Predicates as (complete) lattices *}

subsubsection {* Equality *}

lemma pred_equals_eq: "((\<lambda>x. x \<in> R) = (\<lambda>x. x \<in> S)) = (R = S)"
  by (simp add: mem_def)

lemma pred_equals_eq2 [pred_set_conv]: "((\<lambda>x y. (x, y) \<in> R) = (\<lambda>x y. (x, y) \<in> S)) = (R = S)"
  by (simp add: expand_fun_eq mem_def)


subsubsection {* Order relation *}

lemma pred_subset_eq: "((\<lambda>x. x \<in> R) <= (\<lambda>x. x \<in> S)) = (R <= S)"
  by (simp add: mem_def)

lemma pred_subset_eq2 [pred_set_conv]: "((\<lambda>x y. (x, y) \<in> R) <= (\<lambda>x y. (x, y) \<in> S)) = (R <= S)"
  by fast


subsubsection {* Top and bottom elements *}

lemma top1I [intro!]: "top x"
  by (simp add: top_fun_eq top_bool_eq)

lemma top2I [intro!]: "top x y"
  by (simp add: top_fun_eq top_bool_eq)

lemma bot1E [elim!]: "bot x \<Longrightarrow> P"
  by (simp add: bot_fun_eq bot_bool_eq)

lemma bot2E [elim!]: "bot x y \<Longrightarrow> P"
  by (simp add: bot_fun_eq bot_bool_eq)

lemma bot_empty_eq: "bot = (\<lambda>x. x \<in> {})"
  by (auto simp add: expand_fun_eq)

lemma bot_empty_eq2: "bot = (\<lambda>x y. (x, y) \<in> {})"
  by (auto simp add: expand_fun_eq)


subsubsection {* Binary union *}

lemma sup1I1 [elim?]: "A x \<Longrightarrow> sup A B x"
  by (simp add: sup_fun_eq sup_bool_eq)

lemma sup2I1 [elim?]: "A x y \<Longrightarrow> sup A B x y"
  by (simp add: sup_fun_eq sup_bool_eq)

lemma sup1I2 [elim?]: "B x \<Longrightarrow> sup A B x"
  by (simp add: sup_fun_eq sup_bool_eq)

lemma sup2I2 [elim?]: "B x y \<Longrightarrow> sup A B x y"
  by (simp add: sup_fun_eq sup_bool_eq)

lemma sup1E [elim!]: "sup A B x ==> (A x ==> P) ==> (B x ==> P) ==> P"
  by (simp add: sup_fun_eq sup_bool_eq) iprover

lemma sup2E [elim!]: "sup A B x y ==> (A x y ==> P) ==> (B x y ==> P) ==> P"
  by (simp add: sup_fun_eq sup_bool_eq) iprover

text {*
  \medskip Classical introduction rule: no commitment to @{text A} vs
  @{text B}.
*}

lemma sup1CI [intro!]: "(~ B x ==> A x) ==> sup A B x"
  by (auto simp add: sup_fun_eq sup_bool_eq)

lemma sup2CI [intro!]: "(~ B x y ==> A x y) ==> sup A B x y"
  by (auto simp add: sup_fun_eq sup_bool_eq)

lemma sup_Un_eq: "sup (\<lambda>x. x \<in> R) (\<lambda>x. x \<in> S) = (\<lambda>x. x \<in> R \<union> S)"
  by (simp add: sup_fun_eq sup_bool_eq mem_def)

lemma sup_Un_eq2 [pred_set_conv]: "sup (\<lambda>x y. (x, y) \<in> R) (\<lambda>x y. (x, y) \<in> S) = (\<lambda>x y. (x, y) \<in> R \<union> S)"
  by (simp add: sup_fun_eq sup_bool_eq mem_def)


subsubsection {* Binary intersection *}

lemma inf1I [intro!]: "A x ==> B x ==> inf A B x"
  by (simp add: inf_fun_eq inf_bool_eq)

lemma inf2I [intro!]: "A x y ==> B x y ==> inf A B x y"
  by (simp add: inf_fun_eq inf_bool_eq)

lemma inf1E [elim!]: "inf A B x ==> (A x ==> B x ==> P) ==> P"
  by (simp add: inf_fun_eq inf_bool_eq)

lemma inf2E [elim!]: "inf A B x y ==> (A x y ==> B x y ==> P) ==> P"
  by (simp add: inf_fun_eq inf_bool_eq)

lemma inf1D1: "inf A B x ==> A x"
  by (simp add: inf_fun_eq inf_bool_eq)

lemma inf2D1: "inf A B x y ==> A x y"
  by (simp add: inf_fun_eq inf_bool_eq)

lemma inf1D2: "inf A B x ==> B x"
  by (simp add: inf_fun_eq inf_bool_eq)

lemma inf2D2: "inf A B x y ==> B x y"
  by (simp add: inf_fun_eq inf_bool_eq)

lemma inf_Int_eq: "inf (\<lambda>x. x \<in> R) (\<lambda>x. x \<in> S) = (\<lambda>x. x \<in> R \<inter> S)"
  by (simp add: inf_fun_eq inf_bool_eq mem_def)

lemma inf_Int_eq2 [pred_set_conv]: "inf (\<lambda>x y. (x, y) \<in> R) (\<lambda>x y. (x, y) \<in> S) = (\<lambda>x y. (x, y) \<in> R \<inter> S)"
  by (simp add: inf_fun_eq inf_bool_eq mem_def)


subsubsection {* Unions of families *}

lemma SUP1_iff: "(SUP x:A. B x) b = (EX x:A. B x b)"
  by (simp add: SUPR_def Sup_fun_def Sup_bool_def) blast

lemma SUP2_iff: "(SUP x:A. B x) b c = (EX x:A. B x b c)"
  by (simp add: SUPR_def Sup_fun_def Sup_bool_def) blast

lemma SUP1_I [intro]: "a : A ==> B a b ==> (SUP x:A. B x) b"
  by (auto simp add: SUP1_iff)

lemma SUP2_I [intro]: "a : A ==> B a b c ==> (SUP x:A. B x) b c"
  by (auto simp add: SUP2_iff)

lemma SUP1_E [elim!]: "(SUP x:A. B x) b ==> (!!x. x : A ==> B x b ==> R) ==> R"
  by (auto simp add: SUP1_iff)

lemma SUP2_E [elim!]: "(SUP x:A. B x) b c ==> (!!x. x : A ==> B x b c ==> R) ==> R"
  by (auto simp add: SUP2_iff)

lemma SUP_UN_eq: "(SUP i. (\<lambda>x. x \<in> r i)) = (\<lambda>x. x \<in> (UN i. r i))"
  by (simp add: SUP1_iff expand_fun_eq)

lemma SUP_UN_eq2: "(SUP i. (\<lambda>x y. (x, y) \<in> r i)) = (\<lambda>x y. (x, y) \<in> (UN i. r i))"
  by (simp add: SUP2_iff expand_fun_eq)


subsubsection {* Intersections of families *}

lemma INF1_iff: "(INF x:A. B x) b = (ALL x:A. B x b)"
  by (simp add: INFI_def Inf_fun_def Inf_bool_def) blast

lemma INF2_iff: "(INF x:A. B x) b c = (ALL x:A. B x b c)"
  by (simp add: INFI_def Inf_fun_def Inf_bool_def) blast

lemma INF1_I [intro!]: "(!!x. x : A ==> B x b) ==> (INF x:A. B x) b"
  by (auto simp add: INF1_iff)

lemma INF2_I [intro!]: "(!!x. x : A ==> B x b c) ==> (INF x:A. B x) b c"
  by (auto simp add: INF2_iff)

lemma INF1_D [elim]: "(INF x:A. B x) b ==> a : A ==> B a b"
  by (auto simp add: INF1_iff)

lemma INF2_D [elim]: "(INF x:A. B x) b c ==> a : A ==> B a b c"
  by (auto simp add: INF2_iff)

lemma INF1_E [elim]: "(INF x:A. B x) b ==> (B a b ==> R) ==> (a ~: A ==> R) ==> R"
  by (auto simp add: INF1_iff)

lemma INF2_E [elim]: "(INF x:A. B x) b c ==> (B a b c ==> R) ==> (a ~: A ==> R) ==> R"
  by (auto simp add: INF2_iff)

lemma INF_INT_eq: "(INF i. (\<lambda>x. x \<in> r i)) = (\<lambda>x. x \<in> (INT i. r i))"
  by (simp add: INF1_iff expand_fun_eq)

lemma INF_INT_eq2: "(INF i. (\<lambda>x y. (x, y) \<in> r i)) = (\<lambda>x y. (x, y) \<in> (INT i. r i))"
  by (simp add: INF2_iff expand_fun_eq)


subsection {* Predicates as relations *}

subsubsection {* Composition  *}

inductive
  pred_comp  :: "['a => 'b => bool, 'b => 'c => bool] => 'a => 'c => bool"
    (infixr "OO" 75)
  for r :: "'a => 'b => bool" and s :: "'b => 'c => bool"
where
  pred_compI [intro]: "r a b ==> s b c ==> (r OO s) a c"

inductive_cases pred_compE [elim!]: "(r OO s) a c"

lemma pred_comp_rel_comp_eq [pred_set_conv]:
  "((\<lambda>x y. (x, y) \<in> r) OO (\<lambda>x y. (x, y) \<in> s)) = (\<lambda>x y. (x, y) \<in> r O s)"
  by (auto simp add: expand_fun_eq elim: pred_compE)


subsubsection {* Converse *}

inductive
  conversep :: "('a => 'b => bool) => 'b => 'a => bool"
    ("(_^--1)" [1000] 1000)
  for r :: "'a => 'b => bool"
where
  conversepI: "r a b ==> r^--1 b a"

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
  by (auto simp add: expand_fun_eq)

lemma conversep_conversep [simp]: "(r^--1)^--1 = r"
  by (iprover intro: order_antisym conversepI dest: conversepD)

lemma converse_pred_comp: "(r OO s)^--1 = s^--1 OO r^--1"
  by (iprover intro: order_antisym conversepI pred_compI
    elim: pred_compE dest: conversepD)

lemma converse_meet: "(inf r s)^--1 = inf r^--1 s^--1"
  by (simp add: inf_fun_eq inf_bool_eq)
    (iprover intro: conversepI ext dest: conversepD)

lemma converse_join: "(sup r s)^--1 = sup r^--1 s^--1"
  by (simp add: sup_fun_eq sup_bool_eq)
    (iprover intro: conversepI ext dest: conversepD)

lemma conversep_noteq [simp]: "(op ~=)^--1 = op ~="
  by (auto simp add: expand_fun_eq)

lemma conversep_eq [simp]: "(op =)^--1 = op ="
  by (auto simp add: expand_fun_eq)


subsubsection {* Domain *}

inductive
  DomainP :: "('a => 'b => bool) => 'a => bool"
  for r :: "'a => 'b => bool"
where
  DomainPI [intro]: "r a b ==> DomainP r a"

inductive_cases DomainPE [elim!]: "DomainP r a"

lemma DomainP_Domain_eq [pred_set_conv]: "DomainP (\<lambda>x y. (x, y) \<in> r) = (\<lambda>x. x \<in> Domain r)"
  by (blast intro!: Orderings.order_antisym predicate1I)


subsubsection {* Range *}

inductive
  RangeP :: "('a => 'b => bool) => 'b => bool"
  for r :: "'a => 'b => bool"
where
  RangePI [intro]: "r a b ==> RangeP r b"

inductive_cases RangePE [elim!]: "RangeP r b"

lemma RangeP_Range_eq [pred_set_conv]: "RangeP (\<lambda>x y. (x, y) \<in> r) = (\<lambda>x. x \<in> Range r)"
  by (blast intro!: Orderings.order_antisym predicate1I)


subsubsection {* Inverse image *}

definition
  inv_imagep :: "('b => 'b => bool) => ('a => 'b) => 'a => 'a => bool" where
  "inv_imagep r f == %x y. r (f x) (f y)"

lemma [pred_set_conv]: "inv_imagep (\<lambda>x y. (x, y) \<in> r) f = (\<lambda>x y. (x, y) \<in> inv_image r f)"
  by (simp add: inv_image_def inv_imagep_def)

lemma in_inv_imagep [simp]: "inv_imagep r f x y = r (f x) (f y)"
  by (simp add: inv_imagep_def)


subsubsection {* Powerset *}

definition Powp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "Powp A == \<lambda>B. \<forall>x \<in> B. A x"

lemma Powp_Pow_eq [pred_set_conv]: "Powp (\<lambda>x. x \<in> A) = (\<lambda>x. x \<in> Pow A)"
  by (auto simp add: Powp_def expand_fun_eq)

lemmas Powp_mono [mono] = Pow_mono [to_pred pred_subset_eq]


subsubsection {* Properties of relations *}

abbreviation antisymP :: "('a => 'a => bool) => bool" where
  "antisymP r == antisym {(x, y). r x y}"

abbreviation transP :: "('a => 'a => bool) => bool" where
  "transP r == trans {(x, y). r x y}"

abbreviation single_valuedP :: "('a => 'b => bool) => bool" where
  "single_valuedP r == single_valued {(x, y). r x y}"


subsection {* Predicates as enumerations *}

subsubsection {* The type of predicate enumerations (a monad) *}

datatype 'a pred = Pred "'a \<Rightarrow> bool"

primrec eval :: "'a pred \<Rightarrow> 'a \<Rightarrow> bool" where
  eval_pred: "eval (Pred f) = f"

lemma Pred_eval [simp]:
  "Pred (eval x) = x"
  by (cases x) simp

lemma eval_inject: "eval x = eval y \<longleftrightarrow> x = y"
  by (cases x) auto

definition single :: "'a \<Rightarrow> 'a pred" where
  "single x = Pred ((op =) x)"

definition bind :: "'a pred \<Rightarrow> ('a \<Rightarrow> 'b pred) \<Rightarrow> 'b pred" (infixl "\<guillemotright>=" 70) where
  "P \<guillemotright>= f = Pred (\<lambda>x. (\<exists>y. eval P y \<and> eval (f y) x))"

instantiation pred :: (type) "{complete_lattice, boolean_algebra}"
begin

definition
  "P \<le> Q \<longleftrightarrow> eval P \<le> eval Q"

definition
  "P < Q \<longleftrightarrow> eval P < eval Q"

definition
  "\<bottom> = Pred \<bottom>"

definition
  "\<top> = Pred \<top>"

definition
  "P \<sqinter> Q = Pred (eval P \<sqinter> eval Q)"

definition
  "P \<squnion> Q = Pred (eval P \<squnion> eval Q)"

definition
  [code del]: "\<Sqinter>A = Pred (INFI A eval)"

definition
  [code del]: "\<Squnion>A = Pred (SUPR A eval)"

definition
  "- P = Pred (- eval P)"

definition
  "P - Q = Pred (eval P - eval Q)"

instance proof
qed (auto simp add: less_eq_pred_def less_pred_def
    inf_pred_def sup_pred_def bot_pred_def top_pred_def
    Inf_pred_def Sup_pred_def uminus_pred_def minus_pred_def fun_Compl_def bool_Compl_def,
    auto simp add: le_fun_def less_fun_def le_bool_def less_bool_def
    eval_inject mem_def)

end

lemma bind_bind:
  "(P \<guillemotright>= Q) \<guillemotright>= R = P \<guillemotright>= (\<lambda>x. Q x \<guillemotright>= R)"
  by (auto simp add: bind_def expand_fun_eq)

lemma bind_single:
  "P \<guillemotright>= single = P"
  by (simp add: bind_def single_def)

lemma single_bind:
  "single x \<guillemotright>= P = P x"
  by (simp add: bind_def single_def)

lemma bottom_bind:
  "\<bottom> \<guillemotright>= P = \<bottom>"
  by (auto simp add: bot_pred_def bind_def expand_fun_eq)

lemma sup_bind:
  "(P \<squnion> Q) \<guillemotright>= R = P \<guillemotright>= R \<squnion> Q \<guillemotright>= R"
  by (auto simp add: bind_def sup_pred_def expand_fun_eq)

lemma Sup_bind: "(\<Squnion>A \<guillemotright>= f) = \<Squnion>((\<lambda>x. x \<guillemotright>= f) ` A)"
  by (auto simp add: bind_def Sup_pred_def SUP1_iff expand_fun_eq)

lemma pred_iffI:
  assumes "\<And>x. eval A x \<Longrightarrow> eval B x"
  and "\<And>x. eval B x \<Longrightarrow> eval A x"
  shows "A = B"
proof -
  from assms have "\<And>x. eval A x \<longleftrightarrow> eval B x" by blast
  then show ?thesis by (cases A, cases B) (simp add: expand_fun_eq)
qed
  
lemma singleI: "eval (single x) x"
  unfolding single_def by simp

lemma singleI_unit: "eval (single ()) x"
  by simp (rule singleI)

lemma singleE: "eval (single x) y \<Longrightarrow> (y = x \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding single_def by simp

lemma singleE': "eval (single x) y \<Longrightarrow> (x = y \<Longrightarrow> P) \<Longrightarrow> P"
  by (erule singleE) simp

lemma bindI: "eval P x \<Longrightarrow> eval (Q x) y \<Longrightarrow> eval (P \<guillemotright>= Q) y"
  unfolding bind_def by auto

lemma bindE: "eval (R \<guillemotright>= Q) y \<Longrightarrow> (\<And>x. eval R x \<Longrightarrow> eval (Q x) y \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding bind_def by auto

lemma botE: "eval \<bottom> x \<Longrightarrow> P"
  unfolding bot_pred_def by auto

lemma supI1: "eval A x \<Longrightarrow> eval (A \<squnion> B) x"
  unfolding sup_pred_def by (simp add: sup_fun_eq sup_bool_eq)

lemma supI2: "eval B x \<Longrightarrow> eval (A \<squnion> B) x" 
  unfolding sup_pred_def by (simp add: sup_fun_eq sup_bool_eq)

lemma supE: "eval (A \<squnion> B) x \<Longrightarrow> (eval A x \<Longrightarrow> P) \<Longrightarrow> (eval B x \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding sup_pred_def by auto

lemma single_not_bot [simp]:
  "single x \<noteq> \<bottom>"
  by (auto simp add: single_def bot_pred_def expand_fun_eq)

lemma not_bot:
  assumes "A \<noteq> \<bottom>"
  obtains x where "eval A x"
using assms by (cases A)
  (auto simp add: bot_pred_def, auto simp add: mem_def)
  

subsubsection {* Emptiness check and definite choice *}

definition is_empty :: "'a pred \<Rightarrow> bool" where
  "is_empty A \<longleftrightarrow> A = \<bottom>"

lemma is_empty_bot:
  "is_empty \<bottom>"
  by (simp add: is_empty_def)

lemma not_is_empty_single:
  "\<not> is_empty (single x)"
  by (auto simp add: is_empty_def single_def bot_pred_def expand_fun_eq)

lemma is_empty_sup:
  "is_empty (A \<squnion> B) \<longleftrightarrow> is_empty A \<and> is_empty B"
  by (auto simp add: is_empty_def intro: sup_eq_bot_eq1 sup_eq_bot_eq2)

definition singleton :: "(unit => 'a) \<Rightarrow> 'a pred \<Rightarrow> 'a" where
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
    by (simp (no_asm_use) add: single_def expand_fun_eq) blast
  then show ?thesis by (simp add: eval_inject)
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
  by (auto simp add: expand_fun_eq elim: botE)
next
  case Insert show ?case
  by (auto simp add: expand_fun_eq elim: supE singleE intro: supI1 supI2 singleI)
next
  case Join then show ?case
  by (auto simp add: expand_fun_eq elim: supE intro: supI1 supI2)
qed

lemma eval_code [code]: "eval (Seq f) = member (f ())"
  unfolding Seq_def by (rule sym, rule eval_member)

lemma single_code [code]:
  "single x = Seq (\<lambda>u. Insert x \<bottom>)"
  unfolding Seq_def by simp

primrec "apply" :: "('a \<Rightarrow> 'b Predicate.pred) \<Rightarrow> 'a seq \<Rightarrow> 'b seq" where
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
    unfolding Seq_def by (simp add: sup_commute [of "\<bottom>"]  sup_bot)
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
  by (auto simp add: single_def less_eq_pred_def mem_def)

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
  shows "eq_class.eq P Q \<longleftrightarrow> P \<le> Q \<and> Q \<le> P"
  unfolding eq by auto

lemma [code]:
  "pred_case f P = f (eval P)"
  by (cases P) simp

lemma [code]:
  "pred_rec f P = f (eval P)"
  by (cases P) simp

inductive eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where "eq x x"

lemma eq_is_eq: "eq x y \<equiv> (x = y)"
  by (rule eq_reflection) (auto intro: eq.intros elim: eq.cases)

definition map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a pred \<Rightarrow> 'b pred" where
  "map f P = P \<guillemotright>= (single o f)"

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

definition not_unique :: "'a pred => 'a"
where
  [code del]: "not_unique A = (THE x. eval A x)"

definition the :: "'a pred => 'a"
where
  [code del]: "the A = (THE x. eval A x)"

lemma the_eq[code]: "the A = singleton (\<lambda>x. not_unique A) A"
by (auto simp add: the_def singleton_def not_unique_def)

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

@{code_datatype pred = Seq};
@{code_datatype seq = Empty | Insert | Join};

fun yield (@{code Seq} f) = next (f ())
and next @{code Empty} = NONE
  | next (@{code Insert} (x, P)) = SOME (x, P)
  | next (@{code Join} (P, xq)) = (case yield P
     of NONE => next xq
      | SOME (x, Q) => SOME (x, @{code Seq} (fn _ => @{code Join} (Q, xq))))

fun anamorph f k x = (if k = 0 then ([], x)
  else case f x
   of NONE => ([], x)
    | SOME (v, y) => let
        val (vs, z) = anamorph f (k - 1) y
      in (v :: vs, z) end)

fun yieldn P = anamorph yield P;

fun map f = @{code map} f;

end;
*}

code_reserved Eval Predicate

code_type pred and seq
  (Eval "_/ Predicate.pred" and "_/ Predicate.seq")

code_const Seq and Empty and Insert and Join
  (Eval "Predicate.Seq" and "Predicate.Empty" and "Predicate.Insert/ (_,/ _)" and "Predicate.Join/ (_,/ _)")

code_abort not_unique

text {* dummy setup for @{text code_pred} and @{text values} keywords *}

ML {*
local

structure P = OuterParse;

val opt_modes = Scan.optional (P.$$$ "(" |-- P.!!! (Scan.repeat1 P.xname --| P.$$$ ")")) [];

in

val _ = OuterSyntax.local_theory_to_proof "code_pred" "sets up goal for cases rule from given introduction rules and compiles predicate"
  OuterKeyword.thy_goal (P.term_group >> (K (Proof.theorem_i NONE (K I) [[]])));

val _ = OuterSyntax.improper_command "values" "enumerate and print comprehensions"
  OuterKeyword.diag ((opt_modes -- P.term)
    >> (fn (modes, t) => Toplevel.no_timing o Toplevel.keep
        (K ())));

end
*}

no_notation
  inf (infixl "\<sqinter>" 70) and
  sup (infixl "\<squnion>" 65) and
  Inf ("\<Sqinter>_" [900] 900) and
  Sup ("\<Squnion>_" [900] 900) and
  top ("\<top>") and
  bot ("\<bottom>") and
  bind (infixl "\<guillemotright>=" 70)

hide (open) type pred seq
hide (open) const Pred eval single bind is_empty singleton if_pred not_pred
  Empty Insert Join Seq member pred_of_seq "apply" adjunct null the_only eq map not_unique the

end
