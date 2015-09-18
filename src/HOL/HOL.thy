(*  Title:      HOL/HOL.thy
    Author:     Tobias Nipkow, Markus Wenzel, and Larry Paulson
*)

section \<open>The basis of Higher-Order Logic\<close>

theory HOL
imports Pure "~~/src/Tools/Code_Generator"
keywords
  "try" "solve_direct" "quickcheck" "print_coercions" "print_claset"
    "print_induct_rules" :: diag and
  "quickcheck_params" :: thy_decl
begin

ML_file "~~/src/Tools/misc_legacy.ML"
ML_file "~~/src/Tools/try.ML"
ML_file "~~/src/Tools/quickcheck.ML"
ML_file "~~/src/Tools/solve_direct.ML"
ML_file "~~/src/Tools/IsaPlanner/zipper.ML"
ML_file "~~/src/Tools/IsaPlanner/isand.ML"
ML_file "~~/src/Tools/IsaPlanner/rw_inst.ML"
ML_file "~~/src/Provers/hypsubst.ML"
ML_file "~~/src/Provers/splitter.ML"
ML_file "~~/src/Provers/classical.ML"
ML_file "~~/src/Provers/blast.ML"
ML_file "~~/src/Provers/clasimp.ML"
ML_file "~~/src/Tools/eqsubst.ML"
ML_file "~~/src/Provers/quantifier1.ML"
ML_file "~~/src/Tools/atomize_elim.ML"
ML_file "~~/src/Tools/cong_tac.ML"
ML_file "~~/src/Tools/intuitionistic.ML" setup \<open>Intuitionistic.method_setup @{binding iprover}\<close>
ML_file "~~/src/Tools/project_rule.ML"
ML_file "~~/src/Tools/subtyping.ML"
ML_file "~~/src/Tools/case_product.ML"


ML \<open>Plugin_Name.declare_setup @{binding extraction}\<close>

ML \<open>
  Plugin_Name.declare_setup @{binding quickcheck_random};
  Plugin_Name.declare_setup @{binding quickcheck_exhaustive};
  Plugin_Name.declare_setup @{binding quickcheck_bounded_forall};
  Plugin_Name.declare_setup @{binding quickcheck_full_exhaustive};
  Plugin_Name.declare_setup @{binding quickcheck_narrowing};
\<close>
ML \<open>
  Plugin_Name.define_setup @{binding quickcheck}
   [@{plugin quickcheck_exhaustive},
    @{plugin quickcheck_random},
    @{plugin quickcheck_bounded_forall},
    @{plugin quickcheck_full_exhaustive},
    @{plugin quickcheck_narrowing}]
\<close>


subsection \<open>Primitive logic\<close>

subsubsection \<open>Core syntax\<close>

setup \<open>Axclass.class_axiomatization (@{binding type}, [])\<close>
default_sort type
setup \<open>Object_Logic.add_base_sort @{sort type}\<close>

axiomatization where fun_arity: "OFCLASS('a \<Rightarrow> 'b, type_class)"
instance "fun" :: (type, type) type by (rule fun_arity)

axiomatization where itself_arity: "OFCLASS('a itself, type_class)"
instance itself :: (type) type by (rule itself_arity)

typedecl bool

judgment
  Trueprop      :: "bool \<Rightarrow> prop"                   ("(_)" 5)

axiomatization
  implies       :: "[bool, bool] \<Rightarrow> bool"           (infixr "-->" 25)  and
  eq            :: "['a, 'a] \<Rightarrow> bool"               (infixl "=" 50)  and
  The           :: "('a \<Rightarrow> bool) \<Rightarrow> 'a"

consts
  True          :: bool
  False         :: bool
  Not           :: "bool \<Rightarrow> bool"                   ("~ _" [40] 40)

  conj          :: "[bool, bool] \<Rightarrow> bool"           (infixr "&" 35)
  disj          :: "[bool, bool] \<Rightarrow> bool"           (infixr "|" 30)

  All           :: "('a \<Rightarrow> bool) \<Rightarrow> bool"           (binder "ALL " 10)
  Ex            :: "('a \<Rightarrow> bool) \<Rightarrow> bool"           (binder "EX " 10)
  Ex1           :: "('a \<Rightarrow> bool) \<Rightarrow> bool"           (binder "EX! " 10)


subsubsection \<open>Additional concrete syntax\<close>

notation (output)
  eq  (infix "=" 50)

abbreviation
  not_equal :: "['a, 'a] \<Rightarrow> bool"  (infixl "~=" 50) where
  "x ~= y \<equiv> ~ (x = y)"

notation (output)
  not_equal  (infix "~=" 50)

notation (xsymbols)
  Not  ("\<not> _" [40] 40) and
  conj  (infixr "\<and>" 35) and
  disj  (infixr "\<or>" 30) and
  implies  (infixr "\<longrightarrow>" 25) and
  not_equal  (infixl "\<noteq>" 50)

notation (xsymbols output)
  not_equal  (infix "\<noteq>" 50)

notation (HTML output)
  Not  ("\<not> _" [40] 40) and
  conj  (infixr "\<and>" 35) and
  disj  (infixr "\<or>" 30) and
  not_equal  (infix "\<noteq>" 50)

abbreviation (iff)
  iff :: "[bool, bool] \<Rightarrow> bool"  (infixr "<->" 25) where
  "A <-> B \<equiv> A = B"

notation (xsymbols)
  iff  (infixr "\<longleftrightarrow>" 25)

syntax "_The" :: "[pttrn, bool] \<Rightarrow> 'a"  ("(3THE _./ _)" [0, 10] 10)
translations "THE x. P" \<rightleftharpoons> "CONST The (\<lambda>x. P)"
print_translation \<open>
  [(@{const_syntax The}, fn _ => fn [Abs abs] =>
      let val (x, t) = Syntax_Trans.atomic_abs_tr' abs
      in Syntax.const @{syntax_const "_The"} $ x $ t end)]
\<close>  -- \<open>To avoid eta-contraction of body\<close>

nonterminal letbinds and letbind
syntax
  "_bind"       :: "[pttrn, 'a] \<Rightarrow> letbind"              ("(2_ =/ _)" 10)
  ""            :: "letbind \<Rightarrow> letbinds"                 ("_")
  "_binds"      :: "[letbind, letbinds] \<Rightarrow> letbinds"     ("_;/ _")
  "_Let"        :: "[letbinds, 'a] \<Rightarrow> 'a"                ("(let (_)/ in (_))" [0, 10] 10)

nonterminal case_syn and cases_syn
syntax
  "_case_syntax" :: "['a, cases_syn] \<Rightarrow> 'b"  ("(case _ of/ _)" 10)
  "_case1" :: "['a, 'b] \<Rightarrow> case_syn"  ("(2_ =>/ _)" 10)
  "" :: "case_syn \<Rightarrow> cases_syn"  ("_")
  "_case2" :: "[case_syn, cases_syn] \<Rightarrow> cases_syn"  ("_/ | _")
syntax (xsymbols)
  "_case1" :: "['a, 'b] \<Rightarrow> case_syn"  ("(2_ \<Rightarrow>/ _)" 10)

notation (xsymbols)
  All  (binder "\<forall>" 10) and
  Ex  (binder "\<exists>" 10) and
  Ex1  (binder "\<exists>!" 10)

notation (HTML output)
  All  (binder "\<forall>" 10) and
  Ex  (binder "\<exists>" 10) and
  Ex1  (binder "\<exists>!" 10)

notation (HOL)
  All  (binder "! " 10) and
  Ex  (binder "? " 10) and
  Ex1  (binder "?! " 10)


subsubsection \<open>Axioms and basic definitions\<close>

axiomatization where
  refl: "t = (t::'a)" and
  subst: "s = t \<Longrightarrow> P s \<Longrightarrow> P t" and
  ext: "(\<And>x::'a. (f x ::'b) = g x) \<Longrightarrow> (\<lambda>x. f x) = (\<lambda>x. g x)"
    -- \<open>Extensionality is built into the meta-logic, and this rule expresses
         a related property.  It is an eta-expanded version of the traditional
         rule, and similar to the ABS rule of HOL\<close> and

  the_eq_trivial: "(THE x. x = a) = (a::'a)"

axiomatization where
  impI: "(P \<Longrightarrow> Q) \<Longrightarrow> P \<longrightarrow> Q" and
  mp: "\<lbrakk>P \<longrightarrow> Q; P\<rbrakk> \<Longrightarrow> Q" and

  iff: "(P \<longrightarrow> Q) \<longrightarrow> (Q \<longrightarrow> P) \<longrightarrow> (P = Q)" and
  True_or_False: "(P = True) \<or> (P = False)"

defs
  True_def:     "True      \<equiv> ((\<lambda>x::bool. x) = (\<lambda>x. x))"
  All_def:      "All P     \<equiv> (P = (\<lambda>x. True))"
  Ex_def:       "Ex P      \<equiv> \<forall>Q. (\<forall>x. P x \<longrightarrow> Q) \<longrightarrow> Q"
  False_def:    "False     \<equiv> (\<forall>P. P)"
  not_def:      "\<not> P       \<equiv> P \<longrightarrow> False"
  and_def:      "P \<and> Q     \<equiv> \<forall>R. (P \<longrightarrow> Q \<longrightarrow> R) \<longrightarrow> R"
  or_def:       "P \<or> Q     \<equiv> \<forall>R. (P \<longrightarrow> R) \<longrightarrow> (Q \<longrightarrow> R) \<longrightarrow> R"
  Ex1_def:      "Ex1 P     \<equiv> \<exists>x. P x \<and> (\<forall>y. P y \<longrightarrow> y = x)"

definition If :: "bool \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("(if (_)/ then (_)/ else (_))" [0, 0, 10] 10)
  where "If P x y \<equiv> (THE z::'a. (P = True \<longrightarrow> z = x) \<and> (P = False \<longrightarrow> z = y))"

definition Let :: "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b"
  where "Let s f \<equiv> f s"

translations
  "_Let (_binds b bs) e"  \<rightleftharpoons> "_Let b (_Let bs e)"
  "let x = a in e"        \<rightleftharpoons> "CONST Let a (\<lambda>x. e)"

axiomatization undefined :: 'a

class default = fixes default :: 'a


subsection \<open>Fundamental rules\<close>

subsubsection \<open>Equality\<close>

lemma sym: "s = t \<Longrightarrow> t = s"
  by (erule subst) (rule refl)

lemma ssubst: "t = s \<Longrightarrow> P s \<Longrightarrow> P t"
  by (drule sym) (erule subst)

lemma trans: "\<lbrakk>r = s; s = t\<rbrakk> \<Longrightarrow> r = t"
  by (erule subst)

lemma trans_sym [Pure.elim?]: "r = s \<Longrightarrow> t = s \<Longrightarrow> r = t"
  by (rule trans [OF _ sym])

lemma meta_eq_to_obj_eq:
  assumes meq: "A \<equiv> B"
  shows "A = B"
  by (unfold meq) (rule refl)

text \<open>Useful with @{text erule} for proving equalities from known equalities.\<close>
     (* a = b
        |   |
        c = d   *)
lemma box_equals: "\<lbrakk>a = b; a = c; b = d\<rbrakk> \<Longrightarrow> c = d"
apply (rule trans)
apply (rule trans)
apply (rule sym)
apply assumption+
done

text \<open>For calculational reasoning:\<close>

lemma forw_subst: "a = b \<Longrightarrow> P b \<Longrightarrow> P a"
  by (rule ssubst)

lemma back_subst: "P a \<Longrightarrow> a = b \<Longrightarrow> P b"
  by (rule subst)


subsubsection \<open>Congruence rules for application\<close>

text \<open>Similar to @{text AP_THM} in Gordon's HOL.\<close>
lemma fun_cong: "(f :: 'a \<Rightarrow> 'b) = g \<Longrightarrow> f x = g x"
apply (erule subst)
apply (rule refl)
done

text \<open>Similar to @{text AP_TERM} in Gordon's HOL and FOL's @{text subst_context}.\<close>
lemma arg_cong: "x = y \<Longrightarrow> f x = f y"
apply (erule subst)
apply (rule refl)
done

lemma arg_cong2: "\<lbrakk>a = b; c = d\<rbrakk> \<Longrightarrow> f a c = f b d"
apply (erule ssubst)+
apply (rule refl)
done

lemma cong: "\<lbrakk>f = g; (x::'a) = y\<rbrakk> \<Longrightarrow> f x = g y"
apply (erule subst)+
apply (rule refl)
done

ML \<open>fun cong_tac ctxt = Cong_Tac.cong_tac ctxt @{thm cong}\<close>


subsubsection \<open>Equality of booleans -- iff\<close>

lemma iffI: assumes "P \<Longrightarrow> Q" and "Q \<Longrightarrow> P" shows "P = Q"
  by (iprover intro: iff [THEN mp, THEN mp] impI assms)

lemma iffD2: "\<lbrakk>P = Q; Q\<rbrakk> \<Longrightarrow> P"
  by (erule ssubst)

lemma rev_iffD2: "\<lbrakk>Q; P = Q\<rbrakk> \<Longrightarrow> P"
  by (erule iffD2)

lemma iffD1: "Q = P \<Longrightarrow> Q \<Longrightarrow> P"
  by (drule sym) (rule iffD2)

lemma rev_iffD1: "Q \<Longrightarrow> Q = P \<Longrightarrow> P"
  by (drule sym) (rule rev_iffD2)

lemma iffE:
  assumes major: "P = Q"
    and minor: "\<lbrakk>P \<longrightarrow> Q; Q \<longrightarrow> P\<rbrakk> \<Longrightarrow> R"
  shows R
  by (iprover intro: minor impI major [THEN iffD2] major [THEN iffD1])


subsubsection \<open>True\<close>

lemma TrueI: "True"
  unfolding True_def by (rule refl)

lemma eqTrueI: "P \<Longrightarrow> P = True"
  by (iprover intro: iffI TrueI)

lemma eqTrueE: "P = True \<Longrightarrow> P"
  by (erule iffD2) (rule TrueI)


subsubsection \<open>Universal quantifier\<close>

lemma allI: assumes "\<And>x::'a. P x" shows "\<forall>x. P x"
  unfolding All_def by (iprover intro: ext eqTrueI assms)

lemma spec: "\<forall>x::'a. P x \<Longrightarrow> P x"
apply (unfold All_def)
apply (rule eqTrueE)
apply (erule fun_cong)
done

lemma allE:
  assumes major: "\<forall>x. P x"
    and minor: "P x \<Longrightarrow> R"
  shows R
  by (iprover intro: minor major [THEN spec])

lemma all_dupE:
  assumes major: "\<forall>x. P x"
    and minor: "\<lbrakk>P x; \<forall>x. P x\<rbrakk> \<Longrightarrow> R"
  shows R
  by (iprover intro: minor major major [THEN spec])


subsubsection \<open>False\<close>

text \<open>
  Depends upon @{text spec}; it is impossible to do propositional
  logic before quantifiers!
\<close>

lemma FalseE: "False \<Longrightarrow> P"
  apply (unfold False_def)
  apply (erule spec)
  done

lemma False_neq_True: "False = True \<Longrightarrow> P"
  by (erule eqTrueE [THEN FalseE])


subsubsection \<open>Negation\<close>

lemma notI:
  assumes "P \<Longrightarrow> False"
  shows "\<not> P"
  apply (unfold not_def)
  apply (iprover intro: impI assms)
  done

lemma False_not_True: "False \<noteq> True"
  apply (rule notI)
  apply (erule False_neq_True)
  done

lemma True_not_False: "True \<noteq> False"
  apply (rule notI)
  apply (drule sym)
  apply (erule False_neq_True)
  done

lemma notE: "\<lbrakk>\<not> P; P\<rbrakk> \<Longrightarrow> R"
  apply (unfold not_def)
  apply (erule mp [THEN FalseE])
  apply assumption
  done

lemma notI2: "(P \<Longrightarrow> \<not> Pa) \<Longrightarrow> (P \<Longrightarrow> Pa) \<Longrightarrow> \<not> P"
  by (erule notE [THEN notI]) (erule meta_mp)


subsubsection \<open>Implication\<close>

lemma impE:
  assumes "P \<longrightarrow> Q" P "Q \<Longrightarrow> R"
  shows R
by (iprover intro: assms mp)

(* Reduces Q to P \<longrightarrow> Q, allowing substitution in P. *)
lemma rev_mp: "\<lbrakk>P; P \<longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
by (iprover intro: mp)

lemma contrapos_nn:
  assumes major: "\<not> Q"
      and minor: "P \<Longrightarrow> Q"
  shows "\<not> P"
by (iprover intro: notI minor major [THEN notE])

(*not used at all, but we already have the other 3 combinations *)
lemma contrapos_pn:
  assumes major: "Q"
      and minor: "P \<Longrightarrow> \<not> Q"
  shows "\<not> P"
by (iprover intro: notI minor major notE)

lemma not_sym: "t \<noteq> s \<Longrightarrow> s \<noteq> t"
  by (erule contrapos_nn) (erule sym)

lemma eq_neq_eq_imp_neq: "\<lbrakk>x = a; a \<noteq> b; b = y\<rbrakk> \<Longrightarrow> x \<noteq> y"
  by (erule subst, erule ssubst, assumption)


subsubsection \<open>Existential quantifier\<close>

lemma exI: "P x \<Longrightarrow> \<exists>x::'a. P x"
apply (unfold Ex_def)
apply (iprover intro: allI allE impI mp)
done

lemma exE:
  assumes major: "\<exists>x::'a. P x"
      and minor: "\<And>x. P x \<Longrightarrow> Q"
  shows "Q"
apply (rule major [unfolded Ex_def, THEN spec, THEN mp])
apply (iprover intro: impI [THEN allI] minor)
done


subsubsection \<open>Conjunction\<close>

lemma conjI: "\<lbrakk>P; Q\<rbrakk> \<Longrightarrow> P \<and> Q"
apply (unfold and_def)
apply (iprover intro: impI [THEN allI] mp)
done

lemma conjunct1: "\<lbrakk>P \<and> Q\<rbrakk> \<Longrightarrow> P"
apply (unfold and_def)
apply (iprover intro: impI dest: spec mp)
done

lemma conjunct2: "\<lbrakk>P \<and> Q\<rbrakk> \<Longrightarrow> Q"
apply (unfold and_def)
apply (iprover intro: impI dest: spec mp)
done

lemma conjE:
  assumes major: "P \<and> Q"
      and minor: "\<lbrakk>P; Q\<rbrakk> \<Longrightarrow> R"
  shows R
apply (rule minor)
apply (rule major [THEN conjunct1])
apply (rule major [THEN conjunct2])
done

lemma context_conjI:
  assumes P "P \<Longrightarrow> Q" shows "P \<and> Q"
by (iprover intro: conjI assms)


subsubsection \<open>Disjunction\<close>

lemma disjI1: "P \<Longrightarrow> P \<or> Q"
apply (unfold or_def)
apply (iprover intro: allI impI mp)
done

lemma disjI2: "Q \<Longrightarrow> P \<or> Q"
apply (unfold or_def)
apply (iprover intro: allI impI mp)
done

lemma disjE:
  assumes major: "P \<or> Q"
      and minorP: "P \<Longrightarrow> R"
      and minorQ: "Q \<Longrightarrow> R"
  shows R
by (iprover intro: minorP minorQ impI
                 major [unfolded or_def, THEN spec, THEN mp, THEN mp])


subsubsection \<open>Classical logic\<close>

lemma classical:
  assumes prem: "\<not> P \<Longrightarrow> P"
  shows P
apply (rule True_or_False [THEN disjE, THEN eqTrueE])
apply assumption
apply (rule notI [THEN prem, THEN eqTrueI])
apply (erule subst)
apply assumption
done

lemmas ccontr = FalseE [THEN classical]

(*notE with premises exchanged; it discharges \<not> R so that it can be used to
  make elimination rules*)
lemma rev_notE:
  assumes premp: P
      and premnot: "\<not> R \<Longrightarrow> \<not> P"
  shows R
apply (rule ccontr)
apply (erule notE [OF premnot premp])
done

(*Double negation law*)
lemma notnotD: "\<not>\<not> P \<Longrightarrow> P"
apply (rule classical)
apply (erule notE)
apply assumption
done

lemma contrapos_pp:
  assumes p1: Q
      and p2: "\<not> P \<Longrightarrow> \<not> Q"
  shows P
by (iprover intro: classical p1 p2 notE)


subsubsection \<open>Unique existence\<close>

lemma ex1I:
  assumes "P a" "\<And>x. P x \<Longrightarrow> x = a"
  shows "\<exists>!x. P x"
by (unfold Ex1_def, iprover intro: assms exI conjI allI impI)

text\<open>Sometimes easier to use: the premises have no shared variables.  Safe!\<close>
lemma ex_ex1I:
  assumes ex_prem: "\<exists>x. P x"
      and eq: "\<And>x y. \<lbrakk>P x; P y\<rbrakk> \<Longrightarrow> x = y"
  shows "\<exists>!x. P x"
by (iprover intro: ex_prem [THEN exE] ex1I eq)

lemma ex1E:
  assumes major: "\<exists>!x. P x"
      and minor: "\<And>x. \<lbrakk>P x; \<forall>y. P y \<longrightarrow> y = x\<rbrakk> \<Longrightarrow> R"
  shows R
apply (rule major [unfolded Ex1_def, THEN exE])
apply (erule conjE)
apply (iprover intro: minor)
done

lemma ex1_implies_ex: "\<exists>!x. P x \<Longrightarrow> \<exists>x. P x"
apply (erule ex1E)
apply (rule exI)
apply assumption
done


subsubsection \<open>Classical intro rules for disjunction and existential quantifiers\<close>

lemma disjCI:
  assumes "\<not> Q \<Longrightarrow> P" shows "P \<or> Q"
apply (rule classical)
apply (iprover intro: assms disjI1 disjI2 notI elim: notE)
done

lemma excluded_middle: "\<not> P \<or> P"
by (iprover intro: disjCI)

text \<open>
  case distinction as a natural deduction rule.
  Note that @{term "\<not> P"} is the second case, not the first
\<close>
lemma case_split [case_names True False]:
  assumes prem1: "P \<Longrightarrow> Q"
      and prem2: "\<not> P \<Longrightarrow> Q"
  shows Q
apply (rule excluded_middle [THEN disjE])
apply (erule prem2)
apply (erule prem1)
done

(*Classical implies (\<longrightarrow>) elimination. *)
lemma impCE:
  assumes major: "P \<longrightarrow> Q"
      and minor: "\<not> P \<Longrightarrow> R" "Q \<Longrightarrow> R"
  shows R
apply (rule excluded_middle [of P, THEN disjE])
apply (iprover intro: minor major [THEN mp])+
done

(*This version of \<longrightarrow> elimination works on Q before P.  It works best for
  those cases in which P holds "almost everywhere".  Can't install as
  default: would break old proofs.*)
lemma impCE':
  assumes major: "P \<longrightarrow> Q"
      and minor: "Q \<Longrightarrow> R" "\<not> P \<Longrightarrow> R"
  shows R
apply (rule excluded_middle [of P, THEN disjE])
apply (iprover intro: minor major [THEN mp])+
done

(*Classical <-> elimination. *)
lemma iffCE:
  assumes major: "P = Q"
      and minor: "\<lbrakk>P; Q\<rbrakk> \<Longrightarrow> R" "\<lbrakk>\<not> P; \<not> Q\<rbrakk> \<Longrightarrow> R"
  shows R
apply (rule major [THEN iffE])
apply (iprover intro: minor elim: impCE notE)
done

lemma exCI:
  assumes "\<forall>x. \<not> P x \<Longrightarrow> P a"
  shows "\<exists>x. P x"
apply (rule ccontr)
apply (iprover intro: assms exI allI notI notE [of "\<exists>x. P x"])
done


subsubsection \<open>Intuitionistic Reasoning\<close>

lemma impE':
  assumes 1: "P \<longrightarrow> Q"
    and 2: "Q \<Longrightarrow> R"
    and 3: "P \<longrightarrow> Q \<Longrightarrow> P"
  shows R
proof -
  from 3 and 1 have P .
  with 1 have Q by (rule impE)
  with 2 show R .
qed

lemma allE':
  assumes 1: "\<forall>x. P x"
    and 2: "P x \<Longrightarrow> \<forall>x. P x \<Longrightarrow> Q"
  shows Q
proof -
  from 1 have "P x" by (rule spec)
  from this and 1 show Q by (rule 2)
qed

lemma notE':
  assumes 1: "\<not> P"
    and 2: "\<not> P \<Longrightarrow> P"
  shows R
proof -
  from 2 and 1 have P .
  with 1 show R by (rule notE)
qed

lemma TrueE: "True \<Longrightarrow> P \<Longrightarrow> P" .
lemma notFalseE: "\<not> False \<Longrightarrow> P \<Longrightarrow> P" .

lemmas [Pure.elim!] = disjE iffE FalseE conjE exE TrueE notFalseE
  and [Pure.intro!] = iffI conjI impI TrueI notI allI refl
  and [Pure.elim 2] = allE notE' impE'
  and [Pure.intro] = exI disjI2 disjI1

lemmas [trans] = trans
  and [sym] = sym not_sym
  and [Pure.elim?] = iffD1 iffD2 impE


subsubsection \<open>Atomizing meta-level connectives\<close>

axiomatization where
  eq_reflection: "x = y \<Longrightarrow> x \<equiv> y" (*admissible axiom*)

lemma atomize_all [atomize]: "(\<And>x. P x) \<equiv> Trueprop (\<forall>x. P x)"
proof
  assume "\<And>x. P x"
  then show "\<forall>x. P x" ..
next
  assume "\<forall>x. P x"
  then show "\<And>x. P x" by (rule allE)
qed

lemma atomize_imp [atomize]: "(A \<Longrightarrow> B) \<equiv> Trueprop (A \<longrightarrow> B)"
proof
  assume r: "A \<Longrightarrow> B"
  show "A \<longrightarrow> B" by (rule impI) (rule r)
next
  assume "A \<longrightarrow> B" and A
  then show B by (rule mp)
qed

lemma atomize_not: "(A \<Longrightarrow> False) \<equiv> Trueprop (\<not> A)"
proof
  assume r: "A \<Longrightarrow> False"
  show "\<not> A" by (rule notI) (rule r)
next
  assume "\<not> A" and A
  then show False by (rule notE)
qed

lemma atomize_eq [atomize, code]: "(x \<equiv> y) \<equiv> Trueprop (x = y)"
proof
  assume "x \<equiv> y"
  show "x = y" by (unfold \<open>x \<equiv> y\<close>) (rule refl)
next
  assume "x = y"
  then show "x \<equiv> y" by (rule eq_reflection)
qed

lemma atomize_conj [atomize]: "(A &&& B) \<equiv> Trueprop (A \<and> B)"
proof
  assume conj: "A &&& B"
  show "A \<and> B"
  proof (rule conjI)
    from conj show A by (rule conjunctionD1)
    from conj show B by (rule conjunctionD2)
  qed
next
  assume conj: "A \<and> B"
  show "A &&& B"
  proof -
    from conj show A ..
    from conj show B ..
  qed
qed

lemmas [symmetric, rulify] = atomize_all atomize_imp
  and [symmetric, defn] = atomize_all atomize_imp atomize_eq


subsubsection \<open>Atomizing elimination rules\<close>

lemma atomize_exL[atomize_elim]: "(\<And>x. P x \<Longrightarrow> Q) \<equiv> ((\<exists>x. P x) \<Longrightarrow> Q)"
  by rule iprover+

lemma atomize_conjL[atomize_elim]: "(A \<Longrightarrow> B \<Longrightarrow> C) \<equiv> (A \<and> B \<Longrightarrow> C)"
  by rule iprover+

lemma atomize_disjL[atomize_elim]: "((A \<Longrightarrow> C) \<Longrightarrow> (B \<Longrightarrow> C) \<Longrightarrow> C) \<equiv> ((A \<or> B \<Longrightarrow> C) \<Longrightarrow> C)"
  by rule iprover+

lemma atomize_elimL[atomize_elim]: "(\<And>B. (A \<Longrightarrow> B) \<Longrightarrow> B) \<equiv> Trueprop A" ..


subsection \<open>Package setup\<close>

ML_file "Tools/hologic.ML"


subsubsection \<open>Sledgehammer setup\<close>

text \<open>
Theorems blacklisted to Sledgehammer. These theorems typically produce clauses
that are prolific (match too many equality or membership literals) and relate to
seldom-used facts. Some duplicate other rules.
\<close>

named_theorems no_atp "theorems that should be filtered out by Sledgehammer"


subsubsection \<open>Classical Reasoner setup\<close>

lemma imp_elim: "P \<longrightarrow> Q \<Longrightarrow> (\<not> R \<Longrightarrow> P) \<Longrightarrow> (Q \<Longrightarrow> R) \<Longrightarrow> R"
  by (rule classical) iprover

lemma swap: "\<not> P \<Longrightarrow> (\<not> R \<Longrightarrow> P) \<Longrightarrow> R"
  by (rule classical) iprover

lemma thin_refl: "\<And>X. \<lbrakk>x = x; PROP W\<rbrakk> \<Longrightarrow> PROP W" .

ML \<open>
structure Hypsubst = Hypsubst
(
  val dest_eq = HOLogic.dest_eq
  val dest_Trueprop = HOLogic.dest_Trueprop
  val dest_imp = HOLogic.dest_imp
  val eq_reflection = @{thm eq_reflection}
  val rev_eq_reflection = @{thm meta_eq_to_obj_eq}
  val imp_intr = @{thm impI}
  val rev_mp = @{thm rev_mp}
  val subst = @{thm subst}
  val sym = @{thm sym}
  val thin_refl = @{thm thin_refl};
);
open Hypsubst;

structure Classical = Classical
(
  val imp_elim = @{thm imp_elim}
  val not_elim = @{thm notE}
  val swap = @{thm swap}
  val classical = @{thm classical}
  val sizef = Drule.size_of_thm
  val hyp_subst_tacs = [Hypsubst.hyp_subst_tac]
);

structure Basic_Classical: BASIC_CLASSICAL = Classical;
open Basic_Classical;
\<close>

setup \<open>
  (*prevent substitution on bool*)
  let
    fun non_bool_eq (@{const_name HOL.eq}, Type (_, [T, _])) = T <> @{typ bool}
      | non_bool_eq _ = false;
    fun hyp_subst_tac' ctxt =
      SUBGOAL (fn (goal, i) =>
        if Term.exists_Const non_bool_eq goal
        then Hypsubst.hyp_subst_tac ctxt i
        else no_tac);
  in
    Context_Rules.addSWrapper (fn ctxt => fn tac => hyp_subst_tac' ctxt ORELSE' tac)
  end
\<close>

declare iffI [intro!]
  and notI [intro!]
  and impI [intro!]
  and disjCI [intro!]
  and conjI [intro!]
  and TrueI [intro!]
  and refl [intro!]

declare iffCE [elim!]
  and FalseE [elim!]
  and impCE [elim!]
  and disjE [elim!]
  and conjE [elim!]

declare ex_ex1I [intro!]
  and allI [intro!]
  and exI [intro]

declare exE [elim!]
  allE [elim]

ML \<open>val HOL_cs = claset_of @{context}\<close>

lemma contrapos_np: "\<not> Q \<Longrightarrow> (\<not> P \<Longrightarrow> Q) \<Longrightarrow> P"
  apply (erule swap)
  apply (erule (1) meta_mp)
  done

declare ex_ex1I [rule del, intro! 2]
  and ex1I [intro]

declare ext [intro]

lemmas [intro?] = ext
  and [elim?] = ex1_implies_ex

(*Better then ex1E for classical reasoner: needs no quantifier duplication!*)
lemma alt_ex1E [elim!]:
  assumes major: "\<exists>!x. P x"
      and prem: "\<And>x. \<lbrakk> P x; \<forall>y y'. P y \<and> P y' \<longrightarrow> y = y' \<rbrakk> \<Longrightarrow> R"
  shows R
apply (rule ex1E [OF major])
apply (rule prem)
apply assumption
apply (rule allI)+
apply (tactic \<open>eresolve_tac @{context} [Classical.dup_elim @{context} @{thm allE}] 1\<close>)
apply iprover
done

ML \<open>
  structure Blast = Blast
  (
    structure Classical = Classical
    val Trueprop_const = dest_Const @{const Trueprop}
    val equality_name = @{const_name HOL.eq}
    val not_name = @{const_name Not}
    val notE = @{thm notE}
    val ccontr = @{thm ccontr}
    val hyp_subst_tac = Hypsubst.blast_hyp_subst_tac
  );
  val blast_tac = Blast.blast_tac;
\<close>


subsubsection \<open>THE: definite description operator\<close>

lemma the_equality [intro]:
  assumes "P a"
      and "\<And>x. P x \<Longrightarrow> x = a"
  shows "(THE x. P x) = a"
  by (blast intro: assms trans [OF arg_cong [where f=The] the_eq_trivial])

lemma theI:
  assumes "P a" and "\<And>x. P x \<Longrightarrow> x = a"
  shows "P (THE x. P x)"
by (iprover intro: assms the_equality [THEN ssubst])

lemma theI': "\<exists>!x. P x \<Longrightarrow> P (THE x. P x)"
  by (blast intro: theI)

(*Easier to apply than theI: only one occurrence of P*)
lemma theI2:
  assumes "P a" "\<And>x. P x \<Longrightarrow> x = a" "\<And>x. P x \<Longrightarrow> Q x"
  shows "Q (THE x. P x)"
by (iprover intro: assms theI)

lemma the1I2: assumes "\<exists>!x. P x" "\<And>x. P x \<Longrightarrow> Q x" shows "Q (THE x. P x)"
by(iprover intro:assms(2) theI2[where P=P and Q=Q] ex1E[OF assms(1)]
           elim:allE impE)

lemma the1_equality [elim?]: "\<lbrakk>\<exists>!x. P x; P a\<rbrakk> \<Longrightarrow> (THE x. P x) = a"
  by blast

lemma the_sym_eq_trivial: "(THE y. x = y) = x"
  by blast


subsubsection \<open>Simplifier\<close>

lemma eta_contract_eq: "(\<lambda>s. f s) = f" ..

lemma simp_thms:
  shows not_not: "(\<not> \<not> P) = P"
  and Not_eq_iff: "((\<not> P) = (\<not> Q)) = (P = Q)"
  and
    "(P \<noteq> Q) = (P = (\<not> Q))"
    "(P \<or> \<not>P) = True"    "(\<not> P \<or> P) = True"
    "(x = x) = True"
  and not_True_eq_False [code]: "(\<not> True) = False"
  and not_False_eq_True [code]: "(\<not> False) = True"
  and
    "(\<not> P) \<noteq> P"  "P \<noteq> (\<not> P)"
    "(True = P) = P"
  and eq_True: "(P = True) = P"
  and "(False = P) = (\<not> P)"
  and eq_False: "(P = False) = (\<not> P)"
  and
    "(True \<longrightarrow> P) = P"  "(False \<longrightarrow> P) = True"
    "(P \<longrightarrow> True) = True"  "(P \<longrightarrow> P) = True"
    "(P \<longrightarrow> False) = (\<not> P)"  "(P \<longrightarrow> \<not> P) = (\<not> P)"
    "(P \<and> True) = P"  "(True \<and> P) = P"
    "(P \<and> False) = False"  "(False \<and> P) = False"
    "(P \<and> P) = P"  "(P \<and> (P \<and> Q)) = (P \<and> Q)"
    "(P \<and> \<not> P) = False"    "(\<not> P \<and> P) = False"
    "(P \<or> True) = True"  "(True \<or> P) = True"
    "(P \<or> False) = P"  "(False \<or> P) = P"
    "(P \<or> P) = P"  "(P \<or> (P \<or> Q)) = (P \<or> Q)" and
    "(\<forall>x. P) = P"  "(\<exists>x. P) = P"  "\<exists>x. x = t"  "\<exists>x. t = x"
  and
    "\<And>P. (\<exists>x. x = t \<and> P x) = P t"
    "\<And>P. (\<exists>x. t = x \<and> P x) = P t"
    "\<And>P. (\<forall>x. x = t \<longrightarrow> P x) = P t"
    "\<And>P. (\<forall>x. t = x \<longrightarrow> P x) = P t"
  by (blast, blast, blast, blast, blast, iprover+)

lemma disj_absorb: "(A \<or> A) = A"
  by blast

lemma disj_left_absorb: "(A \<or> (A \<or> B)) = (A \<or> B)"
  by blast

lemma conj_absorb: "(A \<and> A) = A"
  by blast

lemma conj_left_absorb: "(A \<and> (A \<and> B)) = (A \<and> B)"
  by blast

lemma eq_ac:
  shows eq_commute: "a = b \<longleftrightarrow> b = a"
    and iff_left_commute: "(P \<longleftrightarrow> (Q \<longleftrightarrow> R)) \<longleftrightarrow> (Q \<longleftrightarrow> (P \<longleftrightarrow> R))"
    and iff_assoc: "((P \<longleftrightarrow> Q) \<longleftrightarrow> R) \<longleftrightarrow> (P \<longleftrightarrow> (Q \<longleftrightarrow> R))" by (iprover, blast+)
lemma neq_commute: "a \<noteq> b \<longleftrightarrow> b \<noteq> a" by iprover

lemma conj_comms:
  shows conj_commute: "(P \<and> Q) = (Q \<and> P)"
    and conj_left_commute: "(P \<and> (Q \<and> R)) = (Q \<and> (P \<and> R))" by iprover+
lemma conj_assoc: "((P \<and> Q) \<and> R) = (P \<and> (Q \<and> R))" by iprover

lemmas conj_ac = conj_commute conj_left_commute conj_assoc

lemma disj_comms:
  shows disj_commute: "(P \<or> Q) = (Q \<or> P)"
    and disj_left_commute: "(P \<or> (Q \<or> R)) = (Q \<or> (P \<or> R))" by iprover+
lemma disj_assoc: "((P \<or> Q) \<or> R) = (P \<or> (Q \<or> R))" by iprover

lemmas disj_ac = disj_commute disj_left_commute disj_assoc

lemma conj_disj_distribL: "(P \<and> (Q \<or> R)) = (P \<and> Q \<or> P \<and> R)" by iprover
lemma conj_disj_distribR: "((P \<or> Q) \<and> R) = (P \<and> R \<or> Q \<and> R)" by iprover

lemma disj_conj_distribL: "(P \<or> (Q \<and> R)) = ((P \<or> Q) \<and> (P \<or> R))" by iprover
lemma disj_conj_distribR: "((P \<and> Q) \<or> R) = ((P \<or> R) \<and> (Q \<or> R))" by iprover

lemma imp_conjR: "(P \<longrightarrow> (Q \<and> R)) = ((P \<longrightarrow> Q) \<and> (P \<longrightarrow> R))" by iprover
lemma imp_conjL: "((P \<and> Q) \<longrightarrow> R) = (P \<longrightarrow> (Q \<longrightarrow> R))" by iprover
lemma imp_disjL: "((P \<or> Q) \<longrightarrow> R) = ((P \<longrightarrow> R) \<and> (Q \<longrightarrow> R))" by iprover

text \<open>These two are specialized, but @{text imp_disj_not1} is useful in @{text "Auth/Yahalom"}.\<close>
lemma imp_disj_not1: "(P \<longrightarrow> Q \<or> R) = (\<not> Q \<longrightarrow> P \<longrightarrow> R)" by blast
lemma imp_disj_not2: "(P \<longrightarrow> Q \<or> R) = (\<not> R \<longrightarrow> P \<longrightarrow> Q)" by blast

lemma imp_disj1: "((P \<longrightarrow> Q) \<or> R) = (P \<longrightarrow> Q \<or> R)" by blast
lemma imp_disj2: "(Q \<or> (P \<longrightarrow> R)) = (P \<longrightarrow> Q \<or> R)" by blast

lemma imp_cong: "(P = P') \<Longrightarrow> (P' \<Longrightarrow> (Q = Q')) \<Longrightarrow> ((P \<longrightarrow> Q) = (P' \<longrightarrow> Q'))"
  by iprover

lemma de_Morgan_disj: "(\<not> (P \<or> Q)) = (\<not> P \<and> \<not> Q)" by iprover
lemma de_Morgan_conj: "(\<not> (P \<and> Q)) = (\<not> P \<or> \<not> Q)" by blast
lemma not_imp: "(\<not> (P \<longrightarrow> Q)) = (P \<and> \<not> Q)" by blast
lemma not_iff: "(P \<noteq> Q) = (P = (\<not> Q))" by blast
lemma disj_not1: "(\<not> P \<or> Q) = (P \<longrightarrow> Q)" by blast
lemma disj_not2: "(P \<or> \<not> Q) = (Q \<longrightarrow> P)"  -- \<open>changes orientation :-(\<close>
  by blast
lemma imp_conv_disj: "(P \<longrightarrow> Q) = ((\<not> P) \<or> Q)" by blast

lemma iff_conv_conj_imp: "(P = Q) = ((P \<longrightarrow> Q) \<and> (Q \<longrightarrow> P))" by iprover


lemma cases_simp: "((P \<longrightarrow> Q) \<and> (\<not> P \<longrightarrow> Q)) = Q"
  -- \<open>Avoids duplication of subgoals after @{text split_if}, when the true and false\<close>
  -- \<open>cases boil down to the same thing.\<close>
  by blast

lemma not_all: "(\<not> (\<forall>x. P x)) = (\<exists>x. \<not> P x)" by blast
lemma imp_all: "((\<forall>x. P x) \<longrightarrow> Q) = (\<exists>x. P x \<longrightarrow> Q)" by blast
lemma not_ex: "(\<not> (\<exists>x. P x)) = (\<forall>x. \<not> P x)" by iprover
lemma imp_ex: "((\<exists>x. P x) \<longrightarrow> Q) = (\<forall>x. P x \<longrightarrow> Q)" by iprover
lemma all_not_ex: "(\<forall>x. P x) = (\<not> (\<exists>x. \<not> P x ))" by blast

declare All_def [no_atp]

lemma ex_disj_distrib: "(\<exists>x. P x \<or> Q x) = ((\<exists>x. P x) \<or> (\<exists>x. Q x))" by iprover
lemma all_conj_distrib: "(\<forall>x. P x \<and> Q x) = ((\<forall>x. P x) \<and> (\<forall>x. Q x))" by iprover

text \<open>
  \medskip The @{text "\<and>"} congruence rule: not included by default!
  May slow rewrite proofs down by as much as 50\%\<close>

lemma conj_cong:
    "(P = P') \<Longrightarrow> (P' \<Longrightarrow> (Q = Q')) \<Longrightarrow> ((P \<and> Q) = (P' \<and> Q'))"
  by iprover

lemma rev_conj_cong:
    "(Q = Q') \<Longrightarrow> (Q' \<Longrightarrow> (P = P')) \<Longrightarrow> ((P \<and> Q) = (P' \<and> Q'))"
  by iprover

text \<open>The @{text "|"} congruence rule: not included by default!\<close>

lemma disj_cong:
    "(P = P') \<Longrightarrow> (\<not> P' \<Longrightarrow> (Q = Q')) \<Longrightarrow> ((P \<or> Q) = (P' \<or> Q'))"
  by blast


text \<open>\medskip if-then-else rules\<close>

lemma if_True [code]: "(if True then x else y) = x"
  by (unfold If_def) blast

lemma if_False [code]: "(if False then x else y) = y"
  by (unfold If_def) blast

lemma if_P: "P \<Longrightarrow> (if P then x else y) = x"
  by (unfold If_def) blast

lemma if_not_P: "\<not> P \<Longrightarrow> (if P then x else y) = y"
  by (unfold If_def) blast

lemma split_if: "P (if Q then x else y) = ((Q \<longrightarrow> P x) \<and> (\<not> Q \<longrightarrow> P y))"
  apply (rule case_split [of Q])
   apply (simplesubst if_P)
    prefer 3 apply (simplesubst if_not_P, blast+)
  done

lemma split_if_asm: "P (if Q then x else y) = (\<not> ((Q \<and> \<not> P x) \<or> (\<not> Q \<and> \<not> P y)))"
by (simplesubst split_if, blast)

lemmas if_splits [no_atp] = split_if split_if_asm

lemma if_cancel: "(if c then x else x) = x"
by (simplesubst split_if, blast)

lemma if_eq_cancel: "(if x = y then y else x) = x"
by (simplesubst split_if, blast)

lemma if_bool_eq_conj: "(if P then Q else R) = ((P \<longrightarrow> Q) \<and> (\<not> P \<longrightarrow> R))"
  -- \<open>This form is useful for expanding @{text "if"}s on the RIGHT of the @{text "\<Longrightarrow>"} symbol.\<close>
  by (rule split_if)

lemma if_bool_eq_disj: "(if P then Q else R) = ((P \<and> Q) \<or> (\<not> P \<and> R))"
  -- \<open>And this form is useful for expanding @{text "if"}s on the LEFT.\<close>
  by (simplesubst split_if) blast

lemma Eq_TrueI: "P \<Longrightarrow> P \<equiv> True" by (unfold atomize_eq) iprover
lemma Eq_FalseI: "\<not> P \<Longrightarrow> P \<equiv> False" by (unfold atomize_eq) iprover

text \<open>\medskip let rules for simproc\<close>

lemma Let_folded: "f x \<equiv> g x \<Longrightarrow> Let x f \<equiv> Let x g"
  by (unfold Let_def)

lemma Let_unfold: "f x \<equiv> g \<Longrightarrow> Let x f \<equiv> g"
  by (unfold Let_def)

text \<open>
  The following copy of the implication operator is useful for
  fine-tuning congruence rules.  It instructs the simplifier to simplify
  its premise.
\<close>

definition simp_implies :: "[prop, prop] \<Rightarrow> prop"  (infixr "=simp=>" 1) where
  "simp_implies \<equiv> op \<Longrightarrow>"

lemma simp_impliesI:
  assumes PQ: "(PROP P \<Longrightarrow> PROP Q)"
  shows "PROP P =simp=> PROP Q"
  apply (unfold simp_implies_def)
  apply (rule PQ)
  apply assumption
  done

lemma simp_impliesE:
  assumes PQ: "PROP P =simp=> PROP Q"
  and P: "PROP P"
  and QR: "PROP Q \<Longrightarrow> PROP R"
  shows "PROP R"
  apply (rule QR)
  apply (rule PQ [unfolded simp_implies_def])
  apply (rule P)
  done

lemma simp_implies_cong:
  assumes PP' :"PROP P \<equiv> PROP P'"
  and P'QQ': "PROP P' \<Longrightarrow> (PROP Q \<equiv> PROP Q')"
  shows "(PROP P =simp=> PROP Q) \<equiv> (PROP P' =simp=> PROP Q')"
proof (unfold simp_implies_def, rule equal_intr_rule)
  assume PQ: "PROP P \<Longrightarrow> PROP Q"
  and P': "PROP P'"
  from PP' [symmetric] and P' have "PROP P"
    by (rule equal_elim_rule1)
  then have "PROP Q" by (rule PQ)
  with P'QQ' [OF P'] show "PROP Q'" by (rule equal_elim_rule1)
next
  assume P'Q': "PROP P' \<Longrightarrow> PROP Q'"
  and P: "PROP P"
  from PP' and P have P': "PROP P'" by (rule equal_elim_rule1)
  then have "PROP Q'" by (rule P'Q')
  with P'QQ' [OF P', symmetric] show "PROP Q"
    by (rule equal_elim_rule1)
qed

lemma uncurry:
  assumes "P \<longrightarrow> Q \<longrightarrow> R"
  shows "P \<and> Q \<longrightarrow> R"
  using assms by blast

lemma iff_allI:
  assumes "\<And>x. P x = Q x"
  shows "(\<forall>x. P x) = (\<forall>x. Q x)"
  using assms by blast

lemma iff_exI:
  assumes "\<And>x. P x = Q x"
  shows "(\<exists>x. P x) = (\<exists>x. Q x)"
  using assms by blast

lemma all_comm:
  "(\<forall>x y. P x y) = (\<forall>y x. P x y)"
  by blast

lemma ex_comm:
  "(\<exists>x y. P x y) = (\<exists>y x. P x y)"
  by blast

ML_file "Tools/simpdata.ML"
ML \<open>open Simpdata\<close>

setup \<open>
  map_theory_simpset (put_simpset HOL_basic_ss) #>
  Simplifier.method_setup Splitter.split_modifiers
\<close>

simproc_setup defined_Ex ("\<exists>x. P x") = \<open>fn _ => Quantifier1.rearrange_ex\<close>
simproc_setup defined_All ("\<forall>x. P x") = \<open>fn _ => Quantifier1.rearrange_all\<close>

text \<open>Simproc for proving @{text "(y = x) \<equiv> False"} from premise @{text "\<not> (x = y)"}:\<close>

simproc_setup neq ("x = y") = \<open>fn _ =>
let
  val neq_to_EQ_False = @{thm not_sym} RS @{thm Eq_FalseI};
  fun is_neq eq lhs rhs thm =
    (case Thm.prop_of thm of
      _ $ (Not $ (eq' $ l' $ r')) =>
        Not = HOLogic.Not andalso eq' = eq andalso
        r' aconv lhs andalso l' aconv rhs
    | _ => false);
  fun proc ss ct =
    (case Thm.term_of ct of
      eq $ lhs $ rhs =>
        (case find_first (is_neq eq lhs rhs) (Simplifier.prems_of ss) of
          SOME thm => SOME (thm RS neq_to_EQ_False)
        | NONE => NONE)
     | _ => NONE);
in proc end;
\<close>

simproc_setup let_simp ("Let x f") = \<open>
let
  fun count_loose (Bound i) k = if i >= k then 1 else 0
    | count_loose (s $ t) k = count_loose s k + count_loose t k
    | count_loose (Abs (_, _, t)) k = count_loose  t (k + 1)
    | count_loose _ _ = 0;
  fun is_trivial_let (Const (@{const_name Let}, _) $ x $ t) =
    (case t of
      Abs (_, _, t') => count_loose t' 0 <= 1
    | _ => true);
in
  fn _ => fn ctxt => fn ct =>
    if is_trivial_let (Thm.term_of ct)
    then SOME @{thm Let_def} (*no or one ocurrence of bound variable*)
    else
      let (*Norbert Schirmer's case*)
        val t = Thm.term_of ct;
        val ([t'], ctxt') = Variable.import_terms false [t] ctxt;
      in
        Option.map (hd o Variable.export ctxt' ctxt o single)
          (case t' of Const (@{const_name Let},_) $ x $ f => (* x and f are already in normal form *)
            if is_Free x orelse is_Bound x orelse is_Const x
            then SOME @{thm Let_def}
            else
              let
                val n = case f of (Abs (x, _, _)) => x | _ => "x";
                val cx = Thm.cterm_of ctxt x;
                val xT = Thm.typ_of_cterm cx;
                val cf = Thm.cterm_of ctxt f;
                val fx_g = Simplifier.rewrite ctxt (Thm.apply cf cx);
                val (_ $ _ $ g) = Thm.prop_of fx_g;
                val g' = abstract_over (x, g);
                val abs_g'= Abs (n, xT, g');
              in
                if g aconv g' then
                  let
                    val rl =
                      infer_instantiate ctxt [(("f", 0), cf), (("x", 0), cx)] @{thm Let_unfold};
                  in SOME (rl OF [fx_g]) end
                else if (Envir.beta_eta_contract f) aconv (Envir.beta_eta_contract abs_g')
                then NONE (*avoid identity conversion*)
                else
                  let
                    val g'x = abs_g' $ x;
                    val g_g'x = Thm.symmetric (Thm.beta_conversion false (Thm.cterm_of ctxt g'x));
                    val rl =
                      @{thm Let_folded} |> infer_instantiate ctxt
                        [(("f", 0), Thm.cterm_of ctxt f),
                         (("x", 0), cx),
                         (("g", 0), Thm.cterm_of ctxt abs_g')];
                  in SOME (rl OF [Thm.transitive fx_g g_g'x]) end
              end
          | _ => NONE)
      end
end\<close>

lemma True_implies_equals: "(True \<Longrightarrow> PROP P) \<equiv> PROP P"
proof
  assume "True \<Longrightarrow> PROP P"
  from this [OF TrueI] show "PROP P" .
next
  assume "PROP P"
  then show "PROP P" .
qed

lemma implies_True_equals: "(PROP P \<Longrightarrow> True) \<equiv> Trueprop True"
  by standard (intro TrueI)

lemma False_implies_equals: "(False \<Longrightarrow> P) \<equiv> Trueprop True"
  by standard simp_all

(* This is not made a simp rule because it does not improve any proofs
   but slows some AFP entries down by 5% (cpu time). May 2015 *)
lemma implies_False_swap: "NO_MATCH (Trueprop False) P \<Longrightarrow>
  (False \<Longrightarrow> PROP P \<Longrightarrow> PROP Q) \<equiv> (PROP P \<Longrightarrow> False \<Longrightarrow> PROP Q)"
by(rule swap_prems_eq)

lemma ex_simps:
  "\<And>P Q. (\<exists>x. P x \<and> Q)   = ((\<exists>x. P x) \<and> Q)"
  "\<And>P Q. (\<exists>x. P \<and> Q x)   = (P \<and> (\<exists>x. Q x))"
  "\<And>P Q. (\<exists>x. P x \<or> Q)   = ((\<exists>x. P x) \<or> Q)"
  "\<And>P Q. (\<exists>x. P \<or> Q x)   = (P \<or> (\<exists>x. Q x))"
  "\<And>P Q. (\<exists>x. P x \<longrightarrow> Q) = ((\<forall>x. P x) \<longrightarrow> Q)"
  "\<And>P Q. (\<exists>x. P \<longrightarrow> Q x) = (P \<longrightarrow> (\<exists>x. Q x))"
  -- \<open>Miniscoping: pushing in existential quantifiers.\<close>
  by (iprover | blast)+

lemma all_simps:
  "\<And>P Q. (\<forall>x. P x \<and> Q)   = ((\<forall>x. P x) \<and> Q)"
  "\<And>P Q. (\<forall>x. P \<and> Q x)   = (P \<and> (\<forall>x. Q x))"
  "\<And>P Q. (\<forall>x. P x \<or> Q)   = ((\<forall>x. P x) \<or> Q)"
  "\<And>P Q. (\<forall>x. P \<or> Q x)   = (P \<or> (\<forall>x. Q x))"
  "\<And>P Q. (\<forall>x. P x \<longrightarrow> Q) = ((\<exists>x. P x) \<longrightarrow> Q)"
  "\<And>P Q. (\<forall>x. P \<longrightarrow> Q x) = (P \<longrightarrow> (\<forall>x. Q x))"
  -- \<open>Miniscoping: pushing in universal quantifiers.\<close>
  by (iprover | blast)+

lemmas [simp] =
  triv_forall_equality (*prunes params*)
  True_implies_equals implies_True_equals (*prune True in asms*)
  False_implies_equals (*prune False in asms*)
  if_True
  if_False
  if_cancel
  if_eq_cancel
  imp_disjL
  (*In general it seems wrong to add distributive laws by default: they
    might cause exponential blow-up.  But imp_disjL has been in for a while
    and cannot be removed without affecting existing proofs.  Moreover,
    rewriting by "(P \<or> Q \<longrightarrow> R) = ((P \<longrightarrow> R) \<and> (Q \<longrightarrow> R))" might be justified on the
    grounds that it allows simplification of R in the two cases.*)
  conj_assoc
  disj_assoc
  de_Morgan_conj
  de_Morgan_disj
  imp_disj1
  imp_disj2
  not_imp
  disj_not1
  not_all
  not_ex
  cases_simp
  the_eq_trivial
  the_sym_eq_trivial
  ex_simps
  all_simps
  simp_thms

lemmas [cong] = imp_cong simp_implies_cong
lemmas [split] = split_if

ML \<open>val HOL_ss = simpset_of @{context}\<close>

text \<open>Simplifies @{term x} assuming @{prop c} and @{term y} assuming @{prop "\<not> c"}\<close>
lemma if_cong:
  assumes "b = c"
      and "c \<Longrightarrow> x = u"
      and "\<not> c \<Longrightarrow> y = v"
  shows "(if b then x else y) = (if c then u else v)"
  using assms by simp

text \<open>Prevents simplification of x and y:
  faster and allows the execution of functional programs.\<close>
lemma if_weak_cong [cong]:
  assumes "b = c"
  shows "(if b then x else y) = (if c then x else y)"
  using assms by (rule arg_cong)

text \<open>Prevents simplification of t: much faster\<close>
lemma let_weak_cong:
  assumes "a = b"
  shows "(let x = a in t x) = (let x = b in t x)"
  using assms by (rule arg_cong)

text \<open>To tidy up the result of a simproc.  Only the RHS will be simplified.\<close>
lemma eq_cong2:
  assumes "u = u'"
  shows "(t \<equiv> u) \<equiv> (t \<equiv> u')"
  using assms by simp

lemma if_distrib:
  "f (if c then x else y) = (if c then f x else f y)"
  by simp

text\<open>As a simplification rule, it replaces all function equalities by
  first-order equalities.\<close>
lemma fun_eq_iff: "f = g \<longleftrightarrow> (\<forall>x. f x = g x)"
  by auto


subsubsection \<open>Generic cases and induction\<close>

text \<open>Rule projections:\<close>
ML \<open>
structure Project_Rule = Project_Rule
(
  val conjunct1 = @{thm conjunct1}
  val conjunct2 = @{thm conjunct2}
  val mp = @{thm mp}
);
\<close>

context
begin

qualified definition "induct_forall P \<equiv> \<forall>x. P x"
qualified definition "induct_implies A B \<equiv> A \<longrightarrow> B"
qualified definition "induct_equal x y \<equiv> x = y"
qualified definition "induct_conj A B \<equiv> A \<and> B"
qualified definition "induct_true \<equiv> True"
qualified definition "induct_false \<equiv> False"

lemma induct_forall_eq: "(\<And>x. P x) \<equiv> Trueprop (induct_forall (\<lambda>x. P x))"
  by (unfold atomize_all induct_forall_def)

lemma induct_implies_eq: "(A \<Longrightarrow> B) \<equiv> Trueprop (induct_implies A B)"
  by (unfold atomize_imp induct_implies_def)

lemma induct_equal_eq: "(x \<equiv> y) \<equiv> Trueprop (induct_equal x y)"
  by (unfold atomize_eq induct_equal_def)

lemma induct_conj_eq: "(A &&& B) \<equiv> Trueprop (induct_conj A B)"
  by (unfold atomize_conj induct_conj_def)

lemmas induct_atomize' = induct_forall_eq induct_implies_eq induct_conj_eq
lemmas induct_atomize = induct_atomize' induct_equal_eq
lemmas induct_rulify' [symmetric] = induct_atomize'
lemmas induct_rulify [symmetric] = induct_atomize
lemmas induct_rulify_fallback =
  induct_forall_def induct_implies_def induct_equal_def induct_conj_def
  induct_true_def induct_false_def

lemma induct_forall_conj: "induct_forall (\<lambda>x. induct_conj (A x) (B x)) =
    induct_conj (induct_forall A) (induct_forall B)"
  by (unfold induct_forall_def induct_conj_def) iprover

lemma induct_implies_conj: "induct_implies C (induct_conj A B) =
    induct_conj (induct_implies C A) (induct_implies C B)"
  by (unfold induct_implies_def induct_conj_def) iprover

lemma induct_conj_curry: "(induct_conj A B \<Longrightarrow> PROP C) \<equiv> (A \<Longrightarrow> B \<Longrightarrow> PROP C)"
proof
  assume r: "induct_conj A B \<Longrightarrow> PROP C"
  assume ab: A B
  show "PROP C" by (rule r) (simp add: induct_conj_def ab)
next
  assume r: "A \<Longrightarrow> B \<Longrightarrow> PROP C"
  assume ab: "induct_conj A B"
  show "PROP C" by (rule r) (simp_all add: ab [unfolded induct_conj_def])
qed

lemmas induct_conj = induct_forall_conj induct_implies_conj induct_conj_curry

lemma induct_trueI: "induct_true"
  by (simp add: induct_true_def)

text \<open>Method setup.\<close>

ML_file "~~/src/Tools/induct.ML"
ML \<open>
structure Induct = Induct
(
  val cases_default = @{thm case_split}
  val atomize = @{thms induct_atomize}
  val rulify = @{thms induct_rulify'}
  val rulify_fallback = @{thms induct_rulify_fallback}
  val equal_def = @{thm induct_equal_def}
  fun dest_def (Const (@{const_name induct_equal}, _) $ t $ u) = SOME (t, u)
    | dest_def _ = NONE
  fun trivial_tac ctxt = match_tac ctxt @{thms induct_trueI}
)
\<close>

ML_file "~~/src/Tools/induction.ML"

declaration \<open>
  fn _ => Induct.map_simpset (fn ss => ss
    addsimprocs
      [Simplifier.make_simproc @{context} "swap_induct_false"
        {lhss = [@{term "induct_false \<Longrightarrow> PROP P \<Longrightarrow> PROP Q"}],
         proc = fn _ => fn _ => fn ct =>
          (case Thm.term_of ct of
            _ $ (P as _ $ @{const induct_false}) $ (_ $ Q $ _) =>
              if P <> Q then SOME Drule.swap_prems_eq else NONE
          | _ => NONE),
         identifier = []},
       Simplifier.make_simproc @{context} "induct_equal_conj_curry"
        {lhss = [@{term "induct_conj P Q \<Longrightarrow> PROP R"}],
         proc = fn _ => fn _ => fn ct =>
          (case Thm.term_of ct of
            _ $ (_ $ P) $ _ =>
              let
                fun is_conj (@{const induct_conj} $ P $ Q) =
                      is_conj P andalso is_conj Q
                  | is_conj (Const (@{const_name induct_equal}, _) $ _ $ _) = true
                  | is_conj @{const induct_true} = true
                  | is_conj @{const induct_false} = true
                  | is_conj _ = false
              in if is_conj P then SOME @{thm induct_conj_curry} else NONE end
            | _ => NONE),
          identifier = []}]
    |> Simplifier.set_mksimps (fn ctxt =>
        Simpdata.mksimps Simpdata.mksimps_pairs ctxt #>
        map (rewrite_rule ctxt (map Thm.symmetric @{thms induct_rulify_fallback}))))
\<close>

text \<open>Pre-simplification of induction and cases rules\<close>

lemma [induct_simp]: "(\<And>x. induct_equal x t \<Longrightarrow> PROP P x) \<equiv> PROP P t"
  unfolding induct_equal_def
proof
  assume r: "\<And>x. x = t \<Longrightarrow> PROP P x"
  show "PROP P t" by (rule r [OF refl])
next
  fix x
  assume "PROP P t" "x = t"
  then show "PROP P x" by simp
qed

lemma [induct_simp]: "(\<And>x. induct_equal t x \<Longrightarrow> PROP P x) \<equiv> PROP P t"
  unfolding induct_equal_def
proof
  assume r: "\<And>x. t = x \<Longrightarrow> PROP P x"
  show "PROP P t" by (rule r [OF refl])
next
  fix x
  assume "PROP P t" "t = x"
  then show "PROP P x" by simp
qed

lemma [induct_simp]: "(induct_false \<Longrightarrow> P) \<equiv> Trueprop induct_true"
  unfolding induct_false_def induct_true_def
  by (iprover intro: equal_intr_rule)

lemma [induct_simp]: "(induct_true \<Longrightarrow> PROP P) \<equiv> PROP P"
  unfolding induct_true_def
proof
  assume "True \<Longrightarrow> PROP P"
  then show "PROP P" using TrueI .
next
  assume "PROP P"
  then show "PROP P" .
qed

lemma [induct_simp]: "(PROP P \<Longrightarrow> induct_true) \<equiv> Trueprop induct_true"
  unfolding induct_true_def
  by (iprover intro: equal_intr_rule)

lemma [induct_simp]: "(\<And>x. induct_true) \<equiv> Trueprop induct_true"
  unfolding induct_true_def
  by (iprover intro: equal_intr_rule)

lemma [induct_simp]: "induct_implies induct_true P \<equiv> P"
  by (simp add: induct_implies_def induct_true_def)

lemma [induct_simp]: "x = x \<longleftrightarrow> True"
  by (rule simp_thms)

end

ML_file "~~/src/Tools/induct_tacs.ML"


subsubsection \<open>Coherent logic\<close>

ML_file "~~/src/Tools/coherent.ML"
ML \<open>
structure Coherent = Coherent
(
  val atomize_elimL = @{thm atomize_elimL};
  val atomize_exL = @{thm atomize_exL};
  val atomize_conjL = @{thm atomize_conjL};
  val atomize_disjL = @{thm atomize_disjL};
  val operator_names = [@{const_name HOL.disj}, @{const_name HOL.conj}, @{const_name Ex}];
);
\<close>


subsubsection \<open>Reorienting equalities\<close>

ML \<open>
signature REORIENT_PROC =
sig
  val add : (term -> bool) -> theory -> theory
  val proc : morphism -> Proof.context -> cterm -> thm option
end;

structure Reorient_Proc : REORIENT_PROC =
struct
  structure Data = Theory_Data
  (
    type T = ((term -> bool) * stamp) list;
    val empty = [];
    val extend = I;
    fun merge data : T = Library.merge (eq_snd op =) data;
  );
  fun add m = Data.map (cons (m, stamp ()));
  fun matches thy t = exists (fn (m, _) => m t) (Data.get thy);

  val meta_reorient = @{thm eq_commute [THEN eq_reflection]};
  fun proc phi ctxt ct =
    let
      val thy = Proof_Context.theory_of ctxt;
    in
      case Thm.term_of ct of
        (_ $ t $ u) => if matches thy u then NONE else SOME meta_reorient
      | _ => NONE
    end;
end;
\<close>


subsection \<open>Other simple lemmas and lemma duplicates\<close>

lemma ex1_eq [iff]: "\<exists>!x. x = t" "\<exists>!x. t = x"
  by blast+

lemma choice_eq: "(\<forall>x. \<exists>!y. P x y) = (\<exists>!f. \<forall>x. P x (f x))"
  apply (rule iffI)
  apply (rule_tac a = "\<lambda>x. THE y. P x y" in ex1I)
  apply (fast dest!: theI')
  apply (fast intro: the1_equality [symmetric])
  apply (erule ex1E)
  apply (rule allI)
  apply (rule ex1I)
  apply (erule spec)
  apply (erule_tac x = "\<lambda>z. if z = x then y else f z" in allE)
  apply (erule impE)
  apply (rule allI)
  apply (case_tac "xa = x")
  apply (drule_tac [3] x = x in fun_cong, simp_all)
  done

lemmas eq_sym_conv = eq_commute

lemma nnf_simps:
  "(\<not>(P \<and> Q)) = (\<not> P \<or> \<not> Q)" "(\<not> (P \<or> Q)) = (\<not> P \<and> \<not>Q)" "(P \<longrightarrow> Q) = (\<not>P \<or> Q)"
  "(P = Q) = ((P \<and> Q) \<or> (\<not>P \<and> \<not> Q))" "(\<not>(P = Q)) = ((P \<and> \<not> Q) \<or> (\<not>P \<and> Q))"
  "(\<not> \<not>(P)) = P"
by blast+

subsection \<open>Basic ML bindings\<close>

ML \<open>
val FalseE = @{thm FalseE}
val Let_def = @{thm Let_def}
val TrueI = @{thm TrueI}
val allE = @{thm allE}
val allI = @{thm allI}
val all_dupE = @{thm all_dupE}
val arg_cong = @{thm arg_cong}
val box_equals = @{thm box_equals}
val ccontr = @{thm ccontr}
val classical = @{thm classical}
val conjE = @{thm conjE}
val conjI = @{thm conjI}
val conjunct1 = @{thm conjunct1}
val conjunct2 = @{thm conjunct2}
val disjCI = @{thm disjCI}
val disjE = @{thm disjE}
val disjI1 = @{thm disjI1}
val disjI2 = @{thm disjI2}
val eq_reflection = @{thm eq_reflection}
val ex1E = @{thm ex1E}
val ex1I = @{thm ex1I}
val ex1_implies_ex = @{thm ex1_implies_ex}
val exE = @{thm exE}
val exI = @{thm exI}
val excluded_middle = @{thm excluded_middle}
val ext = @{thm ext}
val fun_cong = @{thm fun_cong}
val iffD1 = @{thm iffD1}
val iffD2 = @{thm iffD2}
val iffI = @{thm iffI}
val impE = @{thm impE}
val impI = @{thm impI}
val meta_eq_to_obj_eq = @{thm meta_eq_to_obj_eq}
val mp = @{thm mp}
val notE = @{thm notE}
val notI = @{thm notI}
val not_all = @{thm not_all}
val not_ex = @{thm not_ex}
val not_iff = @{thm not_iff}
val not_not = @{thm not_not}
val not_sym = @{thm not_sym}
val refl = @{thm refl}
val rev_mp = @{thm rev_mp}
val spec = @{thm spec}
val ssubst = @{thm ssubst}
val subst = @{thm subst}
val sym = @{thm sym}
val trans = @{thm trans}
\<close>

ML_file "Tools/cnf.ML"


section \<open>@{text NO_MATCH} simproc\<close>

text \<open>
 The simplification procedure can be used to avoid simplification of terms of a certain form
\<close>

definition NO_MATCH :: "'a \<Rightarrow> 'b \<Rightarrow> bool" where "NO_MATCH pat val \<equiv> True"

lemma NO_MATCH_cong[cong]: "NO_MATCH pat val = NO_MATCH pat val" by (rule refl)

declare [[coercion_args NO_MATCH - -]]

simproc_setup NO_MATCH ("NO_MATCH pat val") = \<open>fn _ => fn ctxt => fn ct =>
  let
    val thy = Proof_Context.theory_of ctxt
    val dest_binop = Term.dest_comb #> apfst (Term.dest_comb #> snd)
    val m = Pattern.matches thy (dest_binop (Thm.term_of ct))
  in if m then NONE else SOME @{thm NO_MATCH_def} end
\<close>

text \<open>
  This setup ensures that a rewrite rule of the form @{term "NO_MATCH pat val \<Longrightarrow> t"}
  is only applied, if the pattern @{term pat} does not match the value @{term val}.
\<close>


subsection \<open>Code generator setup\<close>

subsubsection \<open>Generic code generator preprocessor setup\<close>

lemma conj_left_cong:
  "P \<longleftrightarrow> Q \<Longrightarrow> P \<and> R \<longleftrightarrow> Q \<and> R"
  by (fact arg_cong)

lemma disj_left_cong:
  "P \<longleftrightarrow> Q \<Longrightarrow> P \<or> R \<longleftrightarrow> Q \<or> R"
  by (fact arg_cong)

setup \<open>
  Code_Preproc.map_pre (put_simpset HOL_basic_ss) #>
  Code_Preproc.map_post (put_simpset HOL_basic_ss) #>
  Code_Simp.map_ss (put_simpset HOL_basic_ss #>
  Simplifier.add_cong @{thm conj_left_cong} #>
  Simplifier.add_cong @{thm disj_left_cong})
\<close>


subsubsection \<open>Equality\<close>

class equal =
  fixes equal :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes equal_eq: "equal x y \<longleftrightarrow> x = y"
begin

lemma equal: "equal = (op =)"
  by (rule ext equal_eq)+

lemma equal_refl: "equal x x \<longleftrightarrow> True"
  unfolding equal by rule+

lemma eq_equal: "(op =) \<equiv> equal"
  by (rule eq_reflection) (rule ext, rule ext, rule sym, rule equal_eq)

end

declare eq_equal [symmetric, code_post]
declare eq_equal [code]

setup \<open>
  Code_Preproc.map_pre (fn ctxt =>
    ctxt addsimprocs
      [Simplifier.make_simproc @{context} "equal"
        {lhss = [@{term HOL.eq}],
         proc = fn _ => fn _ => fn ct =>
          (case Thm.term_of ct of
            Const (_, Type (@{type_name fun}, [Type _, _])) => SOME @{thm eq_equal}
          | _ => NONE),
         identifier = []}])
\<close>


subsubsection \<open>Generic code generator foundation\<close>

text \<open>Datatype @{typ bool}\<close>

code_datatype True False

lemma [code]:
  shows "False \<and> P \<longleftrightarrow> False"
    and "True \<and> P \<longleftrightarrow> P"
    and "P \<and> False \<longleftrightarrow> False"
    and "P \<and> True \<longleftrightarrow> P" by simp_all

lemma [code]:
  shows "False \<or> P \<longleftrightarrow> P"
    and "True \<or> P \<longleftrightarrow> True"
    and "P \<or> False \<longleftrightarrow> P"
    and "P \<or> True \<longleftrightarrow> True" by simp_all

lemma [code]:
  shows "(False \<longrightarrow> P) \<longleftrightarrow> True"
    and "(True \<longrightarrow> P) \<longleftrightarrow> P"
    and "(P \<longrightarrow> False) \<longleftrightarrow> \<not> P"
    and "(P \<longrightarrow> True) \<longleftrightarrow> True" by simp_all

text \<open>More about @{typ prop}\<close>

lemma [code nbe]:
  shows "(True \<Longrightarrow> PROP Q) \<equiv> PROP Q"
    and "(PROP Q \<Longrightarrow> True) \<equiv> Trueprop True"
    and "(P \<Longrightarrow> R) \<equiv> Trueprop (P \<longrightarrow> R)" by (auto intro!: equal_intr_rule)

lemma Trueprop_code [code]:
  "Trueprop True \<equiv> Code_Generator.holds"
  by (auto intro!: equal_intr_rule holds)

declare Trueprop_code [symmetric, code_post]

text \<open>Equality\<close>

declare simp_thms(6) [code nbe]

instantiation itself :: (type) equal
begin

definition equal_itself :: "'a itself \<Rightarrow> 'a itself \<Rightarrow> bool" where
  "equal_itself x y \<longleftrightarrow> x = y"

instance proof
qed (fact equal_itself_def)

end

lemma equal_itself_code [code]:
  "equal TYPE('a) TYPE('a) \<longleftrightarrow> True"
  by (simp add: equal)

setup \<open>Sign.add_const_constraint (@{const_name equal}, SOME @{typ "'a::type \<Rightarrow> 'a \<Rightarrow> bool"})\<close>

lemma equal_alias_cert: "OFCLASS('a, equal_class) \<equiv> ((op = :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<equiv> equal)" (is "?ofclass \<equiv> ?equal")
proof
  assume "PROP ?ofclass"
  show "PROP ?equal"
    by (tactic \<open>ALLGOALS (resolve_tac @{context} [Thm.unconstrainT @{thm eq_equal}])\<close>)
      (fact \<open>PROP ?ofclass\<close>)
next
  assume "PROP ?equal"
  show "PROP ?ofclass" proof
  qed (simp add: \<open>PROP ?equal\<close>)
qed

setup \<open>Sign.add_const_constraint (@{const_name equal}, SOME @{typ "'a::equal \<Rightarrow> 'a \<Rightarrow> bool"})\<close>

setup \<open>Nbe.add_const_alias @{thm equal_alias_cert}\<close>

text \<open>Cases\<close>

lemma Let_case_cert:
  assumes "CASE \<equiv> (\<lambda>x. Let x f)"
  shows "CASE x \<equiv> f x"
  using assms by simp_all

setup \<open>
  Code.add_case @{thm Let_case_cert} #>
  Code.add_undefined @{const_name undefined}
\<close>

declare [[code abort: undefined]]


subsubsection \<open>Generic code generator target languages\<close>

text \<open>type @{typ bool}\<close>

code_printing
  type_constructor bool \<rightharpoonup>
    (SML) "bool" and (OCaml) "bool" and (Haskell) "Bool" and (Scala) "Boolean"
| constant True \<rightharpoonup>
    (SML) "true" and (OCaml) "true" and (Haskell) "True" and (Scala) "true"
| constant False \<rightharpoonup>
    (SML) "false" and (OCaml) "false" and (Haskell) "False" and (Scala) "false"

code_reserved SML
  bool true false

code_reserved OCaml
  bool

code_reserved Scala
  Boolean

code_printing
  constant Not \<rightharpoonup>
    (SML) "not" and (OCaml) "not" and (Haskell) "not" and (Scala) "'! _"
| constant HOL.conj \<rightharpoonup>
    (SML) infixl 1 "andalso" and (OCaml) infixl 3 "&&" and (Haskell) infixr 3 "&&" and (Scala) infixl 3 "&&"
| constant HOL.disj \<rightharpoonup>
    (SML) infixl 0 "orelse" and (OCaml) infixl 2 "||" and (Haskell) infixl 2 "||" and (Scala) infixl 1 "||"
| constant HOL.implies \<rightharpoonup>
    (SML) "!(if (_)/ then (_)/ else true)"
    and (OCaml) "!(if (_)/ then (_)/ else true)"
    and (Haskell) "!(if (_)/ then (_)/ else True)"
    and (Scala) "!(if ((_))/ (_)/ else true)"
| constant If \<rightharpoonup>
    (SML) "!(if (_)/ then (_)/ else (_))"
    and (OCaml) "!(if (_)/ then (_)/ else (_))"
    and (Haskell) "!(if (_)/ then (_)/ else (_))"
    and (Scala) "!(if ((_))/ (_)/ else (_))"

code_reserved SML
  not

code_reserved OCaml
  not

code_identifier
  code_module Pure \<rightharpoonup>
    (SML) HOL and (OCaml) HOL and (Haskell) HOL and (Scala) HOL

text \<open>using built-in Haskell equality\<close>

code_printing
  type_class equal \<rightharpoonup> (Haskell) "Eq"
| constant HOL.equal \<rightharpoonup> (Haskell) infix 4 "=="
| constant HOL.eq \<rightharpoonup> (Haskell) infix 4 "=="

text \<open>undefined\<close>

code_printing
  constant undefined \<rightharpoonup>
    (SML) "!(raise/ Fail/ \"undefined\")"
    and (OCaml) "failwith/ \"undefined\""
    and (Haskell) "error/ \"undefined\""
    and (Scala) "!sys.error(\"undefined\")"


subsubsection \<open>Evaluation and normalization by evaluation\<close>

method_setup eval = \<open>
  let
    fun eval_tac ctxt =
      let val conv = Code_Runtime.dynamic_holds_conv ctxt
      in
        CONVERSION (Conv.params_conv ~1 (K (Conv.concl_conv ~1 conv)) ctxt) THEN'
        resolve_tac ctxt [TrueI]
      end
  in
    Scan.succeed (SIMPLE_METHOD' o eval_tac)
  end
\<close> "solve goal by evaluation"

method_setup normalization = \<open>
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD'
      (CHANGED_PROP o
        (CONVERSION (Nbe.dynamic_conv ctxt)
          THEN_ALL_NEW (TRY o resolve_tac ctxt [TrueI]))))
\<close> "solve goal by normalization"


subsection \<open>Counterexample Search Units\<close>

subsubsection \<open>Quickcheck\<close>

quickcheck_params [size = 5, iterations = 50]


subsubsection \<open>Nitpick setup\<close>

named_theorems nitpick_unfold "alternative definitions of constants as needed by Nitpick"
  and nitpick_simp "equational specification of constants as needed by Nitpick"
  and nitpick_psimp "partial equational specification of constants as needed by Nitpick"
  and nitpick_choice_spec "choice specification of constants as needed by Nitpick"

declare if_bool_eq_conj [nitpick_unfold, no_atp]
        if_bool_eq_disj [no_atp]


subsection \<open>Preprocessing for the predicate compiler\<close>

named_theorems code_pred_def "alternative definitions of constants for the Predicate Compiler"
  and code_pred_inline "inlining definitions for the Predicate Compiler"
  and code_pred_simp "simplification rules for the optimisations in the Predicate Compiler"


subsection \<open>Legacy tactics and ML bindings\<close>

ML \<open>
  (* combination of (spec RS spec RS ...(j times) ... spec RS mp) *)
  local
    fun wrong_prem (Const (@{const_name All}, _) $ Abs (_, _, t)) = wrong_prem t
      | wrong_prem (Bound _) = true
      | wrong_prem _ = false;
    val filter_right = filter (not o wrong_prem o HOLogic.dest_Trueprop o hd o Thm.prems_of);
  in
    fun smp i = funpow i (fn m => filter_right ([spec] RL m)) ([mp]);
    fun smp_tac ctxt j = EVERY' [dresolve_tac ctxt (smp j), assume_tac ctxt];
  end;

  local
    val nnf_ss =
      simpset_of (put_simpset HOL_basic_ss @{context} addsimps @{thms simp_thms nnf_simps});
  in
    fun nnf_conv ctxt = Simplifier.rewrite (put_simpset nnf_ss ctxt);
  end
\<close>

hide_const (open) eq equal

end
