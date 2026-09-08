(*  Title:      HOL/SMT.thy
    Author:     Sascha Boehme, TU Muenchen
    Author:     Jasmin Blanchette, VU Amsterdam
*)

section \<open>Bindings to Satisfiability Modulo Theories (SMT) solvers based on SMT-LIB 2\<close>

theory SMT
  imports Numeral_Simprocs
  keywords
    "smt_status" :: diag
begin

subsection \<open>A skolemization tactic and proof method\<close>

lemma ex_iff_push: "(\<exists>y. P \<longleftrightarrow> Q y) \<longleftrightarrow> (P \<longrightarrow> (\<exists>y. Q y)) \<and> ((\<forall>y. Q y) \<longrightarrow> P)"
  by metis

ML \<open>
fun moura_tac ctxt =
  TRY o Atomize_Elim.atomize_elim_tac ctxt THEN'
  REPEAT o EqSubst.eqsubst_tac ctxt [0]
    @{thms choice_iff[symmetric] bchoice_iff[symmetric]} THEN'
  TRY o Simplifier.asm_full_simp_tac
    (Simplifier.clear_simpset ctxt |> Simplifier.add_simps @{thms all_simps ex_simps ex_iff_push}) THEN_ALL_NEW
  Metis_Tactic.metis_tac (take 1 ATP_Proof_Reconstruct.partial_type_encs)
    ATP_Proof_Reconstruct.default_metis_lam_trans ctxt []
\<close>

method_setup moura = \<open>
  Scan.succeed (SIMPLE_METHOD' o moura_tac)
\<close> "solve skolemization goals, especially those arising from Z3 proofs"

hide_fact (open) ex_iff_push


subsection \<open>Triggers for quantifier instantiation\<close>

text \<open>
Some SMT solvers support patterns as a quantifier instantiation
heuristics. Patterns may either be positive terms (tagged by "pat")
triggering quantifier instantiations -- when the solver finds a
term matching a positive pattern, it instantiates the corresponding
quantifier accordingly -- or negative terms (tagged by "nopat")
inhibiting quantifier instantiations. A list of patterns
of the same kind is called a multipattern, and all patterns in a
multipattern are considered conjunctively for quantifier instantiation.
A list of multipatterns is called a trigger, and their multipatterns
act disjunctively during quantifier instantiation. Each multipattern
should mention at least all quantified variables of the preceding
quantifier block.
\<close>

typedecl 'a symb_list

consts
  Symb_Nil :: "'a symb_list"
  Symb_Cons :: "'a \<Rightarrow> 'a symb_list \<Rightarrow> 'a symb_list"

typedecl pattern

consts
  pat :: "'a \<Rightarrow> pattern"
  nopat :: "'a \<Rightarrow> pattern"

definition trigger :: "pattern symb_list symb_list \<Rightarrow> bool \<Rightarrow> bool" where
  "trigger _ P = P"


subsection \<open>Higher-order encoding\<close>

text \<open>
Application is made explicit for constants occurring with varying
numbers of arguments. This is achieved by the introduction of the
following constant.
\<close>

definition fun_app :: "'a \<Rightarrow> 'a" where "fun_app f = f"

text \<open>
Some solvers support a theory of arrays which can be used to encode
higher-order functions. The following set of lemmas specifies the
properties of such (extensional) arrays.
\<close>

lemmas array_rules = ext fun_upd_apply fun_upd_same fun_upd_other fun_upd_upd fun_app_def


subsection \<open>Normalization\<close>

lemma case_bool_if[abs_def]: "case_bool x y P = (if P then x else y)"
  by simp

lemmas Ex1_def_raw = Ex1_def[abs_def]
lemmas Ball_def_raw = Ball_def[abs_def]
lemmas Bex_def_raw = Bex_def[abs_def]
lemmas abs_if_raw = abs_if[abs_def]
lemmas min_def_raw = min_def[abs_def]
lemmas max_def_raw = max_def[abs_def]

definition pow_2 where "pow_2 y = power (2::int) (nat y)"

lemma pow_2_raw'': "power (2::nat) \<equiv> (\<lambda>b. nat (pow_2 (int b)))"
  unfolding pow_2_def
  apply (rule eq_reflection)
  apply standard+
  using nat_eq_iff2 by force

lemma nat_zero_as_int:
  "0 = nat 0"
  by simp

lemma nat_one_as_int:
  "1 = nat 1"
  by simp

lemma nat_numeral_as_int: "numeral = (\<lambda>i. nat (numeral i))" by simp
lemma nat_less_as_int: "(<) = (\<lambda>a b. int a < int b)" by simp
lemma nat_leq_as_int: "(\<le>) = (\<lambda>a b. int a \<le> int b)" by simp
lemma Suc_as_int: "Suc = (\<lambda>a. nat (int a + 1))" by (rule ext) simp
lemma nat_plus_as_int: "(+) = (\<lambda>a b. nat (int a + int b))" by (rule ext)+ simp
lemma nat_minus_as_int: "(-) = (\<lambda>a b. nat (int a - int b))" by (rule ext)+ simp
lemma nat_times_as_int: "(*) = (\<lambda>a b. nat (int a * int b))" by (simp add: nat_mult_distrib)
lemma nat_div_as_int: "(div) = (\<lambda>a b. nat (int a div int b))" by (simp add: nat_div_distrib)
lemma nat_mod_as_int: "(mod) = (\<lambda>a b. nat (int a mod int b))" by (simp add: nat_mod_distrib)

lemma int_Suc: "int (Suc n) = int n + 1" by simp
lemma int_plus: "int (n + m) = int n + int m" by (rule of_nat_add)
lemma int_minus: "int (n - m) = int (nat (int n - int m))" by auto

lemma nat_int_comparison:
  fixes a b :: nat
  shows "(a = b) = (int a = int b)"
    and "(a < b) = (int a < int b)"
    and "(a \<le> b) = (int a \<le> int b)"
  by simp_all

named_theorems int_ops \<open>Used when embedding natural numbers into integers\<close>
named_theorems nat_embedding_ops \<open>Used when embedding natural numbers into integers\<close>

lemma [int_ops]:
  fixes a b :: nat
  shows "int 0 = 0"
    and "int 1 = 1"
    and "int (numeral n) = numeral n"
    and "int (Suc a) = int a + 1"
    and "int (a + b) = int a + int b"
    and "int (a - b) = (if int a < int b then 0 else int a - int b)"
    and "int (a * b) = int a * int b"
    and "int (a div b) = int a div int b"
    and "int (a mod b) = int a mod int b"
  by (auto intro: zdiv_int zmod_int)

lemma [int_ops]:
 "int (nat (pow_2 x)) = pow_2 x"
  unfolding pow_2_def
  by simp

lemma int_if:
  fixes a b :: nat
  shows "int (if P then a else b) = (if P then int a else int b)"
  by simp

(*Int lifting*)
named_theorems pow_2_word \<open>power on words should be translated natively\<close>


subsection \<open>Integer division and modulo for Z3\<close>

text \<open>
The following Z3-inspired definitions are overspecified for the case where \<open>l = 0\<close>. This
Schönheitsfehler is corrected in the \<open>div_as_z3div\<close> and \<open>mod_as_z3mod\<close> theorems.
\<close>

definition z3div :: "int \<Rightarrow> int \<Rightarrow> int" where
  "z3div k l = (if l \<ge> 0 then k div l else - (k div - l))"

definition z3mod :: "int \<Rightarrow> int \<Rightarrow> int" where
  "z3mod k l = k mod (if l \<ge> 0 then l else - l)"

lemma div_as_z3div:
  "\<forall>k l. k div l = (if l = 0 then 0 else if l > 0 then z3div k l else z3div (- k) (- l))"
  by (simp add: z3div_def)

lemma mod_as_z3mod:
  "\<forall>k l. k mod l = (if l = 0 then k else if l > 0 then z3mod k l else - z3mod (- k) (- l))"
  by (simp add: z3mod_def)


subsection \<open>Extra theorems for Alethe reconstruction\<close>

lemma alethe_sko_forall[no_atp]: \<open>(\<forall>x. P x) \<longleftrightarrow> P (SOME x. \<not>P x)\<close>
  using someI[of \<open>\<lambda>x. \<not>P x\<close>]
  by auto

lemma alethe_sko_forall'[no_atp]: \<open>P (SOME x. \<not>P x) = A \<Longrightarrow> (\<forall>x. P x) = A\<close>
  by (subst alethe_sko_forall)

lemma alethe_sko_forall'': \<open>B = A \<Longrightarrow> (SOME x. P x) = A \<equiv> (SOME x. P x) = B\<close>
  by auto

lemma alethe_sko_forall_indirect[no_atp]: \<open>x = (SOME x. \<not>P x) \<Longrightarrow> (\<forall>x. P x) \<longleftrightarrow> P x\<close>
  using someI[of \<open>\<lambda>x. \<not>P x\<close>]
  by auto

lemma alethe_sko_forall_indirect2[no_atp]:
    \<open>x = (SOME x. \<not>P x) \<Longrightarrow> (\<And>x :: 'a. (P x = P' x)) \<Longrightarrow> (\<forall>x. P' x) \<longleftrightarrow> P x\<close>
  using someI[of \<open>\<lambda>x. \<not>P x\<close>]
  by auto

lemma alethe_sko_ex[no_atp]: \<open>(\<exists>x. P x) \<longleftrightarrow> P (SOME x. P x)\<close>
  using someI[of \<open>\<lambda>x. P x\<close>]
  by auto

lemma alethe_sko_ex'[no_atp]: \<open>P (SOME x. P x) = A \<Longrightarrow> (\<exists>x. P x) = A\<close>
  by (subst alethe_sko_ex)

lemma alethe_sko_ex_indirect[no_atp]: \<open>x = (SOME x. P x) \<Longrightarrow> (\<exists>x. P x) \<longleftrightarrow> P x\<close>
  using someI[of \<open>\<lambda>x. P x\<close>]
  by auto

lemma alethe_sko_ex_indirect2[no_atp]: \<open>x = (SOME x. P x) \<Longrightarrow> (\<And>x. P x = P' x) \<Longrightarrow> (\<exists>x. P' x) \<longleftrightarrow> P x\<close>
  using someI[of \<open>\<lambda>x. P x\<close>]
  by auto

lemma alethe_Pure_trans[no_atp]:
  \<open>P \<equiv> Q \<Longrightarrow> Q \<Longrightarrow> P\<close>
  by auto

lemma alethe_if_cong[no_atp]:
  assumes \<open>b \<equiv> c\<close>
    and \<open>c \<Longrightarrow> x \<equiv> u\<close>
    and \<open>\<not> c \<Longrightarrow> y \<equiv> v\<close>
  shows \<open>(if b then x else y) \<equiv> (if c then u else v)\<close>
  using assms if_cong[of b c x u] by auto

lemma alethe_if_weak_cong'[no_atp]:
  \<open>b \<equiv> c \<Longrightarrow> (if b then x else y) \<equiv> (if c then x else y)\<close>
  by auto

lemma alethe_or_neg[no_atp]:
   \<open>(A \<Longrightarrow> B) \<Longrightarrow> B \<or> \<not>A\<close>
  by auto

lemma alethe_implies_pos[no_atp]: \<open>\<not>(A \<longrightarrow> B) \<or> \<not>A \<or> B\<close>
  by auto

lemma alethe_subst_bool[no_atp]: \<open>P \<Longrightarrow> f True \<Longrightarrow> f P\<close>
  by auto

lemma alethe_and_pos[no_atp]:
  \<open>(a \<Longrightarrow> \<not>(b \<and> c) \<or> A) \<Longrightarrow> \<not>(a \<and> b \<and> c) \<or> A\<close>
  \<open>(a \<Longrightarrow> b \<Longrightarrow> A) \<Longrightarrow> \<not>(a \<and> b) \<or> A\<close>
  by blast+

lemma alethe_and_pos0[no_atp]:
  \<open>(\<not>(b \<and> c) \<or> A) \<Longrightarrow> \<not>(a \<and> b \<and> c) \<or> A\<close>
  \<open>(\<not>b \<or> A) \<Longrightarrow> \<not>(a \<and> b) \<or> A\<close>
  \<open>A \<Longrightarrow> \<not>a \<or> A\<close>
  by blast+

lemma alethe_farkas[no_atp]:
  \<open>(a \<Longrightarrow> A) \<Longrightarrow> \<not>a \<or> A\<close>
  \<open>(\<not>a \<Longrightarrow> A) \<Longrightarrow> a \<or> A\<close>
  by blast+

lemma alethe_or_pos[no_atp]:
  \<open>A \<and> A' \<Longrightarrow> (c \<and> A) \<or> (\<not>c \<and> A')\<close>
  \<open>A \<and> A' \<Longrightarrow> (\<not>c \<and> A) \<or> (c \<and> A')\<close>
  by blast+

lemma alethe_distinct_elim_two_clauses[no_atp]:
  "((x::bool) \<noteq> y \<and> x \<noteq> z \<and> y \<noteq> z) = False"
  apply (cases "x")
   apply (cases "y")
  by simp_all

lemma alethe_distinct_elim_0[no_atp]:
  \<open>(x \<Longrightarrow> \<not>y \<Longrightarrow> \<not>z \<Longrightarrow> ((x \<noteq> a) \<and> A) = False)
\<Longrightarrow> (\<not>x \<Longrightarrow> y \<Longrightarrow> z \<Longrightarrow> ((x \<noteq> a) \<and> A) = False)
\<Longrightarrow> (((x \<noteq> y) \<and> (x \<noteq> z) \<and> (x \<noteq> a) \<and> A) = False)\<close>
  by (cases x; cases y; cases z; simp)

lemma alethe_distinct_elim_1[no_atp]:
  \<open>((x \<noteq> b) \<and> A) = False \<Longrightarrow> ((x \<noteq> a) \<and> (x \<noteq> b) \<and> A) = False\<close>
  \<open> A = False \<Longrightarrow> ((x \<noteq> a) \<and> A) = False\<close>
  \<open>(x = a) \<Longrightarrow> ((x \<noteq> a) \<and> A) = False\<close>
  by blast+

lemma alethe_distinct_elim_2[no_atp]:
  \<open>\<not> y \<Longrightarrow> \<not> z \<Longrightarrow> y = z\<close>
  \<open>y \<Longrightarrow> z \<Longrightarrow> y = z\<close>
  by blast+

lemma alethe_shuffle_and1[no_atp]:
  \<open> A = B \<Longrightarrow> (a \<and> A) = (a \<and> B)\<close>
  by blast

lemma alethe_shuffle_and2[no_atp]:
  \<open>(\<not>a \<longrightarrow> \<not>B) \<Longrightarrow> (a \<Longrightarrow> A = (b \<and> B)) \<Longrightarrow> (a \<and> A) = (b \<and> B)\<close>
  \<open>(\<not>a \<longrightarrow> \<not>(b \<and> B)) \<Longrightarrow> (a \<Longrightarrow> (b \<and> B)) \<Longrightarrow> a = (b \<and> B)\<close>
  by (cases a) auto

lemma alethe_shuffle_and3[no_atp]:
  \<open>b = A \<Longrightarrow> (a \<Longrightarrow> b = (a \<and> A))\<close>
  apply (cases a)
  by simp_all

lemma alethe_shuffle_and4[no_atp]:
  \<open>A \<Longrightarrow> (a = (a \<and> A))\<close>
  apply (cases a)
  by simp_all

lemma alethe_shuffle_or_split[no_atp]:
  "(a \<longrightarrow> (b \<or> B)) \<Longrightarrow> (\<not>a \<Longrightarrow> A = (b \<or> B)) \<Longrightarrow> (a \<or> A) = (b \<or> B)"
  "(a \<longrightarrow> (b \<or> B)) \<Longrightarrow> (\<not>a \<Longrightarrow> \<not>(b \<or> B)) \<Longrightarrow> a = (b \<or> B)"
  by auto

lemma alethe_shuffle_or_resolve[no_atp]:
  "a \<longrightarrow> (a \<or> A)"
  "a \<longrightarrow> A \<Longrightarrow> a \<longrightarrow> (b \<or> A)"
  by auto

lemma alethe_shuffle_or1a[no_atp]: "(A = B) \<Longrightarrow> (a \<or> A) = (a \<or> B)" by auto
lemma alethe_shuffle_or1b[no_atp]: "\<not>B \<Longrightarrow> a = (a \<or> B)" by auto

lemma alethe_shuffle_or4a[no_atp]: "a \<longrightarrow> (a \<or> B)" by auto
lemma alethe_shuffle_or4b[no_atp]: "(a \<longrightarrow> B) \<Longrightarrow> (a \<longrightarrow> (b \<or> B))" by auto

lemma alethe_shuffle_or2b[no_atp]: "(b \<Longrightarrow> A) \<Longrightarrow> (\<not>b \<Longrightarrow> A = B) \<Longrightarrow> A = (b \<or> B)"
  by auto

lemma alethe_shuffle_or3[no_atp]: "(a \<Longrightarrow> A) \<Longrightarrow> (\<not>a \<Longrightarrow> A) \<Longrightarrow> (a \<or> A)"
  by auto

lemma alethe_shuffle_or5[no_atp]: "(a \<Longrightarrow> A) \<Longrightarrow> (\<not>a \<Longrightarrow> \<not>A) \<Longrightarrow> (a = A)"
  by auto

lemma alethe_shuffle_or6[no_atp]: "\<not>A \<Longrightarrow> (\<not>a \<Longrightarrow> (a = A))"
  by auto

lemma alethe_la_generic[no_atp]:
  \<open>(a::int) \<le> x \<or> a = x \<or> a \<ge> x\<close>
  by linarith

lemma alethe_bfun_elim[no_atp]:
  \<open>(if b then P True else P False) = P b\<close>
  \<open>(\<forall>b. P' b) = (P' False \<and> P' True)\<close>
  \<open>(\<exists>b. P' b) = (P' False \<or> P' True)\<close>
  by (cases b) (auto simp: all_bool_eq ex_bool_eq)

lemma alethe_eq_true_simplify[no_atp]:
  \<open>(P = True) \<equiv> P\<close>
  by auto

lemma alethe_and_neg[no_atp]:
  \<open>(a \<Longrightarrow> \<not>b \<or> A) \<Longrightarrow> \<not>(a \<and> b) \<or> A\<close>
  \<open>(a \<Longrightarrow> A) \<Longrightarrow> \<not>a \<or> A\<close>
  \<open>(\<not>a \<Longrightarrow> A) \<Longrightarrow> a \<or> A\<close>
  by blast+

lemma alethe_forall_inst[no_atp]:
  \<open>A \<longleftrightarrow> B \<Longrightarrow> \<not>A \<or> B\<close>
  \<open>\<not>A \<longleftrightarrow> B \<Longrightarrow> A \<or> B\<close>
  \<open>A \<longleftrightarrow> B \<Longrightarrow> \<not>B \<or> A\<close>
  \<open>A \<longleftrightarrow> \<not>B \<Longrightarrow> B \<or> A\<close>
  \<open>A \<longrightarrow> B \<Longrightarrow> \<not>A \<or> B\<close>
  \<open>\<not>A \<longrightarrow> B \<Longrightarrow> A \<or> B\<close>
  by blast+

lemma alethe_eq_transitive[no_atp]:
  \<open>A = B \<Longrightarrow> B = C \<Longrightarrow> A = C\<close>
  \<open>A = B \<Longrightarrow> C = B \<Longrightarrow> A = C\<close>
  \<open>B = A \<Longrightarrow> B = C \<Longrightarrow> A = C\<close>
  \<open>B = A \<Longrightarrow> C = B \<Longrightarrow> A = C\<close>
  by auto

lemma alethe_bool_simplify[no_atp]:
  \<open>\<not>(P \<longrightarrow> Q) \<longleftrightarrow> P \<and> \<not>Q\<close>
  \<open>\<not>(P \<or> Q) \<longleftrightarrow> \<not>P \<and> \<not>Q\<close>
  \<open>\<not>(P \<and> Q) \<longleftrightarrow> \<not>P \<or> \<not>Q\<close>
  \<open>(P \<longrightarrow> (Q \<longrightarrow> R)) \<longleftrightarrow> ((P \<and> Q) \<longrightarrow> R)\<close>
  \<open>((P \<longrightarrow> Q) \<longrightarrow> Q) \<longleftrightarrow> P \<or> Q\<close>
  \<open>(Q \<longleftrightarrow> (P \<or> Q)) \<longleftrightarrow> (P \<longrightarrow> Q)\<close> \<comment> \<open>This rule was inverted\<close>
  \<open>P \<and> (P \<longrightarrow> Q) \<longleftrightarrow> P \<and> Q\<close>
  \<open>(P \<longrightarrow> Q) \<and> P \<longleftrightarrow> P \<and> Q\<close>
 (* \<comment>\<open>Additional rules:\<close>
  *  \<open>((P \<longrightarrow> Q) \<longrightarrow> P) \<longleftrightarrow> P\<close>
  *  \<open>((P \<longrightarrow> Q) \<longrightarrow> Q) \<longleftrightarrow> P \<or> Q\<close>
  *  \<open>(P \<longrightarrow> Q) \<or> P\<close> *)
  unfolding not_imp imp_conjL
  by auto

lemma alethe_connective_def[no_atp]:
  \<open>(A \<noteq> B) = ((\<not>A \<and> B) \<or> (A \<and> \<not>B))\<close> \<comment> \<open>xor case\<close>
  \<open>(A = B) = ((A \<longrightarrow> B) \<and> (B \<longrightarrow> A))\<close>
  \<open>(If A B C) = ((A \<longrightarrow> B) \<and> (\<not>A \<longrightarrow> C))\<close>
  apply (case_tac [!] A)
  by simp_all

lemma alethe_connective_def_forall[no_atp]:
  assumes "\<And>x::'a. (P x = (Q x))"
  shows "(\<forall>x. P x) = (\<forall>x. Q x )"
  using assms
  unfolding All_def
  by (iprover intro: ext eqTrueI assms)

lemma alethe_connective_def_forall2[no_atp]:
  assumes "(P = Q)"
  shows "(\<forall>x. P x) = (\<forall>x. Q x)"
  unfolding assms ..

(*the last theorems are needed because we do not
know in what order the simplifications are applied.*)
lemma alethe_ite_simplify[no_atp]:
  \<open>(If True B C) = B\<close>
  \<open>(If False B C) = C\<close>
  \<open>(If A' B B) = B\<close>
  \<open>(If (\<not>A') B C) = (If A' C B)\<close>
  \<open>(If c (If c A B) C) = (If c A C)\<close>
  \<open>(If c C (If c A B)) = (If c C B)\<close>
  \<open>(If A' True False) = A'\<close>
  \<open>(If A' False True) \<longleftrightarrow> \<not>A'\<close>
  \<open>(If A' True B') \<longleftrightarrow> A' \<or> B'\<close>
  \<open>(If A' B' False) \<longleftrightarrow> A' \<and> B'\<close>
  \<open>(If A' False B') \<longleftrightarrow> \<not>A' \<and> B'\<close>
  \<open>(If A' B' True) \<longleftrightarrow> \<not>A' \<or> B'\<close>
  \<open>x \<and> True \<longleftrightarrow> x\<close>
  \<open>x \<or> False \<longleftrightarrow> x\<close>
  \<open>x \<or> True \<longleftrightarrow> True\<close>
  \<open>x \<and> False \<longleftrightarrow> False\<close>
  \<open>True \<and> x \<longleftrightarrow> x\<close>
  \<open>False \<or> x \<longleftrightarrow> x\<close>
  \<open>True \<or> x \<longleftrightarrow> True\<close>
  \<open>False \<and> x \<longleftrightarrow> False\<close>
  for B C :: 'a and A' B' C' :: bool
  by auto

lemma alethe_and_simplify1[no_atp]:
  \<open>True \<and> b \<longleftrightarrow> b\<close> \<open>b \<and> True \<longleftrightarrow> b\<close>
  \<open>False \<and> b \<longleftrightarrow> False\<close> \<open>b \<and> False \<longleftrightarrow> False\<close>
  \<open>(c \<and> \<not>c) \<longleftrightarrow> False\<close> \<open>(\<not>c \<and> c) \<longleftrightarrow> False\<close>
  \<open>\<not>\<not>a = a\<close>
  by auto

lemmas alethe_and_simplify [no_atp] = conj_ac de_Morgan_conj disj_not1

lemma alethe_or_simplify_1[no_atp]:
  \<open>False \<or> b \<longleftrightarrow> b\<close> \<open>b \<or> False \<longleftrightarrow> b\<close>
  \<open>b \<or> \<not>b\<close>
  \<open>\<not>b \<or> b\<close>
  by auto

lemmas alethe_or_simplify [no_atp] = disj_ac

lemma alethe_not_simplify [no_atp]:
  \<open>\<not> \<not>b \<longleftrightarrow> b\<close> \<open>\<not>True \<longleftrightarrow> False\<close> \<open>\<not>False \<longleftrightarrow> True\<close>
  by auto

lemma alethe_implies_simplify[no_atp]:
  \<open>(\<not>a \<longrightarrow> \<not>b) \<longleftrightarrow> (b \<longrightarrow> a)\<close>
  \<open>(False \<longrightarrow> a) \<longleftrightarrow> True\<close>
  \<open>(a \<longrightarrow> True) \<longleftrightarrow> True\<close>
  \<open>(True \<longrightarrow> a) \<longleftrightarrow> a\<close>
  \<open>(a \<longrightarrow> False) \<longleftrightarrow> \<not>a\<close>
  \<open>(a \<longrightarrow> a) \<longleftrightarrow> True\<close>
  \<open>(\<not>a \<longrightarrow> a) \<longleftrightarrow> a\<close>
  \<open>(a \<longrightarrow> \<not>a) \<longleftrightarrow> \<not>a\<close>
  \<open>((a \<longrightarrow> b) \<longrightarrow> b) \<longleftrightarrow> a \<or> b\<close> (*Why is this necessary*)
  \<open>(\<not>True) \<longleftrightarrow> False\<close> (* Because of non determinism *)
  \<open>(\<not>False) \<longleftrightarrow> True\<close>
  by auto

lemma alethe_equiv_simplify[no_atp]:
  \<open>((\<not>a) = (\<not>b)) \<longleftrightarrow> (a = b)\<close>
  \<open>(a = a) \<longleftrightarrow> True\<close>
  \<open>(a = (\<not>a)) \<longleftrightarrow> False\<close>
  \<open>((\<not>a) = a) \<longleftrightarrow> False\<close>
  \<open>(True = a) \<longleftrightarrow> a\<close>
  \<open>(a = True) \<longleftrightarrow> a\<close>
  \<open>(False = a) \<longleftrightarrow> \<not>a\<close>
  \<open>(a = False) \<longleftrightarrow> \<not>a\<close>
  \<open>\<not>\<not>a \<longleftrightarrow> a\<close>
  \<open>(\<not> False) = True\<close>
  for a b :: bool
  by auto

lemmas alethe_eq_simplify[no_atp] =
  eq_refl num.simps neg_equal_zero equal_neg_zero neg_equal_iff_equal Num.rel_simps

lemma alethe_minus_simplify[no_atp]:
  \<open>(a :: 'a :: cancel_comm_monoid_add) - a = 0\<close>
  \<open>(a :: 'a :: cancel_comm_monoid_add) - 0 = a\<close>
  \<open>0 - (b :: 'b :: {group_add}) = -b\<close>
  \<open>- (- (b :: 'b :: group_add)) = b\<close>
  by auto

lemma alethe_sum_simplify[no_atp]:
  \<open>(a :: 'a :: cancel_comm_monoid_add) + 0 = a\<close>
  by auto

lemmas alethe_prod_simplify[no_atp] =
   mult_1
   mult_1_right

lemmas alethe_div_simplify[no_atp] =
   divide_self div_minus_minus div_by_1
   divide_numeral_1 one_plus_numeral
   divmod_steps less_irrefl divmod_trivial divmod_cancel
   numeral_div_numeral prod.case mult.right_neutral
   divmod_step_def euclidean_size_int_def comp_def of_bool_eq
   nat_numeral fst_conv snd_conv if_False if_True
   minus_numeral_div_numeral Parity.adjust_div_eq
   order_refl
   num.simps numerals eq_neg_numeral_simps eq_numeral_simps
   old.nat.distinct
   mult_numeral_left_semiring_numeral le_numeral_Suc pred_numeral_simps Suc_le_mono le_zero_eq
   le_num_simps less_num_simps euclidean_size_numeral le_numeral_simps numeral_plus_one
   mult.left_neutral numeral_div_minus_numeral
   nat_1 nat_0

lemma alethe_comp_simplify1[no_atp]:
  \<open>(a :: 'a ::order) < a \<longleftrightarrow> False\<close>
  \<open>a \<le> a\<close>
  \<open>\<not>(b' \<le> a') \<longleftrightarrow> (a' :: 'b :: linorder) < b'\<close>
  by auto

lemmas alethe_comp_simplify[no_atp] =
  alethe_comp_simplify1
  zero_less_one
  zero_le_one
  rel_simps

lemma alethe_la_disequality[no_atp]:
  \<open>(a :: 'a ::linorder) = b \<or> \<not>a \<le> b \<or> \<not>b \<le> a\<close>
  by auto

lemma alethe_la_mult_pos_less[no_atp]:
  \<open>(0 :: 'a :: linordered_idom) < m \<and> (a < b) \<longrightarrow> m*a < m*b\<close>
  by simp

lemma alethe_la_mult_pos[no_atp]:
  \<open>c = (0 :: 'a :: linordered_idom) \<Longrightarrow> c < m \<and> (a < b) \<longrightarrow> m*a < m*b\<close>
  \<open>c = (0 :: 'a :: linordered_idom) \<Longrightarrow> c < m \<and> (a \<le> b) \<longrightarrow> m*a \<le> m*b\<close>
  \<open>c = (0 :: 'a :: linordered_idom) \<Longrightarrow> c < m \<and> (a = b) \<longrightarrow> m*a = m*b\<close>
  \<open>c = (0 :: 'a :: linordered_idom) \<Longrightarrow> c < m \<and> \<not>(a = b) \<longrightarrow> \<not>(m*a = m*b)\<close>
  \<open>c = (0 :: 'a :: linordered_idom) \<Longrightarrow> c < m \<and> (a \<ge> b) \<longrightarrow> m*a \<ge> m*b\<close>
  \<open>c = (0 :: 'a :: linordered_idom) \<Longrightarrow> c < m \<and> (a > b) \<longrightarrow> m*a > m*b\<close>
  by simp_all

lemma alethe_la_mult_neg[no_atp]:
  \<open>c = (0 :: 'a :: linordered_idom) \<Longrightarrow> m < c \<and> (a < b) \<longrightarrow> m*a > m*b\<close>
  \<open>c = (0 :: 'a :: linordered_idom) \<Longrightarrow> m < c \<and> (a \<le> b) \<longrightarrow> m*a \<ge> m*b\<close>
  \<open>c = (0 :: 'a :: linordered_idom) \<Longrightarrow> m < c \<and> (a = b) \<longrightarrow> m*a = m*b\<close>
  \<open>c = (0 :: 'a :: linordered_idom) \<Longrightarrow> m < c \<and> \<not>(a = b) \<longrightarrow> \<not>(m*a = m*b)\<close>
  \<open>c = (0 :: 'a :: linordered_idom) \<Longrightarrow> m < c \<and> (a > b) \<longrightarrow> m*a < m*b\<close>
  \<open>c = (0 :: 'a :: linordered_idom) \<Longrightarrow> m < c \<and> (a \<ge> b) \<longrightarrow> m*a \<le> m*b\<close>
  by simp_all

context
begin

text \<open>For the reconstruction, we need to keep the order of the arguments.\<close>

named_theorems smt_arith_multiplication \<open>Theorems to reconstruct arithmetic theorems.\<close>

named_theorems smt_arith_combine \<open>Theorems to reconstruct arithmetic theorems.\<close>

named_theorems smt_arith_simplify \<open>Theorems to combine theorems in the LA procedure\<close>

named_theorems smt_rewrite_lemma_simplify \<open>Theorems to simplify instantiate lemma during rewrite reconstruction\<close>

(*Currently
arith_simp_cvc5 == smt_arith_simplify

arith_mult_poly_norm_cvc5 is meant to be used with field_simps, so
we removed some theorems that were already in them.
*)
named_theorems arith_simp_cvc5 \<open>Might be temp and integrated into smt_arith_simplify\<close>
named_theorems arith_mult_poly_norm_cvc5 \<open>Extra rules for reconstruction of poly-norm.\<close>

lemmas [arith_mult_poly_norm_cvc5] =
         Groups.monoid_mult_class.mult_1_right Nat.mult_Suc_right
         Nat.mult_0_right Nat.add_Suc_right Groups.monoid_add_class.add.right_neutral
         Num.numeral_2_eq_2 Nat.One_nat_def Num.numeral_2_eq_2 Nat.One_nat_def
         Nat.Suc_less_eq Nat.zero_less_Suc minus_nat.diff_0 Nat.diff_Suc_Suc Nat.le0
         prod.case numeral_plus_one divmod_step_def order.refl le_zero_eq
         le_numeral_simps less_numeral_simps mult.right_neutral divides_aux_eq
         mult_nonneg_nonneg dvd_imp_mod_0 dvd_add zero_less_one mod_mult_self4 numeral_mod_numeral
         divmod_trivial prod.sel mult.left_neutral div_pos_pos_trivial arith_simps div_add div_mult_self1
         add_le_cancel_left add_le_same_cancel2 not_one_le_zero le_numeral_simps add_le_same_cancel1
         zero_neq_one zero_le_one le_num_simps add_Suc mod_div_trivial nat.distinct mult_minus_right
         add.inverse_inverse distrib_left_numeral mult_num_simps numeral_times_numeral add_num_simps
         divmod_steps rel_simps if_True if_False numeral_div_numeral divmod_cancel prod.case
         add_num_simps one_plus_numeral fst_conv arith_simps sub_num_simps dbl_inc_simps
         dbl_simps mult_1 add_le_cancel_right left_diff_distrib_numeral add_uminus_conv_diff zero_neq_one
         zero_le_one One_nat_def add_Suc mod_div_trivial nat.distinct of_int_1 numerals numeral_One
         of_int_numeral add_uminus_conv_diff zle_diff1_eq add_less_same_cancel2 minus_add_distrib
         add_uminus_conv_diff mult.left_neutral semiring_class.distrib_right
         add_diff_cancel_left' ring_distribs mult_minus_left minus_diff_eq

lemmas [smt_arith_simplify] =
   Groups.monoid_mult_class.mult_1_right Nat.mult_Suc_right
   Nat.mult_0_right Nat.add_Suc_right Groups.monoid_add_class.add.right_neutral
   Num.numeral_2_eq_2 Nat.One_nat_def
   Nat.Suc_less_eq Nat.zero_less_Suc minus_nat.diff_0 Nat.diff_Suc_Suc Nat.le0
   prod.case numeral_plus_one divmod_step_def order.refl le_zero_eq
   mult.right_neutral divides_aux_eq
   mult_nonneg_nonneg dvd_imp_mod_0 dvd_add zero_less_one mod_mult_self4 numeral_mod_numeral
   divmod_trivial prod.sel mult.left_neutral div_pos_pos_trivial arith_simps div_add div_mult_self1
   add_le_cancel_left add_le_same_cancel2 not_one_le_zero add_le_same_cancel1
   zero_neq_one zero_le_one add_Suc mod_div_trivial nat.distinct mult_minus_right
   add.inverse_inverse distrib_left_numeral
   divmod_steps rel_simps if_True if_False numeral_div_numeral divmod_cancel
   one_plus_numeral fst_conv
   mult_1 add_le_cancel_right left_diff_distrib_numeral add_uminus_conv_diff
   of_int_1 numerals numeral_One
   of_int_numeral zle_diff1_eq add_less_same_cancel2 minus_add_distrib
   semiring_class.distrib_right
   add_diff_cancel_left' add_diff_eq ring_distribs mult_minus_left minus_diff_eq
   mod_mult_self2_is_0
   less_irrefl

lemmas [arith_simp_cvc5] =
  smt_arith_simplify
  ab_semigroup_mult_class.mult.commute

lemma [arith_simp_cvc5,arith_mult_poly_norm_cvc5,smt_arith_simplify]:
  \<open>\<not> (a' :: 'a :: linorder) < b' \<longleftrightarrow> b' \<le> a'\<close>
  \<open>\<not> (a' :: 'a :: linorder) \<le> b' \<longleftrightarrow> b' < a'\<close>
  \<open>(c::int) mod Numeral1 = 0\<close>
  \<open>(a::nat) mod Numeral1 = 0\<close>
  \<open>(c::int) div Numeral1 = c\<close>
  \<open>a div Numeral1 = a\<close>
  \<open>(c::int) mod 1 = 0\<close>
  \<open>a mod 1 = 0\<close>
  \<open>(c::int) div 1 = c\<close>
  \<open>a div 1 = a\<close>
  \<open>\<not>(a' \<noteq> b') \<longleftrightarrow> a' = b'\<close>
  by auto

lemma [arith_simp_cvc5,arith_mult_poly_norm_cvc5]:
  \<open>NO_MATCH 0 (b:: int) \<Longrightarrow> NO_MATCH 0 (a:: int) \<Longrightarrow> a < b \<longleftrightarrow> b - a > 0\<close>
  \<open>NO_MATCH 0 b \<Longrightarrow> NO_MATCH 0 a \<Longrightarrow> a \<le> b \<longleftrightarrow> b - a \<ge> 0\<close>
  \<open>NO_MATCH 0 b \<Longrightarrow> NO_MATCH 0 a \<Longrightarrow> a = b \<longleftrightarrow> b - a = 0\<close>
  by auto

lemmas [arith_simp_cvc5,arith_mult_poly_norm_cvc5,smt_arith_simplify] = divide_eq_eq_numeral1
  uminus_add_conv_diff divide_less_eq_numeral1
  diff_gt_0_iff_gt times_divide_eq_left

lemma div_mod_decomp: "A = (A div n) * n + (A mod n)" for A :: nat
  by auto

lemma div_less_mono:
  fixes A B :: nat
  assumes "A < B" "0 < n" and
    mod: "A mod n = 0""B mod n = 0"
  shows "(A div n) < (B div n)"
  using assms(1)
  by (subst (asm) div_mod_decomp[of "A" n], subst (asm) div_mod_decomp[of "B" n],
    unfold mod, use assms(2,3) in \<open>auto simp: ac_simps\<close>)

lemma alethe_le_mono_div[no_atp]:
  fixes A B :: nat
  assumes "A < B" "0 < n"
  shows "(A div n) + (if B mod n = 0 then 1 else 0) \<le> (B div n)"
  by (auto simp: ac_simps Suc_leI assms less_mult_imp_div_less div_le_mono less_imp_le_nat)

lemmas [smt_arith_multiplication] =
  alethe_le_mono_div[THEN mult_le_mono1, unfolded add_mult_distrib]
  div_le_mono[THEN mult_le_mono2, unfolded add_mult_distrib]

lemma div_mod_decomp_int: "A = (A div n) * n + (A mod n)" for A :: int
  by auto

lemma zdiv_mono_strict:
  fixes A B :: int
  assumes "A < B" "0 < n" and
    mod: "A mod n = 0""B mod n = 0"
  shows "(A div n) < (B div n)"
proof -
  show ?thesis
    using assms(1)
    apply (subst (asm) div_mod_decomp_int[of A n])
    apply (subst (asm) div_mod_decomp_int[of B n])
    unfolding mod
    by (use assms(2,3) in \<open>auto simp: ac_simps\<close>)
qed

lemma alethe_le_mono_div_int[no_atp]:
  \<open>A div n + (if B mod n = 0 then 1 else 0) \<le> B div n\<close>
    if \<open>A < B\<close> \<open>0 < n\<close>
    for A B n :: int
proof -
  from \<open>A < B\<close> \<open>0 < n\<close> have \<open>A div n \<le> B div n\<close>
    by (auto intro: zdiv_mono1)
  show ?thesis
  proof (cases \<open>n dvd B\<close>)
    case False
    with \<open>A div n \<le> B div n\<close> show ?thesis
      by auto
  next
    case True
    then obtain C where \<open>B = n * C\<close> ..
    then have \<open>B div n = C\<close>
      using \<open>0 < n\<close> by simp
    from \<open>0 < n\<close> have \<open>A mod n \<ge> 0\<close>
      by simp
    have \<open>A div n < C\<close>
    proof (rule ccontr)
      assume \<open>\<not> A div n < C\<close>
      then have \<open>C \<le> A div n\<close>
        by simp
      with \<open>B div n = C\<close> \<open>A div n \<le> B div n\<close>
      have \<open>A div n = C\<close>
        by simp
      moreover from \<open>A < B\<close> have \<open>n * (A div n) + A mod n < B\<close>
        by simp
      ultimately have \<open>n * C + A mod n < n * C\<close>
        using \<open>B = n * C\<close> by simp
      moreover have \<open>A mod n \<ge> 0\<close>
        using \<open>0 < n\<close> by simp
      ultimately show False
        by simp
    qed
    with \<open>n dvd B\<close> \<open>B div n = C\<close> show ?thesis
      by simp
  qed
qed

lemma alethe_less_mono_div_int2[no_atp]:
  fixes A B :: int
  assumes "A \<le> B" "0 < -n"
  shows "(A div n) \<ge> (B div n)"
  using assms(1) assms(2) zdiv_mono1_neg by auto

lemmas [smt_arith_multiplication] =
  alethe_le_mono_div_int[THEN mult_left_mono, unfolded int_distrib]
  zdiv_mono1[THEN mult_left_mono, unfolded int_distrib]

(*making it specific to not clash with the real version where div is just division*)
lemma [smt_arith_multiplication]:
  "(x::nat) = y \<Longrightarrow> x div n * p = y div n * p"
  "(x'::int) = y' \<Longrightarrow> x' div n' * p' = y' div n' * p'"
  by simp_all

lemma [smt_arith_combine]:
  "a < b \<Longrightarrow> c < d \<Longrightarrow> a + c + 2 \<le> b + d"
  "a < b \<Longrightarrow> c \<le> d \<Longrightarrow> a + c + 1 \<le> b + d"
  "a \<le> b \<Longrightarrow> c < d \<Longrightarrow> a + c + 1 \<le> b + d" for a b c :: int
  by auto

lemma [smt_arith_combine]:
  "a < b \<Longrightarrow> c < d \<Longrightarrow> a + c + 2 \<le> b + d"
  "a < b \<Longrightarrow> c \<le> d \<Longrightarrow> a + c + 1 \<le> b + d"
  "a \<le> b \<Longrightarrow> c < d \<Longrightarrow> a + c + 1 \<le> b + d" for a b c :: nat
  by auto

lemmas [smt_arith_combine] =
  add_strict_mono
  add_less_le_mono
  add_mono
  add_le_less_mono

lemma [smt_arith_combine]:
  \<open>m < n \<Longrightarrow> c = d \<Longrightarrow> m + c < n + d\<close>
  \<open>m \<le> n \<Longrightarrow> c = d \<Longrightarrow> m + c \<le> n + d\<close>
  \<open>c = d \<Longrightarrow> m < n \<Longrightarrow> m + c < n + d\<close>
  \<open>c = d \<Longrightarrow> m \<le> n \<Longrightarrow> m + c \<le> n + d\<close>
  for m :: \<open>'a :: ordered_cancel_ab_semigroup_add\<close>
  by (auto intro: ordered_cancel_ab_semigroup_add_class.add_strict_right_mono
    ordered_ab_semigroup_add_class.add_right_mono)

lemma [smt_arith_combine]:
  "c = d \<Longrightarrow> e = f \<Longrightarrow> c + e = d + f"
  by simp

lemma alethe_negate_coefficient[no_atp]:
  \<open>a \<le> (b :: 'a :: {ordered_ab_group_add}) \<Longrightarrow> -a \<ge> -b\<close>
  \<open>a < b \<Longrightarrow> -a > -b\<close>
  \<open>a = b \<Longrightarrow> -a = -b\<close>
  by auto

lemma alethe_invert_farkas_equation[no_atp]:
  \<open>a \<le> (b :: 'a :: {ordered_ab_group_add}) \<Longrightarrow> -a \<ge> -b\<close>
  \<open>a < b \<Longrightarrow> -a > -b\<close>
  \<open>a = b \<Longrightarrow> b = a\<close>
  by auto

end

lemma alethe_ite_intro[no_atp]:
  \<open>(If p (a' = (If p a' b')) (b' = (If p a' b'))) \<longleftrightarrow> True\<close>
  \<open>(If p (a' = (If p a' b')) ((If p a' b') = b')) \<longleftrightarrow> True\<close>
  \<open>(If p ((If p a' b') = a') (b' = (If p a' b'))) \<longleftrightarrow> True\<close>
  \<open>(If p ((If p a' b') =a') ((If p a' b') = b')) \<longleftrightarrow> True\<close>
  \<open>(if a then P (if a then a' else b') else Q) \<longleftrightarrow> (if a then P a' else Q)\<close>
  \<open>(if a then P' else Q' (if a then a' else b')) \<longleftrightarrow> (if a then P' else Q' b')\<close>
  \<open>A = f (if a then R else S) \<longleftrightarrow> (if a then A = f R else A = f S)\<close>
  by auto

lemma alethe_ite_if_cong[no_atp]:
  fixes x y :: bool
  assumes "b = c"
    and "c \<equiv> True \<Longrightarrow> x = u"
    and "c \<equiv> False \<Longrightarrow> y = v"
  shows "(if b then x else y) \<equiv> (if c then u else v)"
proof -
  have H: "(if b then x else y) = (if c then u else v)"
    using assms by (auto split: if_splits)

  show "(if b then x else y) \<equiv> (if c then u else v)"
    by (subst H) auto
qed

lemma alethe_miniscope_distribute[no_atp]:
  \<open>(\<forall>X. (F1 X \<and> A X)) = ((\<forall>X. F1 X) \<and> (\<forall>X. A X))\<close>
  \<open>(\<exists>X. (F1 X \<or> A X)) = ((\<exists>X. F1 X) \<or> (\<exists>X. A X))\<close>
  by (simp_all only: all_conj_distrib ex_disj_distrib)

lemma alethe_miniscope_split[no_atp]:
  \<open>((\<forall>x. F1 x) \<or> (\<forall>y. A y)) = (\<forall>x y. (F1 x \<or> A y))\<close>
  \<open>((\<forall>x. F1 x) \<or> B) = (\<forall>x. (F1 x \<or> B))\<close>
  \<open>(B \<or> (\<forall>x. F1 x)) = (\<forall>x. (B \<or> F1 x))\<close>
  \<open>((\<exists>x. F1 x) \<and> (\<exists>y. A y)) = (\<exists>x y. (F1 x \<and> A y))\<close>
  \<open>((\<exists>x. F1 x) \<and> B) = (\<exists>x. (F1 x \<and> B))\<close>
  \<open>(B \<and> (\<exists>x. F1 x)) = (\<exists>x. (B \<and> F1 x))\<close>
  by simp_all

lemma alethe_miniscope_ITE[no_atp]:
  \<open>(\<forall>x Y. (if C then F1 x else A Y)) = (if C then (\<forall>x. F1 x) else (\<forall>Y. A Y))\<close>
  \<open>(\<forall>x. (if C then F1 x else B)) = (if C then (\<forall>x. F1 x) else (\<forall>Y. B))\<close>
  \<open>(\<forall>Y. (if C then F2 else A Y)) = (if C then F2 else (\<forall>Y. A Y))\<close>
  by simp_all

named_theorems alethe_poly_simp_rel \<open>Theorems required to replay poly_simp_rel\<close>

lemma [alethe_poly_simp_rel]:
  fixes x1::"int" and x2 y1 y2 cx cy
  shows "cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * (x1 - x2)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 = x2) = (y1 = y2))"
  by force

lemma [alethe_poly_simp_rel]:
  fixes x1::"int" and x2 y1 y2 cx cy
  shows "((cx > 0) = (cy > 0)) \<Longrightarrow> cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * (x1 - x2)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 < x2) = (y1 < y2))"
  by (metis less_iff_diff_less_0 mult_less_0_iff not_less_iff_gr_or_eq zero_less_mult_iff)

lemma [alethe_poly_simp_rel]:
  fixes x1::"int" and x2 y1 y2 cx cy
  shows "((cx > 0) = (cy > 0)) \<Longrightarrow> cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * (x1 - x2)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 \<le> x2) = (y1 \<le> y2))"
  by (metis diff_gt_0_iff_gt linorder_not_le mult_less_0_iff not_less_iff_gr_or_eq zero_less_mult_iff)

lemma [alethe_poly_simp_rel]:
  fixes x1::"int" and x2 y1 y2 cx cy
  shows "((cx > 0) = (cy > 0)) \<Longrightarrow> cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * (x1 - x2)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 > x2) = (y1 > y2))"
  by (metis le_iff_diff_le_0 linorder_not_le mult_less_0_iff nless_le zero_less_mult_iff)

lemma [alethe_poly_simp_rel]:
  fixes x1::"int" and x2 y1 y2 cx cy
  shows "((cx > 0) = (cy > 0)) \<Longrightarrow> cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * (x1 - x2)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 \<ge> x2) = (y1 \<ge> y2))"
  by (metis diff_ge_0_iff_ge linorder_not_le mult_less_0_iff not_less_iff_gr_or_eq zero_less_mult_iff)

lemma alethe_nat_embedding[no_atp]:
 "\<exists>x. x \<ge> 0 \<and> (y::nat) = nat (x::int)"
  using int_eq_iff by blast

lemma alethe_nat_embedding2[no_atp]:
 "int (nat (Num.numeral_class.numeral n)) \<equiv> numeral n"
  by simp

lemma alethe_nat_embedding_all[no_atp]:
 "(\<forall>(x::nat). P x) = (\<forall>(x::int). x \<ge> 0 \<longrightarrow> P (nat x))"
  using all_nat by simp_all

lemma alethe_nat_embedding_ex[no_atp]:
 "(\<exists>(x::nat). P x) = (\<exists>(x::int). x \<ge> 0 \<and> P (nat x))"
  using ex_nat by simp

lemma int_nat_embedding_preproc_all[no_atp]:
 "(\<forall>(x::nat) . P x) \<equiv> (\<forall>(x::int). x \<ge> 0 \<longrightarrow> P (nat x))"
  using all_nat by simp

lemma int_nat_embedding_preproc_ex[no_atp]:
 "(\<exists>(x::nat). P x) \<equiv> (\<exists>(x::int). x \<ge> 0 \<and> P (nat x))"
  using ex_nat by auto
context 
begin
qualified definition lift_The :: "(int \<Rightarrow> bool) \<Rightarrow> int" where
  "lift_The Q = int (The (\<lambda>n::nat. Q (int n)))"
lemma int_nat_embedding_preproc_the[no_atp]:
 "(The (P::nat \<Rightarrow> bool)) \<equiv> nat (lift_The (\<lambda>z::int. 0 \<le> z \<and> P (nat z)))"
  by (simp add: lift_The_def)

lemma alethe_nat_embedding_all_new[no_atp]:
"(\<forall>x . (\<exists>x'. (((x::nat) = nat (x'::int) \<and> 0 \<le> x' ) \<and> P x = P' x')))
\<Longrightarrow> (\<forall>x::nat. P x) = (\<forall>x'::int. x' \<ge> 0 \<longrightarrow> P' x')"
  apply simp
  apply standard+
  subgoal using eq_nat_nat_iff by blast
  by blast

lemma alethe_nat_embedding_all2[no_atp]:
 "(\<forall>(x::int) \<ge> 0. int (nat x) = x)"
  using all_nat by simp

lemma alethe_nat_embedding_ex2[no_atp]:
 "(\<exists>(x::int). x \<ge> 0 \<and> int (nat x) = x)"
  using ex_nat by auto

lemma alethe_nat_embedding_all3[no_atp]:
 "P (int (nat x)) \<Longrightarrow> x \<ge> 0 \<Longrightarrow> P x"
  using all_nat by simp

lemma smt_lift_int_nat[no_atp]:
 "int (nat 0) \<equiv> 0"
 "int (nat 1) \<equiv> 1"
  by simp_all

lemma smt_natasint_lift_nat_embedding[no_atp]:
  \<open>x \<ge> 0 \<Longrightarrow> int (nat x) = x\<close>
  by simp

lemma smt_natasint_lift_nat_embedding'[no_atp]:
  \<open>x \<ge> 0 \<Longrightarrow> int (nat x) \<equiv> x\<close>
  by simp

lemma smt_natasint_lift_nat_eq[no_atp]:
  fixes a b :: int
  shows \<open>0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> nat a = nat b \<equiv> a = b\<close>
  by (simp add: nat_eq_iff)

lemma alethe_onepoint[no_atp]:
  \<open>(\<And>a. P a = Q a) \<Longrightarrow> (\<forall>a. P a) = (\<forall>a. Q a)\<close>
  \<open>(\<And>a. P' a = Q') \<Longrightarrow> (\<forall>a. P' a) = Q'\<close>
  \<open>(\<And>a. P a = Q a) \<Longrightarrow> (\<exists>a. P a) = (\<exists>a. Q a)\<close>
  \<open>(\<And>a. P' a = Q') \<Longrightarrow> (\<exists>a. P' a) = Q'\<close>
  by auto

lemma alethe_onepoint_simp[no_atp]:
  \<open>(\<forall>x. a = b \<and> P x \<longrightarrow> Q x) \<longleftrightarrow> (a = b \<longrightarrow> (\<forall>x. P x \<longrightarrow> Q x))\<close>
  by auto

lemma alethe_rewrite_in_imp[no_atp]:
  \<open>((a::'a) = (b::'a) \<equiv> P') \<Longrightarrow> (P' \<Longrightarrow> P = Q) \<Longrightarrow> (a = b \<longrightarrow> P) \<equiv> (P' \<longrightarrow> Q)\<close>
  by auto

lemma alethe_imp_commute[no_atp]: \<open>(a \<longrightarrow> b \<longrightarrow> q) = (b \<longrightarrow> a \<longrightarrow> q)\<close>
  by auto

end

named_theorems nat_normalized_input \<open>Theorems required to replay nat operators embedded into lifted int versions\<close>
named_theorems cvc5_normalized_input \<open>Theorems required to replay
our more complicated translations\<close>

named_theorems cvc5_holes_simp \<open>Simplification theorems for holes\<close>
named_theorems cvc5_holes_pre \<open>Theorems applied for holes\<close>

named_theorems simplify_translation \<open>Lemmas to normalize the assertions before translation. When an operator (such as a constant) appears the simplifier is called and uses this set\<close>
lemmas [simplify_translation] = arith_simps more_arith_simps

named_theorems alethe_poly_norm \<open>Extra theorems for poly norm.\<close>
lemmas [alethe_poly_norm] = mult_1_right mult_1_left

named_theorems alethe_aci_simp \<open>Extra theorems for aci simp\<close>

lemma alethe_onepoint2_all[no_atp]:
  assumes \<open>\<And>x. x = t \<Longrightarrow> P t = Q\<close> \<open>\<And>x. P x = (x = t \<longrightarrow> P x)\<close>
  shows \<open>(\<forall>x. P x) = Q\<close>
  by (use assms in metis)+

lemma alethe_onepoint2_ex[no_atp]:
  assumes \<open>\<And>x. x = t \<Longrightarrow> P t = Q\<close> \<open>\<And>x. P x = (x = t \<and> P x)\<close>
  shows \<open>(\<exists>x. P x) = Q\<close>
  by (use assms in metis)+

lemmas alethe_poly_simp_rel_simps[no_atp] =
   less_divide_eq_numeral1
   less_numeral_simps alethe_div_simplify zero_less_one
   not_one_less_zero neg_0_less_iff_less
   Parity.semiring_parity_class.odd_numeral
   Parity.semiring_parity_class.odd_one

named_theorems alethe_poly_simp_rel_bv_simps \<open>Extra theorems for poly simp rel for bv\<close>

lemma alethe_arg_cong0[no_atp]: \<open>f = g \<Longrightarrow> f a = f a\<close>
  by (rule arg_cong)

lemma alethe_arg_cong[no_atp]: \<open>f = g \<Longrightarrow> a = b \<Longrightarrow> f a = g b\<close>
  by (auto)

context
begin

qualified definition alethe_Box :: \<open>bool \<Rightarrow> bool\<close> where
  \<open>alethe_Box P = P\<close>

qualified lemma alethe_Box[no_atp]:
  \<open>P \<equiv> alethe_Box P\<close>
  unfolding alethe_Box_def
  by auto

qualified lemma alethe_Box_def2[no_atp]:
  \<open>alethe_Box P \<equiv> P\<close>
  unfolding alethe_Box_def
  by auto

qualified definition alethe_id :: \<open>'a \<Rightarrow> 'a\<close> where
  \<open>alethe_id x = x\<close>

end


named_theorems rare_simplify_temp \<open>Theorems to reconstruct bitvector theorems concerning list
                                  functions, e.g. take.\<close>

named_theorems cvc_evaluate \<open>Theorems to reconstruct evaluate steps in cvc5 proofs\<close>
named_theorems cvc_evaluate_bv \<open>Theorems to reconstruct bit-vector evaluate steps in cvc5 proofs\<close>

lemmas cvc_arith_rewrite_defs = SMT.z3div_def linorder_not_le alethe_comp_simplify1
add1_zle_eq


subsection \<open>Setup\<close>

ML_file \<open>Tools/SMT/smt_util.ML\<close>
ML_file \<open>Tools/SMT/smt_failure.ML\<close>
ML_file \<open>Tools/SMT/smt_config.ML\<close>
ML_file \<open>Tools/SMT/smt_builtin.ML\<close>
ML_file \<open>Tools/SMT/smt_datatypes.ML\<close>
ML_file \<open>Tools/SMT/smt_normalize.ML\<close>
ML_file \<open>Tools/SMT/smt_translate.ML\<close>
ML_file \<open>Tools/SMT/smt_parser_util.ML\<close>
ML_file \<open>Tools/SMT/smtlib.ML\<close>
ML_file \<open>Tools/SMT/smtlib_interface.ML\<close>
ML_file \<open>Tools/SMT/smtlib_proof.ML\<close>
ML_file \<open>Tools/SMT/smtlib_isar.ML\<close>
ML_file \<open>Tools/SMT/smt_solver.ML\<close>

(*z3 parsing*)
ML_file \<open>Tools/SMT/z3/z3_proof.ML\<close>
ML_file \<open>Tools/SMT/z3/z3_isar.ML\<close>
(*veriT and cvc5 parsing*)
ML_file \<open>Tools/SMT/alethe/alethe_node.ML\<close>
ML_file \<open>Tools/SMT/alethe/alethe_proof.ML\<close>
ML_file \<open>Tools/SMT/alethe/alethe_smt_problem.ML\<close>
ML_file \<open>Tools/SMT/alethe/alethe_isar.ML\<close>
ML_file \<open>Tools/SMT/alethe/alethe_proof_parse.ML\<close>
ML_file \<open>Tools/SMT/alethe/cvc_interface.ML\<close>
ML_file \<open>Tools/SMT/alethe/cvc_proof_parse.ML\<close>

ML_file \<open>Tools/SMT/conj_disj_perm.ML\<close>
ML_file \<open>Tools/SMT/smt_replay_methods.ML\<close>
ML_file \<open>Tools/SMT/smt_replay.ML\<close>
ML_file \<open>Tools/SMT/smt_replay_arith.ML\<close>

(*z3 replay*)
ML_file \<open>Tools/SMT/z3/z3_interface.ML\<close>
ML_file \<open>Tools/SMT/z3/z3_replay_rules.ML\<close>
ML_file \<open>Tools/SMT/z3/z3_replay_methods.ML\<close>
ML_file \<open>Tools/SMT/z3/z3_replay.ML\<close>

(*veriT and cvc5 replay*)
ML_file \<open>Tools/SMT/alethe/alethe_replay_methods.ML\<close>
ML_file \<open>Tools/SMT/alethe/cvc5_replay_methods.ML\<close>
ML_file \<open>Tools/SMT/alethe/verit_replay_methods.ML\<close>
ML_file \<open>Tools/SMT/alethe/alethe_strategies.ML\<close>
ML_file \<open>Tools/SMT/alethe/alethe_replay.ML\<close>
ML_file \<open>Tools/SMT/alethe/verit_replay.ML\<close>
ML_file \<open>Tools/SMT/alethe/cvc5_replay.ML\<close>

ML_file \<open>Tools/SMT/smt_systems.ML\<close>


subsection \<open>Configuration\<close>

text \<open>
The current configuration can be printed by the command
\<open>smt_status\<close>, which shows the values of most options.
\<close>


subsection \<open>General configuration options\<close>

text \<open>
The option \<open>smt_solver\<close> can be used to change the target SMT
solver. The possible values can be obtained from the \<open>smt_status\<close>
command.
\<close>

declare [[smt_solver = z3]]

text \<open>
Since SMT solvers are potentially nonterminating, there is a timeout
(given in seconds) to restrict their runtime.
\<close>

declare [[smt_timeout = 0]]

text \<open>
SMT solvers apply randomized heuristics. In case a problem is not
solvable by an SMT solver, changing the following option might help.
\<close>

declare [[smt_random_seed = 1]]

text \<open>
In general, the binding to SMT solvers runs as an oracle, i.e, the SMT
solvers are fully trusted without additional checks. The following
option can cause the SMT solver to run in proof-producing mode, giving
a checkable certificate. This is currently implemented only for veriT and
Z3.
\<close>

declare [[smt_oracle = false]]

text \<open>
Each SMT solver provides several command-line options to tweak its
behaviour. They can be passed to the solver by setting the following
options.
\<close>

declare [[cvc4_options = ""]]
declare [[cvc5_options = "--proof-alethe-define-skolems --proof-elim-subtypes --enum-inst"]]
declare [[cvc5_proof_options = "--proof-format-mode=alethe --proof-granularity=dsl-rewrite
                          --proof-mode=full-proof-strict --enum-inst"]]
declare [[verit_options = "--proof-with-sharing"]]
declare [[z3_options = ""]]

text \<open>
The SMT method provides an inference mechanism to detect simple triggers
in quantified formulas, which might increase the number of problems
solvable by SMT solvers (note: triggers guide quantifier instantiations
in the SMT solver). To turn it on, set the following option.
\<close>

declare [[smt_infer_triggers = false]]

text \<open>
Enable the following options to use built-in support for datatypes and codatatypes.\<close>

declare [[smt_native_datatypes = false]]
declare [[smt_native_codatatypes = false]]

text \<open>
Enable the following option to use built-in support for div/mod, datatypes,
and records in Z3. Currently, this is implemented only in oracle mode.
\<close>

declare [[z3_extensions = false]]


subsection \<open>Certificates\<close>

text \<open>
By setting the option \<open>smt_certificates\<close> to the name of a file,
all following applications of an SMT solver are cached in that file.
Any further application of the same SMT solver (using the very same
configuration) re-uses the cached certificate instead of invoking the
solver. An empty string disables caching certificates.

The filename should be given as an explicit path. It is good
practice to use the name of the current theory (with ending
\<open>.certs\<close> instead of \<open>.thy\<close>) as the certificates file.
Certificate files should be used at most once in a certain theory context,
to avoid race conditions with other concurrent accesses.
\<close>

declare [[smt_certificates = ""]]

text \<open>
The option \<open>smt_read_only_certificates\<close> controls whether only
stored certificates should be used or invocation of an SMT solver
is allowed. When set to \<open>true\<close>, no SMT solver will ever be
invoked and only the existing certificates found in the configured
cache are used;  when set to \<open>false\<close> and there is no cached
certificate for some proposition, then the configured SMT solver is
invoked.
\<close>

declare [[smt_read_only_certificates = false]]


subsection \<open>Tracing\<close>

text \<open>
The SMT method, when applied, traces important information. To
make it entirely silent, set the following option to \<open>false\<close>.
\<close>

declare [[smt_verbose = true]]

text \<open>
For tracing the generated problem file given to the SMT solver as
well as the returned result of the solver, the option
\<open>smt_trace\<close> should be set to \<open>true\<close>.
\<close>

declare [[smt_trace = false]]


subsection \<open>Schematic rules for Z3 proof reconstruction\<close>

text \<open>
Several prof rules of Z3 are not very well documented. There are two
lemma groups which can turn failing Z3 proof reconstruction attempts
into succeeding ones: the facts in \<open>z3_rule\<close> are tried prior to
any implemented reconstruction procedure for all uncertain Z3 proof
rules;  the facts in \<open>z3_simp\<close> are only fed to invocations of
the simplifier when reconstructing theory-specific proof steps.
\<close>

lemmas [z3_rule] =
  refl eq_commute conj_commute disj_commute simp_thms nnf_simps
  ring_distribs field_simps times_divide_eq_right times_divide_eq_left
  if_True if_False not_not
  NO_MATCH_def

lemma [z3_rule]:
  "(P \<and> Q) = (\<not> (\<not> P \<or> \<not> Q))"
  "(P \<and> Q) = (\<not> (\<not> Q \<or> \<not> P))"
  "(\<not> P \<and> Q) = (\<not> (P \<or> \<not> Q))"
  "(\<not> P \<and> Q) = (\<not> (\<not> Q \<or> P))"
  "(P \<and> \<not> Q) = (\<not> (\<not> P \<or> Q))"
  "(P \<and> \<not> Q) = (\<not> (Q \<or> \<not> P))"
  "(\<not> P \<and> \<not> Q) = (\<not> (P \<or> Q))"
  "(\<not> P \<and> \<not> Q) = (\<not> (Q \<or> P))"
  by auto

lemma [z3_rule]:
  "(P \<longrightarrow> Q) = (Q \<or> \<not> P)"
  "(\<not> P \<longrightarrow> Q) = (P \<or> Q)"
  "(\<not> P \<longrightarrow> Q) = (Q \<or> P)"
  "(True \<longrightarrow> P) = P"
  "(P \<longrightarrow> True) = True"
  "(False \<longrightarrow> P) = True"
  "(P \<longrightarrow> P) = True"
  "(\<not> (A \<longleftrightarrow> \<not> B)) \<longleftrightarrow> (A \<longleftrightarrow> B)"
  by auto

lemma [z3_rule]:
  "((P = Q) \<longrightarrow> R) = (R \<or> (Q = (\<not> P)))"
  by auto

lemma [z3_rule]:
  "(\<not> True) = False"
  "(\<not> False) = True"
  "(x = x) = True"
  "(P = True) = P"
  "(True = P) = P"
  "(P = False) = (\<not> P)"
  "(False = P) = (\<not> P)"
  "((\<not> P) = P) = False"
  "(P = (\<not> P)) = False"
  "((\<not> P) = (\<not> Q)) = (P = Q)"
  "\<not> (P = (\<not> Q)) = (P = Q)"
  "\<not> ((\<not> P) = Q) = (P = Q)"
  "(P \<noteq> Q) = (Q = (\<not> P))"
  "(P = Q) = ((\<not> P \<or> Q) \<and> (P \<or> \<not> Q))"
  "(P \<noteq> Q) = ((\<not> P \<or> \<not> Q) \<and> (P \<or> Q))"
  by auto

lemma [z3_rule]:
  "(if P then P else \<not> P) = True"
  "(if \<not> P then \<not> P else P) = True"
  "(if P then True else False) = P"
  "(if P then False else True) = (\<not> P)"
  "(if P then Q else True) = ((\<not> P) \<or> Q)"
  "(if P then Q else True) = (Q \<or> (\<not> P))"
  "(if P then Q else \<not> Q) = (P = Q)"
  "(if P then Q else \<not> Q) = (Q = P)"
  "(if P then \<not> Q else Q) = (P = (\<not> Q))"
  "(if P then \<not> Q else Q) = ((\<not> Q) = P)"
  "(if \<not> P then x else y) = (if P then y else x)"
  "(if P then (if Q then x else y) else x) = (if P \<and> (\<not> Q) then y else x)"
  "(if P then (if Q then x else y) else x) = (if (\<not> Q) \<and> P then y else x)"
  "(if P then (if Q then x else y) else y) = (if P \<and> Q then x else y)"
  "(if P then (if Q then x else y) else y) = (if Q \<and> P then x else y)"
  "(if P then x else if P then y else z) = (if P then x else z)"
  "(if P then x else if Q then x else y) = (if P \<or> Q then x else y)"
  "(if P then x else if Q then x else y) = (if Q \<or> P then x else y)"
  "(if P then x = y else x = z) = (x = (if P then y else z))"
  "(if P then x = y else y = z) = (y = (if P then x else z))"
  "(if P then x = y else z = y) = (y = (if P then x else z))"
  by auto

lemma [z3_rule]:
  "0 + (x::int) = x"
  "x + 0 = x"
  "x + x = 2 * x"
  "0 * x = 0"
  "1 * x = x"
  "x + y = y + x"
  by auto

lemma [z3_rule]: (* for def-axiom *)
  "P = Q \<or> P \<or> Q"
  "P = Q \<or> \<not> P \<or> \<not> Q"
  "(\<not> P) = Q \<or> \<not> P \<or> Q"
  "(\<not> P) = Q \<or> P \<or> \<not> Q"
  "P = (\<not> Q) \<or> \<not> P \<or> Q"
  "P = (\<not> Q) \<or> P \<or> \<not> Q"
  "P \<noteq> Q \<or> P \<or> \<not> Q"
  "P \<noteq> Q \<or> \<not> P \<or> Q"
  "P \<noteq> (\<not> Q) \<or> P \<or> Q"
  "(\<not> P) \<noteq> Q \<or> P \<or> Q"
  "P \<or> Q \<or> P \<noteq> (\<not> Q)"
  "P \<or> Q \<or> (\<not> P) \<noteq> Q"
  "P \<or> \<not> Q \<or> P \<noteq> Q"
  "\<not> P \<or> Q \<or> P \<noteq> Q"
  "P \<or> y = (if P then x else y)"
  "P \<or> (if P then x else y) = y"
  "\<not> P \<or> x = (if P then x else y)"
  "\<not> P \<or> (if P then x else y) = x"
  "P \<or> R \<or> \<not> (if P then Q else R)"
  "\<not> P \<or> Q \<or> \<not> (if P then Q else R)"
  "\<not> (if P then Q else R) \<or> \<not> P \<or> Q"
  "\<not> (if P then Q else R) \<or> P \<or> R"
  "(if P then Q else R) \<or> \<not> P \<or> \<not> Q"
  "(if P then Q else R) \<or> P \<or> \<not> R"
  "(if P then \<not> Q else R) \<or> \<not> P \<or> Q"
  "(if P then Q else \<not> R) \<or> P \<or> R"
  by auto

hide_type (open) symb_list pattern
hide_const (open) Symb_Nil Symb_Cons trigger pat nopat fun_app z3div z3mod

declare[[smt_cvc_alethe = true]]

end
