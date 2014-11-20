(*  Title:      HOL/SMT.thy
    Author:     Sascha Boehme, TU Muenchen
*)

section {* Bindings to Satisfiability Modulo Theories (SMT) solvers based on SMT-LIB 2 *}

theory SMT
imports Divides
keywords "smt_status" :: diag
begin

subsection {* A skolemization tactic and proof method *}

lemma choices:
  "\<And>Q. \<forall>x. \<exists>y ya. Q x y ya \<Longrightarrow> \<exists>f fa. \<forall>x. Q x (f x) (fa x)"
  "\<And>Q. \<forall>x. \<exists>y ya yb. Q x y ya yb \<Longrightarrow> \<exists>f fa fb. \<forall>x. Q x (f x) (fa x) (fb x)"
  "\<And>Q. \<forall>x. \<exists>y ya yb yc. Q x y ya yb yc \<Longrightarrow> \<exists>f fa fb fc. \<forall>x. Q x (f x) (fa x) (fb x) (fc x)"
  "\<And>Q. \<forall>x. \<exists>y ya yb yc yd. Q x y ya yb yc yd \<Longrightarrow>
     \<exists>f fa fb fc fd. \<forall>x. Q x (f x) (fa x) (fb x) (fc x) (fd x)"
  "\<And>Q. \<forall>x. \<exists>y ya yb yc yd ye. Q x y ya yb yc yd ye \<Longrightarrow>
     \<exists>f fa fb fc fd fe. \<forall>x. Q x (f x) (fa x) (fb x) (fc x) (fd x) (fe x)"
  "\<And>Q. \<forall>x. \<exists>y ya yb yc yd ye yf. Q x y ya yb yc yd ye yf \<Longrightarrow>
     \<exists>f fa fb fc fd fe ff. \<forall>x. Q x (f x) (fa x) (fb x) (fc x) (fd x) (fe x) (ff x)"
  "\<And>Q. \<forall>x. \<exists>y ya yb yc yd ye yf yg. Q x y ya yb yc yd ye yf yg \<Longrightarrow>
     \<exists>f fa fb fc fd fe ff fg. \<forall>x. Q x (f x) (fa x) (fb x) (fc x) (fd x) (fe x) (ff x) (fg x)"
  by metis+

lemma bchoices:
  "\<And>Q. \<forall>x \<in> S. \<exists>y ya. Q x y ya \<Longrightarrow> \<exists>f fa. \<forall>x \<in> S. Q x (f x) (fa x)"
  "\<And>Q. \<forall>x \<in> S. \<exists>y ya yb. Q x y ya yb \<Longrightarrow> \<exists>f fa fb. \<forall>x \<in> S. Q x (f x) (fa x) (fb x)"
  "\<And>Q. \<forall>x \<in> S. \<exists>y ya yb yc. Q x y ya yb yc \<Longrightarrow> \<exists>f fa fb fc. \<forall>x \<in> S. Q x (f x) (fa x) (fb x) (fc x)"
  "\<And>Q. \<forall>x \<in> S. \<exists>y ya yb yc yd. Q x y ya yb yc yd \<Longrightarrow>
    \<exists>f fa fb fc fd. \<forall>x \<in> S. Q x (f x) (fa x) (fb x) (fc x) (fd x)"
  "\<And>Q. \<forall>x \<in> S. \<exists>y ya yb yc yd ye. Q x y ya yb yc yd ye \<Longrightarrow>
    \<exists>f fa fb fc fd fe. \<forall>x \<in> S. Q x (f x) (fa x) (fb x) (fc x) (fd x) (fe x)"
  "\<And>Q. \<forall>x \<in> S. \<exists>y ya yb yc yd ye yf. Q x y ya yb yc yd ye yf \<Longrightarrow>
    \<exists>f fa fb fc fd fe ff. \<forall>x \<in> S. Q x (f x) (fa x) (fb x) (fc x) (fd x) (fe x) (ff x)"
  "\<And>Q. \<forall>x \<in> S. \<exists>y ya yb yc yd ye yf yg. Q x y ya yb yc yd ye yf yg \<Longrightarrow>
    \<exists>f fa fb fc fd fe ff fg. \<forall>x \<in> S. Q x (f x) (fa x) (fb x) (fc x) (fd x) (fe x) (ff x) (fg x)"
  by metis+

ML {*
fun moura_tac ctxt =
  Atomize_Elim.atomize_elim_tac ctxt THEN'
  SELECT_GOAL (Clasimp.auto_tac (ctxt addSIs @{thms choice choices bchoice bchoices}) THEN
    ALLGOALS (Metis_Tactic.metis_tac (take 1 ATP_Proof_Reconstruct.partial_type_encs)
        ATP_Proof_Reconstruct.default_metis_lam_trans ctxt [] ORELSE'
      blast_tac ctxt))
*}

method_setup moura = {*
 Scan.succeed (SIMPLE_METHOD' o moura_tac)
*} "solve skolemization goals, especially those arising from Z3 proofs"

hide_fact (open) choices bchoices


subsection {* Triggers for quantifier instantiation *}

text {*
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
*}

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


subsection {* Higher-order encoding *}

text {*
Application is made explicit for constants occurring with varying
numbers of arguments. This is achieved by the introduction of the
following constant.
*}

definition fun_app :: "'a \<Rightarrow> 'a" where "fun_app f = f"

text {*
Some solvers support a theory of arrays which can be used to encode
higher-order functions. The following set of lemmas specifies the
properties of such (extensional) arrays.
*}

lemmas array_rules = ext fun_upd_apply fun_upd_same fun_upd_other  fun_upd_upd fun_app_def


subsection {* Normalization *}

lemma case_bool_if[abs_def]: "case_bool x y P = (if P then x else y)"
  by simp

lemmas Ex1_def_raw = Ex1_def[abs_def]
lemmas Ball_def_raw = Ball_def[abs_def]
lemmas Bex_def_raw = Bex_def[abs_def]
lemmas abs_if_raw = abs_if[abs_def]
lemmas min_def_raw = min_def[abs_def]
lemmas max_def_raw = max_def[abs_def]


subsection {* Integer division and modulo for Z3 *}

text {*
The following Z3-inspired definitions are overspecified for the case where @{text "l = 0"}. This
Schönheitsfehler is corrected in the @{text div_as_z3div} and @{text mod_as_z3mod} theorems.
*}

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


subsection {* Setup *}

ML_file "Tools/SMT/smt_util.ML"
ML_file "Tools/SMT/smt_failure.ML"
ML_file "Tools/SMT/smt_config.ML"
ML_file "Tools/SMT/smt_builtin.ML"
ML_file "Tools/SMT/smt_datatypes.ML"
ML_file "Tools/SMT/smt_normalize.ML"
ML_file "Tools/SMT/smt_translate.ML"
ML_file "Tools/SMT/smtlib.ML"
ML_file "Tools/SMT/smtlib_interface.ML"
ML_file "Tools/SMT/smtlib_proof.ML"
ML_file "Tools/SMT/smtlib_isar.ML"
ML_file "Tools/SMT/z3_proof.ML"
ML_file "Tools/SMT/z3_isar.ML"
ML_file "Tools/SMT/smt_solver.ML"
ML_file "Tools/SMT/cvc4_interface.ML"
ML_file "Tools/SMT/cvc4_proof_parse.ML"
ML_file "Tools/SMT/verit_proof.ML"
ML_file "Tools/SMT/verit_isar.ML"
ML_file "Tools/SMT/verit_proof_parse.ML"
ML_file "Tools/SMT/z3_interface.ML"
ML_file "Tools/SMT/z3_replay_util.ML"
ML_file "Tools/SMT/z3_replay_literals.ML"
ML_file "Tools/SMT/z3_replay_rules.ML"
ML_file "Tools/SMT/z3_replay_methods.ML"
ML_file "Tools/SMT/z3_replay.ML"
ML_file "Tools/SMT/smt_systems.ML"

method_setup smt = {*
  Scan.optional Attrib.thms [] >>
    (fn thms => fn ctxt =>
      METHOD (fn facts => HEADGOAL (SMT_Solver.smt_tac ctxt (thms @ facts))))
*} "apply an SMT solver to the current goal"


subsection {* Configuration *}

text {*
The current configuration can be printed by the command
@{text smt_status}, which shows the values of most options.
*}


subsection {* General configuration options *}

text {*
The option @{text smt_solver} can be used to change the target SMT
solver. The possible values can be obtained from the @{text smt_status}
command.

Due to licensing restrictions, Z3 is not enabled by default. Z3 is free
for non-commercial applications and can be enabled by setting Isabelle
system option @{text z3_non_commercial} to @{text yes}.
*}

declare [[smt_solver = z3]]

text {*
Since SMT solvers are potentially nonterminating, there is a timeout
(given in seconds) to restrict their runtime.
*}

declare [[smt_timeout = 20]]

text {*
SMT solvers apply randomized heuristics. In case a problem is not
solvable by an SMT solver, changing the following option might help.
*}

declare [[smt_random_seed = 1]]

text {*
In general, the binding to SMT solvers runs as an oracle, i.e, the SMT
solvers are fully trusted without additional checks. The following
option can cause the SMT solver to run in proof-producing mode, giving
a checkable certificate. This is currently only implemented for Z3.
*}

declare [[smt_oracle = false]]

text {*
Each SMT solver provides several commandline options to tweak its
behaviour. They can be passed to the solver by setting the following
options.
*}

declare [[cvc3_options = ""]]
declare [[cvc4_options = "--full-saturate-quant"]]
declare [[veriT_options = ""]]
declare [[z3_options = ""]]

text {*
The SMT method provides an inference mechanism to detect simple triggers
in quantified formulas, which might increase the number of problems
solvable by SMT solvers (note: triggers guide quantifier instantiations
in the SMT solver). To turn it on, set the following option.
*}

declare [[smt_infer_triggers = false]]

text {*
Enable the following option to use built-in support for datatypes,
codatatypes, and records in CVC4. Currently, this is implemented only
in oracle mode.
*}

declare [[cvc4_extensions = false]]

text {*
Enable the following option to use built-in support for div/mod, datatypes,
and records in Z3. Currently, this is implemented only in oracle mode.
*}

declare [[z3_extensions = false]]


subsection {* Certificates *}

text {*
By setting the option @{text smt_certificates} to the name of a file,
all following applications of an SMT solver a cached in that file.
Any further application of the same SMT solver (using the very same
configuration) re-uses the cached certificate instead of invoking the
solver. An empty string disables caching certificates.

The filename should be given as an explicit path. It is good
practice to use the name of the current theory (with ending
@{text ".certs"} instead of @{text ".thy"}) as the certificates file.
Certificate files should be used at most once in a certain theory context,
to avoid race conditions with other concurrent accesses.
*}

declare [[smt_certificates = ""]]

text {*
The option @{text smt_read_only_certificates} controls whether only
stored certificates are should be used or invocation of an SMT solver
is allowed. When set to @{text true}, no SMT solver will ever be
invoked and only the existing certificates found in the configured
cache are used;  when set to @{text false} and there is no cached
certificate for some proposition, then the configured SMT solver is
invoked.
*}

declare [[smt_read_only_certificates = false]]


subsection {* Tracing *}

text {*
The SMT method, when applied, traces important information. To
make it entirely silent, set the following option to @{text false}.
*}

declare [[smt_verbose = true]]

text {*
For tracing the generated problem file given to the SMT solver as
well as the returned result of the solver, the option
@{text smt_trace} should be set to @{text true}.
*}

declare [[smt_trace = false]]


subsection {* Schematic rules for Z3 proof reconstruction *}

text {*
Several prof rules of Z3 are not very well documented. There are two
lemma groups which can turn failing Z3 proof reconstruction attempts
into succeeding ones: the facts in @{text z3_rule} are tried prior to
any implemented reconstruction procedure for all uncertain Z3 proof
rules;  the facts in @{text z3_simp} are only fed to invocations of
the simplifier when reconstructing theory-specific proof steps.
*}

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
  by auto

lemma [z3_rule]:
  "((P = Q) \<longrightarrow> R) = (R | (Q = (\<not> P)))"
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
  by (auto simp add: mult_2)

lemma [z3_rule]:  (* for def-axiom *)
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

end
