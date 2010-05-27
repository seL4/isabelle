(*  Title:      HOL/SMT.thy
    Author:     Sascha Boehme, TU Muenchen
*)

header {* Bindings to Satisfiability Modulo Theories (SMT) solvers *}

theory SMT
imports List
uses
  "~~/src/Tools/cache_io.ML"
  ("Tools/SMT/smt_monomorph.ML")
  ("Tools/SMT/smt_normalize.ML")
  ("Tools/SMT/smt_translate.ML")
  ("Tools/SMT/smt_solver.ML")
  ("Tools/SMT/smtlib_interface.ML")
  ("Tools/SMT/z3_proof_parser.ML")
  ("Tools/SMT/z3_proof_tools.ML")
  ("Tools/SMT/z3_proof_literals.ML")
  ("Tools/SMT/z3_proof_reconstruction.ML")
  ("Tools/SMT/z3_model.ML")
  ("Tools/SMT/z3_interface.ML")
  ("Tools/SMT/z3_solver.ML")
  ("Tools/SMT/cvc3_solver.ML")
  ("Tools/SMT/yices_solver.ML")
begin



subsection {* Triggers for quantifier instantiation *}

text {*
Some SMT solvers support triggers for quantifier instantiation.
Each trigger consists of one ore more patterns.  A pattern may either
be a list of positive subterms (each being tagged by "pat"), or a
list of negative subterms (each being tagged by "nopat").

When an SMT solver finds a term matching a positive pattern (a
pattern with positive subterms only), it instantiates the
corresponding quantifier accordingly.  Negative patterns inhibit
quantifier instantiations.  Each pattern should mention all preceding
bound variables.
*}

datatype pattern = Pattern

definition pat :: "'a \<Rightarrow> pattern" where "pat _ = Pattern"
definition nopat :: "'a \<Rightarrow> pattern" where "nopat _ = Pattern"

definition trigger :: "pattern list list \<Rightarrow> bool \<Rightarrow> bool"
where "trigger _ P = P"



subsection {* Higher-order encoding *}

text {*
Application is made explicit for constants occurring with varying
numbers of arguments.  This is achieved by the introduction of the
following constant.
*}

definition fun_app where "fun_app f x = f x"

text {*
Some solvers support a theory of arrays which can be used to encode
higher-order functions.  The following set of lemmas specifies the
properties of such (extensional) arrays.
*}

lemmas array_rules = ext fun_upd_apply fun_upd_same fun_upd_other
  fun_upd_upd fun_app_def



subsection {* First-order logic *}

text {*
Some SMT solvers require a strict separation between formulas and
terms.  When translating higher-order into first-order problems,
all uninterpreted constants (those not builtin in the target solver)
are treated as function symbols in the first-order sense.  Their
occurrences as head symbols in atoms (i.e., as predicate symbols) is
turned into terms by equating such atoms with @{term True} using the
following term-level equation symbol.
*}

definition term_eq :: "bool \<Rightarrow> bool \<Rightarrow> bool" where "term_eq x y = (x = y)"



subsection {* Integer division and modulo for Z3 *}

definition z3div :: "int \<Rightarrow> int \<Rightarrow> int" where
  "z3div k l = (if 0 \<le> l then k div l else -(k div (-l)))"

definition z3mod :: "int \<Rightarrow> int \<Rightarrow> int" where
  "z3mod k l = (if 0 \<le> l then k mod l else k mod (-l))"

lemma div_by_z3div: "k div l = (
     if k = 0 \<or> l = 0 then 0
     else if (0 < k \<and> 0 < l) \<or> (k < 0 \<and> 0 < l) then z3div k l
     else z3div (-k) (-l))"
  by (auto simp add: z3div_def)

lemma mod_by_z3mod: "k mod l = (
     if l = 0 then k
     else if k = 0 then 0
     else if (0 < k \<and> 0 < l) \<or> (k < 0 \<and> 0 < l) then z3mod k l
     else - z3mod (-k) (-l))"
  by (auto simp add: z3mod_def)



subsection {* Setup *}

use "Tools/SMT/smt_monomorph.ML"
use "Tools/SMT/smt_normalize.ML"
use "Tools/SMT/smt_translate.ML"
use "Tools/SMT/smt_solver.ML"
use "Tools/SMT/smtlib_interface.ML"
use "Tools/SMT/z3_interface.ML"
use "Tools/SMT/z3_proof_parser.ML"
use "Tools/SMT/z3_proof_tools.ML"
use "Tools/SMT/z3_proof_literals.ML"
use "Tools/SMT/z3_proof_reconstruction.ML"
use "Tools/SMT/z3_model.ML"
use "Tools/SMT/z3_solver.ML"
use "Tools/SMT/cvc3_solver.ML"
use "Tools/SMT/yices_solver.ML"

setup {*
  SMT_Solver.setup #>
  Z3_Proof_Reconstruction.setup #>
  Z3_Solver.setup #>
  CVC3_Solver.setup #>
  Yices_Solver.setup
*}



subsection {* Configuration *}

text {*
The current configuration can be printed by the command
@{text smt_status}, which shows the values of most options.
*}



subsection {* General configuration options *}

text {*
The option @{text smt_solver} can be used to change the target SMT
solver.  The possible values are @{text cvc3}, @{text yices}, and
@{text z3}.  It is advisable to locally install the selected solver,
although this is not necessary for @{text cvc3} and @{text z3}, which
can also be used over an Internet-based service.

When using local SMT solvers, the path to their binaries should be
declared by setting the following environment variables:
@{text CVC3_SOLVER}, @{text YICES_SOLVER}, and @{text Z3_SOLVER}.
*}

declare [[ smt_solver = z3 ]]

text {*
Since SMT solvers are potentially non-terminating, there is a timeout
(given in seconds) to restrict their runtime.  A value greater than
120 (seconds) is in most cases not advisable.
*}

declare [[ smt_timeout = 20 ]]



subsection {* Certificates *}

text {*
By setting the option @{text smt_certificates} to the name of a file,
all following applications of an SMT solver a cached in that file.
Any further application of the same SMT solver (using the very same
configuration) re-uses the cached certificate instead of invoking the
solver.  An empty string disables caching certificates.

The filename should be given as an explicit path.  It is good
practice to use the name of the current theory (with ending
@{text ".certs"} instead of @{text ".thy"}) as the certificates file.
*}

declare [[ smt_certificates = "" ]]

text {*
The option @{text smt_fixed} controls whether only stored
certificates are should be used or invocation of an SMT solver is
allowed.  When set to @{text true}, no SMT solver will ever be
invoked and only the existing certificates found in the configured
cache are used;  when set to @{text false} and there is no cached
certificate for some proposition, then the configured SMT solver is
invoked.
*}

declare [[ smt_fixed = false ]]



subsection {* Tracing *}

text {*
For tracing the generated problem file given to the SMT solver as
well as the returned result of the solver, the option
@{text smt_trace} should be set to @{text true}.
*}

declare [[ smt_trace = false ]]



subsection {* Z3-specific options *}

text {*
Z3 is the only SMT solver whose proofs are checked (or reconstructed)
in Isabelle (all other solvers are implemented as oracles).  Enabling
or disabling proof reconstruction for Z3 is controlled by the option
@{text z3_proofs}. 
*}

declare [[ z3_proofs = true ]]

text {*
From the set of assumptions given to Z3, those assumptions used in
the proof are traced when the option @{text z3_trace_assms} is set to
@{term true}.
*}

declare [[ z3_trace_assms = false ]]

text {*
Z3 provides several commandline options to tweak its behaviour.  They
can be configured by writing them literally as value for the option
@{text z3_options}.
*}

declare [[ z3_options = "" ]]



subsection {* Schematic rules for Z3 proof reconstruction *}

text {*
Several prof rules of Z3 are not very well documented.  There are two
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

lemma [z3_rule]:
  "(P \<longrightarrow> Q) = (Q \<or> \<not>P)"
  "(\<not>P \<longrightarrow> Q) = (P \<or> Q)"
  "(\<not>P \<longrightarrow> Q) = (Q \<or> P)"
  by auto

lemma [z3_rule]:
  "((P = Q) \<longrightarrow> R) = (R | (Q = (\<not>P)))"
  by auto

lemma [z3_rule]:
  "((\<not>P) = P) = False"
  "(P = (\<not>P)) = False"
  "(P \<noteq> Q) = (Q = (\<not>P))"
  "(P = Q) = ((\<not>P \<or> Q) \<and> (P \<or> \<not>Q))"
  "(P \<noteq> Q) = ((\<not>P \<or> \<not>Q) \<and> (P \<or> Q))"
  by auto

lemma [z3_rule]:
  "(if P then P else \<not>P) = True"
  "(if \<not>P then \<not>P else P) = True"
  "(if P then True else False) = P"
  "(if P then False else True) = (\<not>P)"
  "(if \<not>P then x else y) = (if P then y else x)"
  by auto

lemma [z3_rule]:
  "P = Q \<or> P \<or> Q"
  "P = Q \<or> \<not>P \<or> \<not>Q"
  "(\<not>P) = Q \<or> \<not>P \<or> Q"
  "(\<not>P) = Q \<or> P \<or> \<not>Q"
  "P = (\<not>Q) \<or> \<not>P \<or> Q"
  "P = (\<not>Q) \<or> P \<or> \<not>Q"
  "P \<noteq> Q \<or> P \<or> \<not>Q"
  "P \<noteq> Q \<or> \<not>P \<or> Q"
  "P \<noteq> (\<not>Q) \<or> P \<or> Q"
  "(\<not>P) \<noteq> Q \<or> P \<or> Q"
  "P \<or> Q \<or> P \<noteq> (\<not>Q)"
  "P \<or> Q \<or> (\<not>P) \<noteq> Q"
  "P \<or> \<not>Q \<or> P \<noteq> Q"
  "\<not>P \<or> Q \<or> P \<noteq> Q"
  by auto

lemma [z3_rule]:
  "0 + (x::int) = x"
  "x + 0 = x"
  "0 * x = 0"
  "1 * x = x"
  "x + y = y + x"
  by auto



hide_type (open) pattern
hide_const Pattern term_eq
hide_const (open) trigger pat nopat fun_app z3div z3mod

end
