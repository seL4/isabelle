(*  Title:      FOL/FOL.thy
    Author:     Lawrence C Paulson and Markus Wenzel
*)

section {* Classical first-order logic *}

theory FOL
imports IFOL
keywords "print_claset" "print_induct_rules" :: diag
begin

ML_file "~~/src/Provers/classical.ML"
ML_file "~~/src/Provers/blast.ML"
ML_file "~~/src/Provers/clasimp.ML"


subsection {* The classical axiom *}

axiomatization where
  classical: "(~P ==> P) ==> P"


subsection {* Lemmas and proof tools *}

lemma ccontr: "(\<not> P \<Longrightarrow> False) \<Longrightarrow> P"
  by (erule FalseE [THEN classical])

(*** Classical introduction rules for | and EX ***)

lemma disjCI: "(~Q ==> P) ==> P|Q"
  apply (rule classical)
  apply (assumption | erule meta_mp | rule disjI1 notI)+
  apply (erule notE disjI2)+
  done

(*introduction rule involving only EX*)
lemma ex_classical:
  assumes r: "~(EX x. P(x)) ==> P(a)"
  shows "EX x. P(x)"
  apply (rule classical)
  apply (rule exI, erule r)
  done

(*version of above, simplifying ~EX to ALL~ *)
lemma exCI:
  assumes r: "ALL x. ~P(x) ==> P(a)"
  shows "EX x. P(x)"
  apply (rule ex_classical)
  apply (rule notI [THEN allI, THEN r])
  apply (erule notE)
  apply (erule exI)
  done

lemma excluded_middle: "~P | P"
  apply (rule disjCI)
  apply assumption
  done

lemma case_split [case_names True False]:
  assumes r1: "P ==> Q"
    and r2: "~P ==> Q"
  shows Q
  apply (rule excluded_middle [THEN disjE])
  apply (erule r2)
  apply (erule r1)
  done

ML {*
  fun case_tac ctxt a fixes =
    Rule_Insts.res_inst_tac ctxt [((("P", 0), Position.none), a)] fixes @{thm case_split}
*}

method_setup case_tac = {*
  Args.goal_spec -- Scan.lift (Args.name_inner_syntax -- Parse.for_fixes) >>
    (fn (quant, (s, fixes)) => fn ctxt => SIMPLE_METHOD'' quant (case_tac ctxt s fixes))
*} "case_tac emulation (dynamic instantiation!)"


(*** Special elimination rules *)


(*Classical implies (-->) elimination. *)
lemma impCE:
  assumes major: "P-->Q"
    and r1: "~P ==> R"
    and r2: "Q ==> R"
  shows R
  apply (rule excluded_middle [THEN disjE])
   apply (erule r1)
  apply (rule r2)
  apply (erule major [THEN mp])
  done

(*This version of --> elimination works on Q before P.  It works best for
  those cases in which P holds "almost everywhere".  Can't install as
  default: would break old proofs.*)
lemma impCE':
  assumes major: "P-->Q"
    and r1: "Q ==> R"
    and r2: "~P ==> R"
  shows R
  apply (rule excluded_middle [THEN disjE])
   apply (erule r2)
  apply (rule r1)
  apply (erule major [THEN mp])
  done

(*Double negation law*)
lemma notnotD: "~~P ==> P"
  apply (rule classical)
  apply (erule notE)
  apply assumption
  done

lemma contrapos2:  "[| Q; ~ P ==> ~ Q |] ==> P"
  apply (rule classical)
  apply (drule (1) meta_mp)
  apply (erule (1) notE)
  done

(*** Tactics for implication and contradiction ***)

(*Classical <-> elimination.  Proof substitutes P=Q in
    ~P ==> ~Q    and    P ==> Q  *)
lemma iffCE:
  assumes major: "P<->Q"
    and r1: "[| P; Q |] ==> R"
    and r2: "[| ~P; ~Q |] ==> R"
  shows R
  apply (rule major [unfolded iff_def, THEN conjE])
  apply (elim impCE)
     apply (erule (1) r2)
    apply (erule (1) notE)+
  apply (erule (1) r1)
  done


(*Better for fast_tac: needs no quantifier duplication!*)
lemma alt_ex1E:
  assumes major: "EX! x. P(x)"
    and r: "!!x. [| P(x);  ALL y y'. P(y) & P(y') --> y=y' |] ==> R"
  shows R
  using major
proof (rule ex1E)
  fix x
  assume * : "\<forall>y. P(y) \<longrightarrow> y = x"
  assume "P(x)"
  then show R
  proof (rule r)
    { fix y y'
      assume "P(y)" and "P(y')"
      with * have "x = y" and "x = y'" by - (tactic "IntPr.fast_tac @{context} 1")+
      then have "y = y'" by (rule subst)
    } note r' = this
    show "\<forall>y y'. P(y) \<and> P(y') \<longrightarrow> y = y'" by (intro strip, elim conjE) (rule r')
  qed
qed

lemma imp_elim: "P --> Q ==> (~ R ==> P) ==> (Q ==> R) ==> R"
  by (rule classical) iprover

lemma swap: "~ P ==> (~ R ==> P) ==> R"
  by (rule classical) iprover


section {* Classical Reasoner *}

ML {*
structure Cla = Classical
(
  val imp_elim = @{thm imp_elim}
  val not_elim = @{thm notE}
  val swap = @{thm swap}
  val classical = @{thm classical}
  val sizef = size_of_thm
  val hyp_subst_tacs = [hyp_subst_tac]
);

structure Basic_Classical: BASIC_CLASSICAL = Cla;
open Basic_Classical;
*}

(*Propositional rules*)
lemmas [intro!] = refl TrueI conjI disjCI impI notI iffI
  and [elim!] = conjE disjE impCE FalseE iffCE
ML {* val prop_cs = claset_of @{context} *}

(*Quantifier rules*)
lemmas [intro!] = allI ex_ex1I
  and [intro] = exI
  and [elim!] = exE alt_ex1E
  and [elim] = allE
ML {* val FOL_cs = claset_of @{context} *}

ML {*
  structure Blast = Blast
  (
    structure Classical = Cla
    val Trueprop_const = dest_Const @{const Trueprop}
    val equality_name = @{const_name eq}
    val not_name = @{const_name Not}
    val notE = @{thm notE}
    val ccontr = @{thm ccontr}
    val hyp_subst_tac = Hypsubst.blast_hyp_subst_tac
  );
  val blast_tac = Blast.blast_tac;
*}


lemma ex1_functional: "[| EX! z. P(a,z);  P(a,b);  P(a,c) |] ==> b = c"
  by blast

(* Elimination of True from asumptions: *)
lemma True_implies_equals: "(True ==> PROP P) == PROP P"
proof
  assume "True \<Longrightarrow> PROP P"
  from this and TrueI show "PROP P" .
next
  assume "PROP P"
  then show "PROP P" .
qed

lemma uncurry: "P --> Q --> R ==> P & Q --> R"
  by blast

lemma iff_allI: "(!!x. P(x) <-> Q(x)) ==> (ALL x. P(x)) <-> (ALL x. Q(x))"
  by blast

lemma iff_exI: "(!!x. P(x) <-> Q(x)) ==> (EX x. P(x)) <-> (EX x. Q(x))"
  by blast

lemma all_comm: "(ALL x y. P(x,y)) <-> (ALL y x. P(x,y))" by blast

lemma ex_comm: "(EX x y. P(x,y)) <-> (EX y x. P(x,y))" by blast



(*** Classical simplification rules ***)

(*Avoids duplication of subgoals after expand_if, when the true and false
  cases boil down to the same thing.*)
lemma cases_simp: "(P --> Q) & (~P --> Q) <-> Q" by blast


(*** Miniscoping: pushing quantifiers in
     We do NOT distribute of ALL over &, or dually that of EX over |
     Baaz and Leitsch, On Skolemization and Proof Complexity (1994)
     show that this step can increase proof length!
***)

(*existential miniscoping*)
lemma int_ex_simps:
  "!!P Q. (EX x. P(x) & Q) <-> (EX x. P(x)) & Q"
  "!!P Q. (EX x. P & Q(x)) <-> P & (EX x. Q(x))"
  "!!P Q. (EX x. P(x) | Q) <-> (EX x. P(x)) | Q"
  "!!P Q. (EX x. P | Q(x)) <-> P | (EX x. Q(x))"
  by iprover+

(*classical rules*)
lemma cla_ex_simps:
  "!!P Q. (EX x. P(x) --> Q) <-> (ALL x. P(x)) --> Q"
  "!!P Q. (EX x. P --> Q(x)) <-> P --> (EX x. Q(x))"
  by blast+

lemmas ex_simps = int_ex_simps cla_ex_simps

(*universal miniscoping*)
lemma int_all_simps:
  "!!P Q. (ALL x. P(x) & Q) <-> (ALL x. P(x)) & Q"
  "!!P Q. (ALL x. P & Q(x)) <-> P & (ALL x. Q(x))"
  "!!P Q. (ALL x. P(x) --> Q) <-> (EX x. P(x)) --> Q"
  "!!P Q. (ALL x. P --> Q(x)) <-> P --> (ALL x. Q(x))"
  by iprover+

(*classical rules*)
lemma cla_all_simps:
  "!!P Q. (ALL x. P(x) | Q) <-> (ALL x. P(x)) | Q"
  "!!P Q. (ALL x. P | Q(x)) <-> P | (ALL x. Q(x))"
  by blast+

lemmas all_simps = int_all_simps cla_all_simps


(*** Named rewrite rules proved for IFOL ***)

lemma imp_disj1: "(P-->Q) | R <-> (P-->Q | R)" by blast
lemma imp_disj2: "Q | (P-->R) <-> (P-->Q | R)" by blast

lemma de_Morgan_conj: "(~(P & Q)) <-> (~P | ~Q)" by blast

lemma not_imp: "~(P --> Q) <-> (P & ~Q)" by blast
lemma not_iff: "~(P <-> Q) <-> (P <-> ~Q)" by blast

lemma not_all: "(~ (ALL x. P(x))) <-> (EX x.~P(x))" by blast
lemma imp_all: "((ALL x. P(x)) --> Q) <-> (EX x. P(x) --> Q)" by blast


lemmas meta_simps =
  triv_forall_equality (* prunes params *)
  True_implies_equals  (* prune asms `True' *)

lemmas IFOL_simps =
  refl [THEN P_iff_T] conj_simps disj_simps not_simps
  imp_simps iff_simps quant_simps

lemma notFalseI: "~False" by iprover

lemma cla_simps_misc:
  "~(P&Q) <-> ~P | ~Q"
  "P | ~P"
  "~P | P"
  "~ ~ P <-> P"
  "(~P --> P) <-> P"
  "(~P <-> ~Q) <-> (P<->Q)" by blast+

lemmas cla_simps =
  de_Morgan_conj de_Morgan_disj imp_disj1 imp_disj2
  not_imp not_all not_ex cases_simp cla_simps_misc


ML_file "simpdata.ML"

simproc_setup defined_Ex ("EX x. P(x)") = {* fn _ => Quantifier1.rearrange_ex *}
simproc_setup defined_All ("ALL x. P(x)") = {* fn _ => Quantifier1.rearrange_all *}

ML {*
(*intuitionistic simprules only*)
val IFOL_ss =
  put_simpset FOL_basic_ss @{context}
  addsimps @{thms meta_simps IFOL_simps int_ex_simps int_all_simps}
  addsimprocs [@{simproc defined_All}, @{simproc defined_Ex}]
  |> Simplifier.add_cong @{thm imp_cong}
  |> simpset_of;

(*classical simprules too*)
val FOL_ss =
  put_simpset IFOL_ss @{context}
  addsimps @{thms cla_simps cla_ex_simps cla_all_simps}
  |> simpset_of;
*}

setup {*
  map_theory_simpset (put_simpset FOL_ss) #>
  Simplifier.method_setup Splitter.split_modifiers
*}

ML_file "~~/src/Tools/eqsubst.ML"


subsection {* Other simple lemmas *}

lemma [simp]: "((P-->R) <-> (Q-->R)) <-> ((P<->Q) | R)"
by blast

lemma [simp]: "((P-->Q) <-> (P-->R)) <-> (P --> (Q<->R))"
by blast

lemma not_disj_iff_imp: "~P | Q <-> (P-->Q)"
by blast

(** Monotonicity of implications **)

lemma conj_mono: "[| P1-->Q1; P2-->Q2 |] ==> (P1&P2) --> (Q1&Q2)"
by fast (*or (IntPr.fast_tac 1)*)

lemma disj_mono: "[| P1-->Q1; P2-->Q2 |] ==> (P1|P2) --> (Q1|Q2)"
by fast (*or (IntPr.fast_tac 1)*)

lemma imp_mono: "[| Q1-->P1; P2-->Q2 |] ==> (P1-->P2)-->(Q1-->Q2)"
by fast (*or (IntPr.fast_tac 1)*)

lemma imp_refl: "P-->P"
by (rule impI, assumption)

(*The quantifier monotonicity rules are also intuitionistically valid*)
lemma ex_mono: "(!!x. P(x) --> Q(x)) ==> (EX x. P(x)) --> (EX x. Q(x))"
by blast

lemma all_mono: "(!!x. P(x) --> Q(x)) ==> (ALL x. P(x)) --> (ALL x. Q(x))"
by blast


subsection {* Proof by cases and induction *}

text {* Proper handling of non-atomic rule statements. *}

context
begin

restricted definition "induct_forall(P) \<equiv> \<forall>x. P(x)"
restricted definition "induct_implies(A, B) \<equiv> A \<longrightarrow> B"
restricted definition "induct_equal(x, y) \<equiv> x = y"
restricted definition "induct_conj(A, B) \<equiv> A \<and> B"

lemma induct_forall_eq: "(\<And>x. P(x)) \<equiv> Trueprop(induct_forall(\<lambda>x. P(x)))"
  unfolding atomize_all induct_forall_def .

lemma induct_implies_eq: "(A \<Longrightarrow> B) \<equiv> Trueprop(induct_implies(A, B))"
  unfolding atomize_imp induct_implies_def .

lemma induct_equal_eq: "(x \<equiv> y) \<equiv> Trueprop(induct_equal(x, y))"
  unfolding atomize_eq induct_equal_def .

lemma induct_conj_eq: "(A &&& B) \<equiv> Trueprop(induct_conj(A, B))"
  unfolding atomize_conj induct_conj_def .

lemmas induct_atomize = induct_forall_eq induct_implies_eq induct_equal_eq induct_conj_eq
lemmas induct_rulify [symmetric] = induct_atomize
lemmas induct_rulify_fallback =
  induct_forall_def induct_implies_def induct_equal_def induct_conj_def

text {* Method setup. *}

ML_file "~~/src/Tools/induct.ML"
ML {*
  structure Induct = Induct
  (
    val cases_default = @{thm case_split}
    val atomize = @{thms induct_atomize}
    val rulify = @{thms induct_rulify}
    val rulify_fallback = @{thms induct_rulify_fallback}
    val equal_def = @{thm induct_equal_def}
    fun dest_def _ = NONE
    fun trivial_tac _ _ = no_tac
  );
*}

declare case_split [cases type: o]

end

ML_file "~~/src/Tools/case_product.ML"


hide_const (open) eq

end
