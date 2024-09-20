(*  Title:      Sequents/LK0.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

There may be printing problems if a seqent is in expanded normal form
(eta-expanded, beta-contracted).
*)

section \<open>Classical First-Order Sequent Calculus\<close>

theory LK0
imports Sequents
begin

setup \<open>Proofterm.set_preproc (Proof_Rewrite_Rules.standard_preproc [])\<close>

class "term"
default_sort "term"

consts

  Trueprop       :: "two_seqi"

  True         :: o
  False        :: o
  equal        :: "['a,'a] \<Rightarrow> o"     (infixl \<open>=\<close> 50)
  Not          :: "o \<Rightarrow> o"           (\<open>\<not> _\<close> [40] 40)
  conj         :: "[o,o] \<Rightarrow> o"       (infixr \<open>\<and>\<close> 35)
  disj         :: "[o,o] \<Rightarrow> o"       (infixr \<open>\<or>\<close> 30)
  imp          :: "[o,o] \<Rightarrow> o"       (infixr \<open>\<longrightarrow>\<close> 25)
  iff          :: "[o,o] \<Rightarrow> o"       (infixr \<open>\<longleftrightarrow>\<close> 25)
  The          :: "('a \<Rightarrow> o) \<Rightarrow> 'a"  (binder \<open>THE \<close> 10)
  All          :: "('a \<Rightarrow> o) \<Rightarrow> o"   (binder \<open>\<forall>\<close> 10)
  Ex           :: "('a \<Rightarrow> o) \<Rightarrow> o"   (binder \<open>\<exists>\<close> 10)

syntax
 "_Trueprop"    :: "two_seqe" (\<open>((_)/ \<turnstile> (_))\<close> [6,6] 5)

parse_translation \<open>[(\<^syntax_const>\<open>_Trueprop\<close>, K (two_seq_tr \<^const_syntax>\<open>Trueprop\<close>))]\<close>
print_translation \<open>[(\<^const_syntax>\<open>Trueprop\<close>, K (two_seq_tr' \<^syntax_const>\<open>_Trueprop\<close>))]\<close>

abbreviation
  not_equal  (infixl \<open>\<noteq>\<close> 50) where
  "x \<noteq> y \<equiv> \<not> (x = y)"

axiomatization where

  (*Structural rules: contraction, thinning, exchange [Soren Heilmann] *)

  contRS: "$H \<turnstile> $E, $S, $S, $F \<Longrightarrow> $H \<turnstile> $E, $S, $F" and
  contLS: "$H, $S, $S, $G \<turnstile> $E \<Longrightarrow> $H, $S, $G \<turnstile> $E" and

  thinRS: "$H \<turnstile> $E, $F \<Longrightarrow> $H \<turnstile> $E, $S, $F" and
  thinLS: "$H, $G \<turnstile> $E \<Longrightarrow> $H, $S, $G \<turnstile> $E" and

  exchRS: "$H \<turnstile> $E, $R, $S, $F \<Longrightarrow> $H \<turnstile> $E, $S, $R, $F" and
  exchLS: "$H, $R, $S, $G \<turnstile> $E \<Longrightarrow> $H, $S, $R, $G \<turnstile> $E" and

  cut:   "\<lbrakk>$H \<turnstile> $E, P;  $H, P \<turnstile> $E\<rbrakk> \<Longrightarrow> $H \<turnstile> $E" and

  (*Propositional rules*)

  basic: "$H, P, $G \<turnstile> $E, P, $F" and

  conjR: "\<lbrakk>$H\<turnstile> $E, P, $F;  $H\<turnstile> $E, Q, $F\<rbrakk> \<Longrightarrow> $H\<turnstile> $E, P \<and> Q, $F" and
  conjL: "$H, P, Q, $G \<turnstile> $E \<Longrightarrow> $H, P \<and> Q, $G \<turnstile> $E" and

  disjR: "$H \<turnstile> $E, P, Q, $F \<Longrightarrow> $H \<turnstile> $E, P \<or> Q, $F" and
  disjL: "\<lbrakk>$H, P, $G \<turnstile> $E;  $H, Q, $G \<turnstile> $E\<rbrakk> \<Longrightarrow> $H, P \<or> Q, $G \<turnstile> $E" and

  impR:  "$H, P \<turnstile> $E, Q, $F \<Longrightarrow> $H \<turnstile> $E, P \<longrightarrow> Q, $F" and
  impL:  "\<lbrakk>$H,$G \<turnstile> $E,P;  $H, Q, $G \<turnstile> $E\<rbrakk> \<Longrightarrow> $H, P \<longrightarrow> Q, $G \<turnstile> $E" and

  notR:  "$H, P \<turnstile> $E, $F \<Longrightarrow> $H \<turnstile> $E, \<not> P, $F" and
  notL:  "$H, $G \<turnstile> $E, P \<Longrightarrow> $H, \<not> P, $G \<turnstile> $E" and

  FalseL: "$H, False, $G \<turnstile> $E" and

  True_def: "True \<equiv> False \<longrightarrow> False" and
  iff_def:  "P \<longleftrightarrow> Q \<equiv> (P \<longrightarrow> Q) \<and> (Q \<longrightarrow> P)"

axiomatization where
  (*Quantifiers*)

  allR:  "(\<And>x. $H \<turnstile> $E, P(x), $F) \<Longrightarrow> $H \<turnstile> $E, \<forall>x. P(x), $F" and
  allL:  "$H, P(x), $G, \<forall>x. P(x) \<turnstile> $E \<Longrightarrow> $H, \<forall>x. P(x), $G \<turnstile> $E" and

  exR:   "$H \<turnstile> $E, P(x), $F, \<exists>x. P(x) \<Longrightarrow> $H \<turnstile> $E, \<exists>x. P(x), $F" and
  exL:   "(\<And>x. $H, P(x), $G \<turnstile> $E) \<Longrightarrow> $H, \<exists>x. P(x), $G \<turnstile> $E" and

  (*Equality*)
  refl:  "$H \<turnstile> $E, a = a, $F" and
  subst: "\<And>G H E. $H(a), $G(a) \<turnstile> $E(a) \<Longrightarrow> $H(b), a=b, $G(b) \<turnstile> $E(b)"

  (* Reflection *)

axiomatization where
  eq_reflection:  "\<turnstile> x = y \<Longrightarrow> (x \<equiv> y)" and
  iff_reflection: "\<turnstile> P \<longleftrightarrow> Q \<Longrightarrow> (P \<equiv> Q)"

  (*Descriptions*)

axiomatization where
  The: "\<lbrakk>$H \<turnstile> $E, P(a), $F;  \<And>x.$H, P(x) \<turnstile> $E, x=a, $F\<rbrakk> \<Longrightarrow>
         $H \<turnstile> $E, P(THE x. P(x)), $F"

definition If :: "[o, 'a, 'a] \<Rightarrow> 'a" (\<open>(if (_)/ then (_)/ else (_))\<close> 10)
  where "If(P,x,y) \<equiv> THE z::'a. (P \<longrightarrow> z = x) \<and> (\<not> P \<longrightarrow> z = y)"


(** Structural Rules on formulas **)

(*contraction*)

lemma contR: "$H \<turnstile> $E, P, P, $F \<Longrightarrow> $H \<turnstile> $E, P, $F"
  by (rule contRS)

lemma contL: "$H, P, P, $G \<turnstile> $E \<Longrightarrow> $H, P, $G \<turnstile> $E"
  by (rule contLS)

(*thinning*)

lemma thinR: "$H \<turnstile> $E, $F \<Longrightarrow> $H \<turnstile> $E, P, $F"
  by (rule thinRS)

lemma thinL: "$H, $G \<turnstile> $E \<Longrightarrow> $H, P, $G \<turnstile> $E"
  by (rule thinLS)

(*exchange*)

lemma exchR: "$H \<turnstile> $E, Q, P, $F \<Longrightarrow> $H \<turnstile> $E, P, Q, $F"
  by (rule exchRS)

lemma exchL: "$H, Q, P, $G \<turnstile> $E \<Longrightarrow> $H, P, Q, $G \<turnstile> $E"
  by (rule exchLS)

ML \<open>
(*Cut and thin, replacing the right-side formula*)
fun cutR_tac ctxt s i =
  Rule_Insts.res_inst_tac ctxt [((("P", 0), Position.none), s)] [] @{thm cut} i THEN
  resolve_tac ctxt @{thms thinR} i

(*Cut and thin, replacing the left-side formula*)
fun cutL_tac ctxt s i =
  Rule_Insts.res_inst_tac ctxt [((("P", 0), Position.none), s)] [] @{thm cut} i THEN
  resolve_tac ctxt @{thms thinL} (i + 1)
\<close>


(** If-and-only-if rules **)
lemma iffR: "\<lbrakk>$H,P \<turnstile> $E,Q,$F;  $H,Q \<turnstile> $E,P,$F\<rbrakk> \<Longrightarrow> $H \<turnstile> $E, P \<longleftrightarrow> Q, $F"
  apply (unfold iff_def)
  apply (assumption | rule conjR impR)+
  done

lemma iffL: "\<lbrakk>$H,$G \<turnstile> $E,P,Q;  $H,Q,P,$G \<turnstile> $E\<rbrakk> \<Longrightarrow> $H, P \<longleftrightarrow> Q, $G \<turnstile> $E"
  apply (unfold iff_def)
  apply (assumption | rule conjL impL basic)+
  done

lemma iff_refl: "$H \<turnstile> $E, (P \<longleftrightarrow> P), $F"
  apply (rule iffR basic)+
  done

lemma TrueR: "$H \<turnstile> $E, True, $F"
  apply (unfold True_def)
  apply (rule impR)
  apply (rule basic)
  done

(*Descriptions*)
lemma the_equality:
  assumes p1: "$H \<turnstile> $E, P(a), $F"
    and p2: "\<And>x. $H, P(x) \<turnstile> $E, x=a, $F"
  shows "$H \<turnstile> $E, (THE x. P(x)) = a, $F"
  apply (rule cut)
   apply (rule_tac [2] p2)
  apply (rule The, rule thinR, rule exchRS, rule p1)
  apply (rule thinR, rule exchRS, rule p2)
  done


(** Weakened quantifier rules.  Incomplete, they let the search terminate.**)

lemma allL_thin: "$H, P(x), $G \<turnstile> $E \<Longrightarrow> $H, \<forall>x. P(x), $G \<turnstile> $E"
  apply (rule allL)
  apply (erule thinL)
  done

lemma exR_thin: "$H \<turnstile> $E, P(x), $F \<Longrightarrow> $H \<turnstile> $E, \<exists>x. P(x), $F"
  apply (rule exR)
  apply (erule thinR)
  done

(*The rules of LK*)

lemmas [safe] =
  iffR iffL
  notR notL
  impR impL
  disjR disjL
  conjR conjL
  FalseL TrueR
  refl basic
ML \<open>val prop_pack = Cla.get_pack \<^context>\<close>

lemmas [safe] = exL allR
lemmas [unsafe] = the_equality exR_thin allL_thin
ML \<open>val LK_pack = Cla.get_pack \<^context>\<close>

ML \<open>
  val LK_dup_pack =
    Cla.put_pack prop_pack \<^context>
    |> fold_rev Cla.add_safe @{thms allR exL}
    |> fold_rev Cla.add_unsafe @{thms allL exR the_equality}
    |> Cla.get_pack;
\<close>

method_setup fast_prop =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (Cla.fast_tac (Cla.put_pack prop_pack ctxt)))\<close>

method_setup fast_dup =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (Cla.fast_tac (Cla.put_pack LK_dup_pack ctxt)))\<close>

method_setup best_dup =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (Cla.best_tac (Cla.put_pack LK_dup_pack ctxt)))\<close>

method_setup lem = \<open>
  Attrib.thm >> (fn th => fn ctxt =>
    SIMPLE_METHOD' (fn i =>
      resolve_tac ctxt [@{thm thinR} RS @{thm cut}] i THEN
      REPEAT (resolve_tac ctxt @{thms thinL} i) THEN
      resolve_tac ctxt [th] i))
\<close>


lemma mp_R:
  assumes major: "$H \<turnstile> $E, $F, P \<longrightarrow> Q"
    and minor: "$H \<turnstile> $E, $F, P"
  shows "$H \<turnstile> $E, Q, $F"
  apply (rule thinRS [THEN cut], rule major)
  apply step
  apply (rule thinR, rule minor)
  done

lemma mp_L:
  assumes major: "$H, $G \<turnstile> $E, P \<longrightarrow> Q"
    and minor: "$H, $G, Q \<turnstile> $E"
  shows "$H, P, $G \<turnstile> $E"
  apply (rule thinL [THEN cut], rule major)
  apply step
  apply (rule thinL, rule minor)
  done


(** Two rules to generate left- and right- rules from implications **)

lemma R_of_imp:
  assumes major: "\<turnstile> P \<longrightarrow> Q"
    and minor: "$H \<turnstile> $E, $F, P"
  shows "$H \<turnstile> $E, Q, $F"
  apply (rule mp_R)
   apply (rule_tac [2] minor)
  apply (rule thinRS, rule major [THEN thinLS])
  done

lemma L_of_imp:
  assumes major: "\<turnstile> P \<longrightarrow> Q"
    and minor: "$H, $G, Q \<turnstile> $E"
  shows "$H, P, $G \<turnstile> $E"
  apply (rule mp_L)
   apply (rule_tac [2] minor)
  apply (rule thinRS, rule major [THEN thinLS])
  done

(*Can be used to create implications in a subgoal*)
lemma backwards_impR:
  assumes prem: "$H, $G \<turnstile> $E, $F, P \<longrightarrow> Q"
  shows "$H, P, $G \<turnstile> $E, Q, $F"
  apply (rule mp_L)
   apply (rule_tac [2] basic)
  apply (rule thinR, rule prem)
  done

lemma conjunct1: "\<turnstile>P \<and> Q \<Longrightarrow> \<turnstile>P"
  apply (erule thinR [THEN cut])
  apply fast
  done

lemma conjunct2: "\<turnstile>P \<and> Q \<Longrightarrow> \<turnstile>Q"
  apply (erule thinR [THEN cut])
  apply fast
  done

lemma spec: "\<turnstile> (\<forall>x. P(x)) \<Longrightarrow> \<turnstile> P(x)"
  apply (erule thinR [THEN cut])
  apply fast
  done


(** Equality **)

lemma sym: "\<turnstile> a = b \<longrightarrow> b = a"
  by (safe add!: subst)

lemma trans: "\<turnstile> a = b \<longrightarrow> b = c \<longrightarrow> a = c"
  by (safe add!: subst)

(* Symmetry of equality in hypotheses *)
lemmas symL = sym [THEN L_of_imp]

(* Symmetry of equality in hypotheses *)
lemmas symR = sym [THEN R_of_imp]

lemma transR: "\<lbrakk>$H\<turnstile> $E, $F, a = b;  $H\<turnstile> $E, $F, b=c\<rbrakk> \<Longrightarrow> $H\<turnstile> $E, a = c, $F"
  by (rule trans [THEN R_of_imp, THEN mp_R])

(* Two theorms for rewriting only one instance of a definition:
   the first for definitions of formulae and the second for terms *)

lemma def_imp_iff: "(A \<equiv> B) \<Longrightarrow> \<turnstile> A \<longleftrightarrow> B"
  apply unfold
  apply (rule iff_refl)
  done

lemma meta_eq_to_obj_eq: "(A \<equiv> B) \<Longrightarrow> \<turnstile> A = B"
  apply unfold
  apply (rule refl)
  done


(** if-then-else rules **)

lemma if_True: "\<turnstile> (if True then x else y) = x"
  unfolding If_def by fast

lemma if_False: "\<turnstile> (if False then x else y) = y"
  unfolding If_def by fast

lemma if_P: "\<turnstile> P \<Longrightarrow> \<turnstile> (if P then x else y) = x"
  apply (unfold If_def)
  apply (erule thinR [THEN cut])
  apply fast
  done

lemma if_not_P: "\<turnstile> \<not> P \<Longrightarrow> \<turnstile> (if P then x else y) = y"
  apply (unfold If_def)
  apply (erule thinR [THEN cut])
  apply fast
  done

end
