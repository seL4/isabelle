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

class "term"
default_sort "term"

consts

  Trueprop       :: "two_seqi"

  True         :: o
  False        :: o
  equal        :: "['a,'a] \<Rightarrow> o"     (infixl "=" 50)
  Not          :: "o \<Rightarrow> o"           ("\<not> _" [40] 40)
  conj         :: "[o,o] \<Rightarrow> o"       (infixr "\<and>" 35)
  disj         :: "[o,o] \<Rightarrow> o"       (infixr "\<or>" 30)
  imp          :: "[o,o] \<Rightarrow> o"       (infixr "\<longrightarrow>" 25)
  iff          :: "[o,o] \<Rightarrow> o"       (infixr "\<longleftrightarrow>" 25)
  The          :: "('a \<Rightarrow> o) \<Rightarrow> 'a"  (binder "THE " 10)
  All          :: "('a \<Rightarrow> o) \<Rightarrow> o"   (binder "\<forall>" 10)
  Ex           :: "('a \<Rightarrow> o) \<Rightarrow> o"   (binder "\<exists>" 10)

syntax
 "_Trueprop"    :: "two_seqe" ("((_)/ |- (_))" [6,6] 5)

parse_translation \<open>[(@{syntax_const "_Trueprop"}, K (two_seq_tr @{const_syntax Trueprop}))]\<close>
print_translation \<open>[(@{const_syntax Trueprop}, K (two_seq_tr' @{syntax_const "_Trueprop"}))]\<close>

abbreviation
  not_equal  (infixl "\<noteq>" 50) where
  "x \<noteq> y \<equiv> \<not> (x = y)"

axiomatization where

  (*Structural rules: contraction, thinning, exchange [Soren Heilmann] *)

  contRS: "$H |- $E, $S, $S, $F \<Longrightarrow> $H |- $E, $S, $F" and
  contLS: "$H, $S, $S, $G |- $E \<Longrightarrow> $H, $S, $G |- $E" and

  thinRS: "$H |- $E, $F \<Longrightarrow> $H |- $E, $S, $F" and
  thinLS: "$H, $G |- $E \<Longrightarrow> $H, $S, $G |- $E" and

  exchRS: "$H |- $E, $R, $S, $F \<Longrightarrow> $H |- $E, $S, $R, $F" and
  exchLS: "$H, $R, $S, $G |- $E \<Longrightarrow> $H, $S, $R, $G |- $E" and

  cut:   "\<lbrakk>$H |- $E, P;  $H, P |- $E\<rbrakk> \<Longrightarrow> $H |- $E" and

  (*Propositional rules*)

  basic: "$H, P, $G |- $E, P, $F" and

  conjR: "\<lbrakk>$H|- $E, P, $F;  $H|- $E, Q, $F\<rbrakk> \<Longrightarrow> $H|- $E, P \<and> Q, $F" and
  conjL: "$H, P, Q, $G |- $E \<Longrightarrow> $H, P \<and> Q, $G |- $E" and

  disjR: "$H |- $E, P, Q, $F \<Longrightarrow> $H |- $E, P \<or> Q, $F" and
  disjL: "\<lbrakk>$H, P, $G |- $E;  $H, Q, $G |- $E\<rbrakk> \<Longrightarrow> $H, P \<or> Q, $G |- $E" and

  impR:  "$H, P |- $E, Q, $F \<Longrightarrow> $H |- $E, P \<longrightarrow> Q, $F" and
  impL:  "\<lbrakk>$H,$G |- $E,P;  $H, Q, $G |- $E\<rbrakk> \<Longrightarrow> $H, P \<longrightarrow> Q, $G |- $E" and

  notR:  "$H, P |- $E, $F \<Longrightarrow> $H |- $E, \<not> P, $F" and
  notL:  "$H, $G |- $E, P \<Longrightarrow> $H, \<not> P, $G |- $E" and

  FalseL: "$H, False, $G |- $E" and

  True_def: "True \<equiv> False \<longrightarrow> False" and
  iff_def:  "P \<longleftrightarrow> Q \<equiv> (P \<longrightarrow> Q) \<and> (Q \<longrightarrow> P)"

axiomatization where
  (*Quantifiers*)

  allR:  "(\<And>x. $H |- $E, P(x), $F) \<Longrightarrow> $H |- $E, \<forall>x. P(x), $F" and
  allL:  "$H, P(x), $G, \<forall>x. P(x) |- $E \<Longrightarrow> $H, \<forall>x. P(x), $G |- $E" and

  exR:   "$H |- $E, P(x), $F, \<exists>x. P(x) \<Longrightarrow> $H |- $E, \<exists>x. P(x), $F" and
  exL:   "(\<And>x. $H, P(x), $G |- $E) \<Longrightarrow> $H, \<exists>x. P(x), $G |- $E" and

  (*Equality*)
  refl:  "$H |- $E, a = a, $F" and
  subst: "\<And>G H E. $H(a), $G(a) |- $E(a) \<Longrightarrow> $H(b), a=b, $G(b) |- $E(b)"

  (* Reflection *)

axiomatization where
  eq_reflection:  "|- x = y \<Longrightarrow> (x \<equiv> y)" and
  iff_reflection: "|- P \<longleftrightarrow> Q \<Longrightarrow> (P \<equiv> Q)"

  (*Descriptions*)

axiomatization where
  The: "\<lbrakk>$H |- $E, P(a), $F;  \<And>x.$H, P(x) |- $E, x=a, $F\<rbrakk> \<Longrightarrow>
         $H |- $E, P(THE x. P(x)), $F"

definition If :: "[o, 'a, 'a] \<Rightarrow> 'a" ("(if (_)/ then (_)/ else (_))" 10)
  where "If(P,x,y) \<equiv> THE z::'a. (P \<longrightarrow> z = x) \<and> (\<not> P \<longrightarrow> z = y)"


(** Structural Rules on formulas **)

(*contraction*)

lemma contR: "$H |- $E, P, P, $F \<Longrightarrow> $H |- $E, P, $F"
  by (rule contRS)

lemma contL: "$H, P, P, $G |- $E \<Longrightarrow> $H, P, $G |- $E"
  by (rule contLS)

(*thinning*)

lemma thinR: "$H |- $E, $F \<Longrightarrow> $H |- $E, P, $F"
  by (rule thinRS)

lemma thinL: "$H, $G |- $E \<Longrightarrow> $H, P, $G |- $E"
  by (rule thinLS)

(*exchange*)

lemma exchR: "$H |- $E, Q, P, $F \<Longrightarrow> $H |- $E, P, Q, $F"
  by (rule exchRS)

lemma exchL: "$H, Q, P, $G |- $E \<Longrightarrow> $H, P, Q, $G |- $E"
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
lemma iffR: "\<lbrakk>$H,P |- $E,Q,$F;  $H,Q |- $E,P,$F\<rbrakk> \<Longrightarrow> $H |- $E, P \<longleftrightarrow> Q, $F"
  apply (unfold iff_def)
  apply (assumption | rule conjR impR)+
  done

lemma iffL: "\<lbrakk>$H,$G |- $E,P,Q;  $H,Q,P,$G |- $E\<rbrakk> \<Longrightarrow> $H, P \<longleftrightarrow> Q, $G |- $E"
  apply (unfold iff_def)
  apply (assumption | rule conjL impL basic)+
  done

lemma iff_refl: "$H |- $E, (P \<longleftrightarrow> P), $F"
  apply (rule iffR basic)+
  done

lemma TrueR: "$H |- $E, True, $F"
  apply (unfold True_def)
  apply (rule impR)
  apply (rule basic)
  done

(*Descriptions*)
lemma the_equality:
  assumes p1: "$H |- $E, P(a), $F"
    and p2: "\<And>x. $H, P(x) |- $E, x=a, $F"
  shows "$H |- $E, (THE x. P(x)) = a, $F"
  apply (rule cut)
   apply (rule_tac [2] p2)
  apply (rule The, rule thinR, rule exchRS, rule p1)
  apply (rule thinR, rule exchRS, rule p2)
  done


(** Weakened quantifier rules.  Incomplete, they let the search terminate.**)

lemma allL_thin: "$H, P(x), $G |- $E \<Longrightarrow> $H, \<forall>x. P(x), $G |- $E"
  apply (rule allL)
  apply (erule thinL)
  done

lemma exR_thin: "$H |- $E, P(x), $F \<Longrightarrow> $H |- $E, \<exists>x. P(x), $F"
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
ML \<open>val prop_pack = Cla.get_pack @{context}\<close>

lemmas [safe] = exL allR
lemmas [unsafe] = the_equality exR_thin allL_thin
ML \<open>val LK_pack = Cla.get_pack @{context}\<close>

ML \<open>
  val LK_dup_pack =
    Cla.put_pack prop_pack @{context}
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
  assumes major: "$H |- $E, $F, P \<longrightarrow> Q"
    and minor: "$H |- $E, $F, P"
  shows "$H |- $E, Q, $F"
  apply (rule thinRS [THEN cut], rule major)
  apply step
  apply (rule thinR, rule minor)
  done

lemma mp_L:
  assumes major: "$H, $G |- $E, P \<longrightarrow> Q"
    and minor: "$H, $G, Q |- $E"
  shows "$H, P, $G |- $E"
  apply (rule thinL [THEN cut], rule major)
  apply step
  apply (rule thinL, rule minor)
  done


(** Two rules to generate left- and right- rules from implications **)

lemma R_of_imp:
  assumes major: "|- P \<longrightarrow> Q"
    and minor: "$H |- $E, $F, P"
  shows "$H |- $E, Q, $F"
  apply (rule mp_R)
   apply (rule_tac [2] minor)
  apply (rule thinRS, rule major [THEN thinLS])
  done

lemma L_of_imp:
  assumes major: "|- P \<longrightarrow> Q"
    and minor: "$H, $G, Q |- $E"
  shows "$H, P, $G |- $E"
  apply (rule mp_L)
   apply (rule_tac [2] minor)
  apply (rule thinRS, rule major [THEN thinLS])
  done

(*Can be used to create implications in a subgoal*)
lemma backwards_impR:
  assumes prem: "$H, $G |- $E, $F, P \<longrightarrow> Q"
  shows "$H, P, $G |- $E, Q, $F"
  apply (rule mp_L)
   apply (rule_tac [2] basic)
  apply (rule thinR, rule prem)
  done

lemma conjunct1: "|-P \<and> Q \<Longrightarrow> |-P"
  apply (erule thinR [THEN cut])
  apply fast
  done

lemma conjunct2: "|-P \<and> Q \<Longrightarrow> |-Q"
  apply (erule thinR [THEN cut])
  apply fast
  done

lemma spec: "|- (\<forall>x. P(x)) \<Longrightarrow> |- P(x)"
  apply (erule thinR [THEN cut])
  apply fast
  done


(** Equality **)

lemma sym: "|- a = b \<longrightarrow> b = a"
  by (safe add!: subst)

lemma trans: "|- a = b \<longrightarrow> b = c \<longrightarrow> a = c"
  by (safe add!: subst)

(* Symmetry of equality in hypotheses *)
lemmas symL = sym [THEN L_of_imp]

(* Symmetry of equality in hypotheses *)
lemmas symR = sym [THEN R_of_imp]

lemma transR: "\<lbrakk>$H|- $E, $F, a = b;  $H|- $E, $F, b=c\<rbrakk> \<Longrightarrow> $H|- $E, a = c, $F"
  by (rule trans [THEN R_of_imp, THEN mp_R])

(* Two theorms for rewriting only one instance of a definition:
   the first for definitions of formulae and the second for terms *)

lemma def_imp_iff: "(A \<equiv> B) \<Longrightarrow> |- A \<longleftrightarrow> B"
  apply unfold
  apply (rule iff_refl)
  done

lemma meta_eq_to_obj_eq: "(A \<equiv> B) \<Longrightarrow> |- A = B"
  apply unfold
  apply (rule refl)
  done


(** if-then-else rules **)

lemma if_True: "|- (if True then x else y) = x"
  unfolding If_def by fast

lemma if_False: "|- (if False then x else y) = y"
  unfolding If_def by fast

lemma if_P: "|- P \<Longrightarrow> |- (if P then x else y) = x"
  apply (unfold If_def)
  apply (erule thinR [THEN cut])
  apply fast
  done

lemma if_not_P: "|- \<not> P \<Longrightarrow> |- (if P then x else y) = y"
  apply (unfold If_def)
  apply (erule thinR [THEN cut])
  apply fast
  done

end
