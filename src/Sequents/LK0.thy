(*  Title:      Sequents/LK0.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

There may be printing problems if a seqent is in expanded normal form
(eta-expanded, beta-contracted).
*)

section {* Classical First-Order Sequent Calculus *}

theory LK0
imports Sequents
begin

class "term"
default_sort "term"

consts

  Trueprop       :: "two_seqi"

  True         :: o
  False        :: o
  equal        :: "['a,'a] => o"     (infixl "=" 50)
  Not          :: "o => o"           ("~ _" [40] 40)
  conj         :: "[o,o] => o"       (infixr "&" 35)
  disj         :: "[o,o] => o"       (infixr "|" 30)
  imp          :: "[o,o] => o"       (infixr "-->" 25)
  iff          :: "[o,o] => o"       (infixr "<->" 25)
  The          :: "('a => o) => 'a"  (binder "THE " 10)
  All          :: "('a => o) => o"   (binder "ALL " 10)
  Ex           :: "('a => o) => o"   (binder "EX " 10)

syntax
 "_Trueprop"    :: "two_seqe" ("((_)/ |- (_))" [6,6] 5)

parse_translation {* [(@{syntax_const "_Trueprop"}, K (two_seq_tr @{const_syntax Trueprop}))] *}
print_translation {* [(@{const_syntax Trueprop}, K (two_seq_tr' @{syntax_const "_Trueprop"}))] *}

abbreviation
  not_equal  (infixl "~=" 50) where
  "x ~= y == ~ (x = y)"

notation (xsymbols)
  Not  ("\<not> _" [40] 40) and
  conj  (infixr "\<and>" 35) and
  disj  (infixr "\<or>" 30) and
  imp  (infixr "\<longrightarrow>" 25) and
  iff  (infixr "\<longleftrightarrow>" 25) and
  All  (binder "\<forall>" 10) and
  Ex  (binder "\<exists>" 10) and
  not_equal  (infixl "\<noteq>" 50)

notation (HTML output)
  Not  ("\<not> _" [40] 40) and
  conj  (infixr "\<and>" 35) and
  disj  (infixr "\<or>" 30) and
  All  (binder "\<forall>" 10) and
  Ex  (binder "\<exists>" 10) and
  not_equal  (infixl "\<noteq>" 50)

axiomatization where

  (*Structural rules: contraction, thinning, exchange [Soren Heilmann] *)

  contRS: "$H |- $E, $S, $S, $F ==> $H |- $E, $S, $F" and
  contLS: "$H, $S, $S, $G |- $E ==> $H, $S, $G |- $E" and

  thinRS: "$H |- $E, $F ==> $H |- $E, $S, $F" and
  thinLS: "$H, $G |- $E ==> $H, $S, $G |- $E" and

  exchRS: "$H |- $E, $R, $S, $F ==> $H |- $E, $S, $R, $F" and
  exchLS: "$H, $R, $S, $G |- $E ==> $H, $S, $R, $G |- $E" and

  cut:   "[| $H |- $E, P;  $H, P |- $E |] ==> $H |- $E" and

  (*Propositional rules*)

  basic: "$H, P, $G |- $E, P, $F" and

  conjR: "[| $H|- $E, P, $F;  $H|- $E, Q, $F |] ==> $H|- $E, P&Q, $F" and
  conjL: "$H, P, Q, $G |- $E ==> $H, P & Q, $G |- $E" and

  disjR: "$H |- $E, P, Q, $F ==> $H |- $E, P|Q, $F" and
  disjL: "[| $H, P, $G |- $E;  $H, Q, $G |- $E |] ==> $H, P|Q, $G |- $E" and

  impR:  "$H, P |- $E, Q, $F ==> $H |- $E, P-->Q, $F" and
  impL:  "[| $H,$G |- $E,P;  $H, Q, $G |- $E |] ==> $H, P-->Q, $G |- $E" and

  notR:  "$H, P |- $E, $F ==> $H |- $E, ~P, $F" and
  notL:  "$H, $G |- $E, P ==> $H, ~P, $G |- $E" and

  FalseL: "$H, False, $G |- $E" and

  True_def: "True == False-->False" and
  iff_def:  "P<->Q == (P-->Q) & (Q-->P)"

axiomatization where
  (*Quantifiers*)

  allR:  "(!!x.$H |- $E, P(x), $F) ==> $H |- $E, ALL x. P(x), $F" and
  allL:  "$H, P(x), $G, ALL x. P(x) |- $E ==> $H, ALL x. P(x), $G |- $E" and

  exR:   "$H |- $E, P(x), $F, EX x. P(x) ==> $H |- $E, EX x. P(x), $F" and
  exL:   "(!!x.$H, P(x), $G |- $E) ==> $H, EX x. P(x), $G |- $E" and

  (*Equality*)
  refl:  "$H |- $E, a=a, $F" and
  subst: "\<And>G H E. $H(a), $G(a) |- $E(a) ==> $H(b), a=b, $G(b) |- $E(b)"

  (* Reflection *)

axiomatization where
  eq_reflection:  "|- x=y ==> (x==y)" and
  iff_reflection: "|- P<->Q ==> (P==Q)"

  (*Descriptions*)

axiomatization where
  The: "[| $H |- $E, P(a), $F;  !!x.$H, P(x) |- $E, x=a, $F |] ==>
          $H |- $E, P(THE x. P(x)), $F"

definition If :: "[o, 'a, 'a] => 'a" ("(if (_)/ then (_)/ else (_))" 10)
  where "If(P,x,y) == THE z::'a. (P --> z=x) & (~P --> z=y)"


(** Structural Rules on formulas **)

(*contraction*)

lemma contR: "$H |- $E, P, P, $F ==> $H |- $E, P, $F"
  by (rule contRS)

lemma contL: "$H, P, P, $G |- $E ==> $H, P, $G |- $E"
  by (rule contLS)

(*thinning*)

lemma thinR: "$H |- $E, $F ==> $H |- $E, P, $F"
  by (rule thinRS)

lemma thinL: "$H, $G |- $E ==> $H, P, $G |- $E"
  by (rule thinLS)

(*exchange*)

lemma exchR: "$H |- $E, Q, P, $F ==> $H |- $E, P, Q, $F"
  by (rule exchRS)

lemma exchL: "$H, Q, P, $G |- $E ==> $H, P, Q, $G |- $E"
  by (rule exchLS)

ML {*
(*Cut and thin, replacing the right-side formula*)
fun cutR_tac ctxt s i =
  Rule_Insts.res_inst_tac ctxt [((("P", 0), Position.none), s)] [] @{thm cut} i THEN
  rtac @{thm thinR} i

(*Cut and thin, replacing the left-side formula*)
fun cutL_tac ctxt s i =
  Rule_Insts.res_inst_tac ctxt [((("P", 0), Position.none), s)] [] @{thm cut} i THEN
  rtac @{thm thinL} (i + 1)
*}


(** If-and-only-if rules **)
lemma iffR:
    "[| $H,P |- $E,Q,$F;  $H,Q |- $E,P,$F |] ==> $H |- $E, P <-> Q, $F"
  apply (unfold iff_def)
  apply (assumption | rule conjR impR)+
  done

lemma iffL:
    "[| $H,$G |- $E,P,Q;  $H,Q,P,$G |- $E |] ==> $H, P <-> Q, $G |- $E"
  apply (unfold iff_def)
  apply (assumption | rule conjL impL basic)+
  done

lemma iff_refl: "$H |- $E, (P <-> P), $F"
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
    and p2: "!!x. $H, P(x) |- $E, x=a, $F"
  shows "$H |- $E, (THE x. P(x)) = a, $F"
  apply (rule cut)
   apply (rule_tac [2] p2)
  apply (rule The, rule thinR, rule exchRS, rule p1)
  apply (rule thinR, rule exchRS, rule p2)
  done


(** Weakened quantifier rules.  Incomplete, they let the search terminate.**)

lemma allL_thin: "$H, P(x), $G |- $E ==> $H, ALL x. P(x), $G |- $E"
  apply (rule allL)
  apply (erule thinL)
  done

lemma exR_thin: "$H |- $E, P(x), $F ==> $H |- $E, EX x. P(x), $F"
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
ML {* val prop_pack = Cla.get_pack @{context} *}

lemmas [safe] = exL allR
lemmas [unsafe] = the_equality exR_thin allL_thin
ML {* val LK_pack = Cla.get_pack @{context} *}

ML {*
  val LK_dup_pack =
    Cla.put_pack prop_pack @{context}
    |> fold_rev Cla.add_safe @{thms allR exL}
    |> fold_rev Cla.add_unsafe @{thms allL exR the_equality}
    |> Cla.get_pack;
*}

method_setup fast_prop =
  {* Scan.succeed (fn ctxt => SIMPLE_METHOD' (Cla.fast_tac (Cla.put_pack prop_pack ctxt))) *}

method_setup fast_dup =
  {* Scan.succeed (fn ctxt => SIMPLE_METHOD' (Cla.fast_tac (Cla.put_pack LK_dup_pack ctxt))) *}

method_setup best_dup =
  {* Scan.succeed (fn ctxt => SIMPLE_METHOD' (Cla.best_tac (Cla.put_pack LK_dup_pack ctxt))) *}

method_setup lem = {*
  Attrib.thm >> (fn th => fn _ =>
    SIMPLE_METHOD' (fn i =>
      rtac (@{thm thinR} RS @{thm cut}) i THEN
      REPEAT (rtac @{thm thinL} i) THEN
      rtac th i))
*}


lemma mp_R:
  assumes major: "$H |- $E, $F, P --> Q"
    and minor: "$H |- $E, $F, P"
  shows "$H |- $E, Q, $F"
  apply (rule thinRS [THEN cut], rule major)
  apply step
  apply (rule thinR, rule minor)
  done

lemma mp_L:
  assumes major: "$H, $G |- $E, P --> Q"
    and minor: "$H, $G, Q |- $E"
  shows "$H, P, $G |- $E"
  apply (rule thinL [THEN cut], rule major)
  apply step
  apply (rule thinL, rule minor)
  done


(** Two rules to generate left- and right- rules from implications **)

lemma R_of_imp:
  assumes major: "|- P --> Q"
    and minor: "$H |- $E, $F, P"
  shows "$H |- $E, Q, $F"
  apply (rule mp_R)
   apply (rule_tac [2] minor)
  apply (rule thinRS, rule major [THEN thinLS])
  done

lemma L_of_imp:
  assumes major: "|- P --> Q"
    and minor: "$H, $G, Q |- $E"
  shows "$H, P, $G |- $E"
  apply (rule mp_L)
   apply (rule_tac [2] minor)
  apply (rule thinRS, rule major [THEN thinLS])
  done

(*Can be used to create implications in a subgoal*)
lemma backwards_impR:
  assumes prem: "$H, $G |- $E, $F, P --> Q"
  shows "$H, P, $G |- $E, Q, $F"
  apply (rule mp_L)
   apply (rule_tac [2] basic)
  apply (rule thinR, rule prem)
  done

lemma conjunct1: "|-P&Q ==> |-P"
  apply (erule thinR [THEN cut])
  apply fast
  done

lemma conjunct2: "|-P&Q ==> |-Q"
  apply (erule thinR [THEN cut])
  apply fast
  done

lemma spec: "|- (ALL x. P(x)) ==> |- P(x)"
  apply (erule thinR [THEN cut])
  apply fast
  done


(** Equality **)

lemma sym: "|- a=b --> b=a"
  by (safe add!: subst)

lemma trans: "|- a=b --> b=c --> a=c"
  by (safe add!: subst)

(* Symmetry of equality in hypotheses *)
lemmas symL = sym [THEN L_of_imp]

(* Symmetry of equality in hypotheses *)
lemmas symR = sym [THEN R_of_imp]

lemma transR: "[| $H|- $E, $F, a=b;  $H|- $E, $F, b=c |] ==> $H|- $E, a=c, $F"
  by (rule trans [THEN R_of_imp, THEN mp_R])

(* Two theorms for rewriting only one instance of a definition:
   the first for definitions of formulae and the second for terms *)

lemma def_imp_iff: "(A == B) ==> |- A <-> B"
  apply unfold
  apply (rule iff_refl)
  done

lemma meta_eq_to_obj_eq: "(A == B) ==> |- A = B"
  apply unfold
  apply (rule refl)
  done


(** if-then-else rules **)

lemma if_True: "|- (if True then x else y) = x"
  unfolding If_def by fast

lemma if_False: "|- (if False then x else y) = y"
  unfolding If_def by fast

lemma if_P: "|- P ==> |- (if P then x else y) = x"
  apply (unfold If_def)
  apply (erule thinR [THEN cut])
  apply fast
  done

lemma if_not_P: "|- ~P ==> |- (if P then x else y) = y"
  apply (unfold If_def)
  apply (erule thinR [THEN cut])
  apply fast
  done

end
