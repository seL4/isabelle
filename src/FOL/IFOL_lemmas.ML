(*  Title:      FOL/IFOL_lemmas.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Tactics and lemmas for theory IFOL (intuitionistic first-order logic).
*)

(* ML bindings *)

val refl = thm "refl";
val subst = thm "subst";
val conjI = thm "conjI";
val conjunct1 = thm "conjunct1";
val conjunct2 = thm "conjunct2";
val disjI1 = thm "disjI1";
val disjI2 = thm "disjI2";
val disjE = thm "disjE";
val impI = thm "impI";
val mp = thm "mp";
val FalseE = thm "FalseE";
val True_def = thm "True_def";
val not_def = thm "not_def";
val iff_def = thm "iff_def";
val ex1_def = thm "ex1_def";
val allI = thm "allI";
val spec = thm "spec";
val exI = thm "exI";
val exE = thm "exE";
val eq_reflection = thm "eq_reflection";
val iff_reflection = thm "iff_reflection";

structure IFOL =
struct
  val thy = the_context ();
  val refl = refl;
  val subst = subst;
  val conjI = conjI;
  val conjunct1 = conjunct1;
  val conjunct2 = conjunct2;
  val disjI1 = disjI1;
  val disjI2 = disjI2;
  val disjE = disjE;
  val impI = impI;
  val mp = mp;
  val FalseE = FalseE;
  val True_def = True_def;
  val not_def = not_def;
  val iff_def = iff_def;
  val ex1_def = ex1_def;
  val allI = allI;
  val spec = spec;
  val exI = exI;
  val exE = exE;
  val eq_reflection = eq_reflection;
  val iff_reflection = iff_reflection;
end;


Goalw [True_def]  "True";
by (REPEAT (ares_tac [impI] 1)) ;
qed "TrueI";

(*** Sequent-style elimination rules for & --> and ALL ***)

val major::prems = Goal 
    "[| P&Q; [| P; Q |] ==> R |] ==> R";
by (resolve_tac prems 1);
by (rtac (major RS conjunct1) 1);
by (rtac (major RS conjunct2) 1);
qed "conjE";

val major::prems = Goal 
    "[| P-->Q;  P;  Q ==> R |] ==> R";
by (resolve_tac prems 1);
by (rtac (major RS mp) 1);
by (resolve_tac prems 1);
qed "impE";

val major::prems = Goal 
    "[| ALL x. P(x); P(x) ==> R |] ==> R";
by (resolve_tac prems 1);
by (rtac (major RS spec) 1);
qed "allE";

(*Duplicates the quantifier; for use with eresolve_tac*)
val major::prems = Goal 
    "[| ALL x. P(x);  [| P(x); ALL x. P(x) |] ==> R \
\    |] ==> R";
by (resolve_tac prems 1);
by (rtac (major RS spec) 1);
by (rtac major 1);
qed "all_dupE";


(*** Negation rules, which translate between ~P and P-->False ***)

val prems = Goalw [not_def]  "(P ==> False) ==> ~P";
by (REPEAT (ares_tac (prems@[impI]) 1)) ;
qed "notI";

Goalw [not_def]  "[| ~P;  P |] ==> R";
by (etac (mp RS FalseE) 1);
by (assume_tac 1);
qed "notE";

Goal "[| P; ~P |] ==> R";
by (etac notE 1);
by (assume_tac 1);
qed "rev_notE";

(*This is useful with the special implication rules for each kind of P. *)
val prems = Goal 
    "[| ~P;  (P-->False) ==> Q |] ==> Q";
by (REPEAT (ares_tac (prems@[impI,notE]) 1)) ;
qed "not_to_imp";

(* For substitution into an assumption P, reduce Q to P-->Q, substitute into
   this implication, then apply impI to move P back into the assumptions.
   To specify P use something like
      eres_inst_tac [ ("P","ALL y. ?S(x,y)") ] rev_mp 1   *)
Goal "[| P;  P --> Q |] ==> Q";
by (etac mp 1);
by (assume_tac 1);
qed "rev_mp";

(*Contrapositive of an inference rule*)
val [major,minor]= Goal "[| ~Q;  P==>Q |] ==> ~P";
by (rtac (major RS notE RS notI) 1);
by (etac minor 1) ;
qed "contrapos";


(*** Modus Ponens Tactics ***)

(*Finds P-->Q and P in the assumptions, replaces implication by Q *)
fun mp_tac i = eresolve_tac [notE,impE] i  THEN  assume_tac i;

(*Like mp_tac but instantiates no variables*)
fun eq_mp_tac i = eresolve_tac [notE,impE] i  THEN  eq_assume_tac i;


(*** If-and-only-if ***)

val prems = Goalw [iff_def] 
   "[| P ==> Q;  Q ==> P |] ==> P<->Q";
by (REPEAT (ares_tac (prems@[conjI, impI]) 1)) ;
qed "iffI";


(*Observe use of rewrite_rule to unfold "<->" in meta-assumptions (prems) *)
val prems = Goalw [iff_def] 
    "[| P <-> Q;  [| P-->Q; Q-->P |] ==> R |] ==> R";
by (rtac conjE 1);
by (REPEAT (ares_tac prems 1)) ;
qed "iffE";

(* Destruct rules for <-> similar to Modus Ponens *)

Goalw [iff_def]  "[| P <-> Q;  P |] ==> Q";
by (etac (conjunct1 RS mp) 1);
by (assume_tac 1);
qed "iffD1";

val prems = Goalw [iff_def]  "[| P <-> Q;  Q |] ==> P";
by (etac (conjunct2 RS mp) 1);
by (assume_tac 1);
qed "iffD2";

Goal "[| P; P <-> Q |] ==> Q";
by (etac iffD1 1);
by (assume_tac 1);
qed "rev_iffD1";

Goal "[| Q; P <-> Q |] ==> P";
by (etac iffD2 1);
by (assume_tac 1);
qed "rev_iffD2";

Goal "P <-> P";
by (REPEAT (ares_tac [iffI] 1)) ;
qed "iff_refl";

Goal "Q <-> P ==> P <-> Q";
by (etac iffE 1);
by (rtac iffI 1);
by (REPEAT (eresolve_tac [asm_rl,mp] 1)) ;
qed "iff_sym";

Goal "[| P <-> Q;  Q<-> R |] ==> P <-> R";
by (rtac iffI 1);
by (REPEAT (eresolve_tac [asm_rl,iffE] 1 ORELSE mp_tac 1)) ;
qed "iff_trans";


(*** Unique existence.  NOTE THAT the following 2 quantifications
   EX!x such that [EX!y such that P(x,y)]     (sequential)
   EX!x,y such that P(x,y)                    (simultaneous)
 do NOT mean the same thing.  The parser treats EX!x y.P(x,y) as sequential.
***)

val prems = Goalw [ex1_def] 
    "[| P(a);  !!x. P(x) ==> x=a |] ==> EX! x. P(x)";
by (REPEAT (ares_tac (prems@[exI,conjI,allI,impI]) 1)) ;
qed "ex1I";

(*Sometimes easier to use: the premises have no shared variables.  Safe!*)
val [ex,eq] = Goal
    "[| EX x. P(x);  !!x y. [| P(x); P(y) |] ==> x=y |] ==> EX! x. P(x)";
by (rtac (ex RS exE) 1);
by (REPEAT (ares_tac [ex1I,eq] 1)) ;
qed "ex_ex1I";

val prems = Goalw [ex1_def] 
    "[| EX! x. P(x);  !!x. [| P(x);  ALL y. P(y) --> y=x |] ==> R |] ==> R";
by (cut_facts_tac prems 1);
by (REPEAT (eresolve_tac [exE,conjE] 1 ORELSE ares_tac prems 1)) ;
qed "ex1E";


(*** <-> congruence rules for simplification ***)

(*Use iffE on a premise.  For conj_cong, imp_cong, all_cong, ex_cong*)
fun iff_tac prems i =
    resolve_tac (prems RL [iffE]) i THEN
    REPEAT1 (eresolve_tac [asm_rl,mp] i);

val prems = Goal 
    "[| P <-> P';  P' ==> Q <-> Q' |] ==> (P&Q) <-> (P'&Q')";
by (cut_facts_tac prems 1);
by (REPEAT  (ares_tac [iffI,conjI] 1
     ORELSE  eresolve_tac [iffE,conjE,mp] 1 
     ORELSE  iff_tac prems 1)) ;
qed "conj_cong";

(*Reversed congruence rule!   Used in ZF/Order*)
val prems = Goal 
    "[| P <-> P';  P' ==> Q <-> Q' |] ==> (Q&P) <-> (Q'&P')";
by (cut_facts_tac prems 1);
by (REPEAT  (ares_tac [iffI,conjI] 1
     ORELSE  eresolve_tac [iffE,conjE,mp] 1 ORELSE  iff_tac prems 1)) ;
qed "conj_cong2";

val prems = Goal 
    "[| P <-> P';  Q <-> Q' |] ==> (P|Q) <-> (P'|Q')";
by (cut_facts_tac prems 1);
by (REPEAT  (eresolve_tac [iffE,disjE,disjI1,disjI2] 1
             ORELSE  ares_tac [iffI] 1 ORELSE  mp_tac 1)) ;
qed "disj_cong";

val prems = Goal 
    "[| P <-> P';  P' ==> Q <-> Q' |] ==> (P-->Q) <-> (P'-->Q')";
by (cut_facts_tac prems 1);
by (REPEAT   (ares_tac [iffI,impI] 1
      ORELSE  etac iffE 1 ORELSE  mp_tac 1 ORELSE iff_tac prems 1)) ;
qed "imp_cong";

val prems = Goal 
    "[| P <-> P';  Q <-> Q' |] ==> (P<->Q) <-> (P'<->Q')";
by (cut_facts_tac prems 1);
by (REPEAT   (etac iffE 1 ORELSE  ares_tac [iffI] 1 ORELSE  mp_tac 1)) ;
qed "iff_cong";

val prems = Goal 
    "P <-> P' ==> ~P <-> ~P'";
by (cut_facts_tac prems 1);
by (REPEAT   (ares_tac [iffI,notI] 1
      ORELSE  mp_tac 1 ORELSE  eresolve_tac [iffE,notE] 1)) ;
qed "not_cong";

val prems = Goal 
    "(!!x. P(x) <-> Q(x)) ==> (ALL x. P(x)) <-> (ALL x. Q(x))";
by (REPEAT   (ares_tac [iffI,allI] 1
     ORELSE   mp_tac 1 ORELSE   etac allE 1 ORELSE iff_tac prems 1)) ;
qed "all_cong";

val prems = Goal 
    "(!!x. P(x) <-> Q(x)) ==> (EX x. P(x)) <-> (EX x. Q(x))";
by (REPEAT   (etac exE 1 ORELSE ares_tac [iffI,exI] 1
     ORELSE   mp_tac 1 ORELSE   iff_tac prems 1)) ;
qed "ex_cong";

val prems = Goal 
    "(!!x. P(x) <-> Q(x)) ==> (EX! x. P(x)) <-> (EX! x. Q(x))";
by (REPEAT   (eresolve_tac [ex1E, spec RS mp] 1
       ORELSE ares_tac [iffI,ex1I] 1 ORELSE   mp_tac 1
       ORELSE   iff_tac prems 1)) ;
qed "ex1_cong";

(*** Equality rules ***)

Goal "a=b ==> b=a";
by (etac subst 1);
by (rtac refl 1) ;
qed "sym";

Goal "[| a=b;  b=c |] ==> a=c";
by (etac subst 1 THEN assume_tac 1) ;
qed "trans";

(** ~ b=a ==> ~ a=b **)
bind_thm ("not_sym", hd (compose(sym,2,contrapos)));


(* Two theorms for rewriting only one instance of a definition:
   the first for definitions of formulae and the second for terms *)

val prems = goal (the_context()) "(A == B) ==> A <-> B";
by (rewrite_goals_tac prems);
by (rtac iff_refl 1);
qed "def_imp_iff";

val prems = goal (the_context()) "(A == B) ==> A = B";
by (rewrite_goals_tac prems);
by (rtac refl 1);
qed "meta_eq_to_obj_eq";

(*substitution*)
bind_thm ("ssubst", sym RS subst);

(*A special case of ex1E that would otherwise need quantifier expansion*)
val prems = Goal
    "[| EX! x. P(x);  P(a);  P(b) |] ==> a=b";
by (cut_facts_tac prems 1);
by (etac ex1E 1);
by (rtac trans 1);
by (rtac sym 2);
by (REPEAT (eresolve_tac [asm_rl, spec RS mp] 1)) ;
qed "ex1_equalsE";

(** Polymorphic congruence rules **)

Goal "[| a=b |]  ==>  t(a)=t(b)";
by (etac ssubst 1);
by (rtac refl 1) ;
qed "subst_context";

Goal "[| a=b;  c=d |]  ==>  t(a,c)=t(b,d)";
by (REPEAT (etac ssubst 1));
by (rtac refl 1) ;
qed "subst_context2";

Goal "[| a=b;  c=d;  e=f |]  ==>  t(a,c,e)=t(b,d,f)";
by (REPEAT (etac ssubst 1));
by (rtac refl 1) ;
qed "subst_context3";

(*Useful with eresolve_tac for proving equalties from known equalities.
        a = b
        |   |
        c = d   *)
Goal "[| a=b;  a=c;  b=d |] ==> c=d";
by (rtac trans 1);
by (rtac trans 1);
by (rtac sym 1);
by (REPEAT (assume_tac 1));
qed "box_equals";

(*Dual of box_equals: for proving equalities backwards*)
Goal "[| a=c;  b=d;  c=d |] ==> a=b";
by (rtac trans 1);
by (rtac trans 1);
by (REPEAT (assume_tac 1));
by (etac sym 1);
qed "simp_equals";

(** Congruence rules for predicate letters **)

Goal "a=a' ==> P(a) <-> P(a')";
by (rtac iffI 1);
by (DEPTH_SOLVE (eresolve_tac [asm_rl, subst, ssubst] 1)) ;
qed "pred1_cong";

Goal "[| a=a';  b=b' |] ==> P(a,b) <-> P(a',b')";
by (rtac iffI 1);
by (DEPTH_SOLVE (eresolve_tac [asm_rl, subst, ssubst] 1)) ;
qed "pred2_cong";

Goal "[| a=a';  b=b';  c=c' |] ==> P(a,b,c) <-> P(a',b',c')";
by (rtac iffI 1);
by (DEPTH_SOLVE (eresolve_tac [asm_rl, subst, ssubst] 1)) ;
qed "pred3_cong";

(*special cases for free variables P, Q, R, S -- up to 3 arguments*)

val pred_congs = 
    flat (map (fn c => 
               map (fn th => read_instantiate [("P",c)] th)
                   [pred1_cong,pred2_cong,pred3_cong])
               (explode"PQRS"));

(*special case for the equality predicate!*)
bind_thm ("eq_cong", read_instantiate [("P","op =")] pred2_cong);


(*** Simplifications of assumed implications.
     Roy Dyckhoff has proved that conj_impE, disj_impE, and imp_impE
     used with mp_tac (restricted to atomic formulae) is COMPLETE for 
     intuitionistic propositional logic.  See
   R. Dyckhoff, Contraction-free sequent calculi for intuitionistic logic
    (preprint, University of St Andrews, 1991)  ***)

val major::prems= Goal 
    "[| (P&Q)-->S;  P-->(Q-->S) ==> R |] ==> R";
by (REPEAT (ares_tac ([conjI, impI, major RS mp]@prems) 1)) ;
qed "conj_impE";

val major::prems= Goal 
    "[| (P|Q)-->S;  [| P-->S; Q-->S |] ==> R |] ==> R";
by (DEPTH_SOLVE (ares_tac ([disjI1, disjI2, impI, major RS mp]@prems) 1)) ;
qed "disj_impE";

(*Simplifies the implication.  Classical version is stronger. 
  Still UNSAFE since Q must be provable -- backtracking needed.  *)
val major::prems= Goal 
    "[| (P-->Q)-->S;  [| P; Q-->S |] ==> Q;  S ==> R |] ==> R";
by (REPEAT (ares_tac ([impI, major RS mp]@prems) 1)) ;
qed "imp_impE";

(*Simplifies the implication.  Classical version is stronger. 
  Still UNSAFE since ~P must be provable -- backtracking needed.  *)
val major::prems= Goal
    "[| ~P --> S;  P ==> False;  S ==> R |] ==> R";
by (REPEAT (ares_tac ([notI, impI, major RS mp]@prems) 1)) ;
qed "not_impE";

(*Simplifies the implication.   UNSAFE.  *)
val major::prems= Goal 
    "[| (P<->Q)-->S;  [| P; Q-->S |] ==> Q;  [| Q; P-->S |] ==> P;  \
\       S ==> R |] ==> R";
by (REPEAT (ares_tac ([iffI, impI, major RS mp]@prems) 1)) ;
qed "iff_impE";

(*What if (ALL x.~~P(x)) --> ~~(ALL x.P(x)) is an assumption? UNSAFE*)
val major::prems= Goal 
    "[| (ALL x. P(x))-->S;  !!x. P(x);  S ==> R |] ==> R";
by (REPEAT (ares_tac ([allI, impI, major RS mp]@prems) 1)) ;
qed "all_impE";

(*Unsafe: (EX x.P(x))-->S  is equivalent to  ALL x.P(x)-->S.  *)
val major::prems= Goal 
    "[| (EX x. P(x))-->S;  P(x)-->S ==> R |] ==> R";
by (REPEAT (ares_tac ([exI, impI, major RS mp]@prems) 1)) ;
qed "ex_impE";

(*** Courtesy of Krzysztof Grabczewski ***)

val major::prems = Goal "[| P|Q;  P==>R;  Q==>S |] ==> R|S";
by (rtac (major RS disjE) 1);
by (REPEAT (eresolve_tac (prems RL [disjI1, disjI2]) 1));
qed "disj_imp_disj";
