(*  Title:      FOL/IFOL.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Tactics and lemmas for IFOL.thy (intuitionistic first-order logic)
*)

open IFOL;


qed_goalw "TrueI" IFOL.thy [True_def] "True"
 (fn _ => [ (REPEAT (ares_tac [impI] 1)) ]);

(*** Sequent-style elimination rules for & --> and ALL ***)

qed_goal "conjE" IFOL.thy 
    "[| P&Q; [| P; Q |] ==> R |] ==> R"
 (fn prems=>
  [ (REPEAT (resolve_tac prems 1
      ORELSE (resolve_tac [conjunct1, conjunct2] 1 THEN
              resolve_tac prems 1))) ]);

qed_goal "impE" IFOL.thy 
    "[| P-->Q;  P;  Q ==> R |] ==> R"
 (fn prems=> [ (REPEAT (resolve_tac (prems@[mp]) 1)) ]);

qed_goal "allE" IFOL.thy 
    "[| ALL x.P(x); P(x) ==> R |] ==> R"
 (fn prems=> [ (REPEAT (resolve_tac (prems@[spec]) 1)) ]);

(*Duplicates the quantifier; for use with eresolve_tac*)
qed_goal "all_dupE" IFOL.thy 
    "[| ALL x.P(x);  [| P(x); ALL x.P(x) |] ==> R \
\    |] ==> R"
 (fn prems=> [ (REPEAT (resolve_tac (prems@[spec]) 1)) ]);


(*** Negation rules, which translate between ~P and P-->False ***)

qed_goalw "notI" IFOL.thy [not_def] "(P ==> False) ==> ~P"
 (fn prems=> [ (REPEAT (ares_tac (prems@[impI]) 1)) ]);

qed_goalw "notE" IFOL.thy [not_def] "[| ~P;  P |] ==> R"
 (fn prems=>
  [ (resolve_tac [mp RS FalseE] 1),
    (REPEAT (resolve_tac prems 1)) ]);

qed_goal "rev_notE" IFOL.thy "!!P R. [| P; ~P |] ==> R"
 (fn _ => [REPEAT (ares_tac [notE] 1)]);

(*This is useful with the special implication rules for each kind of P. *)
qed_goal "not_to_imp" IFOL.thy 
    "[| ~P;  (P-->False) ==> Q |] ==> Q"
 (fn prems=> [ (REPEAT (ares_tac (prems@[impI,notE]) 1)) ]);

(* For substitution into an assumption P, reduce Q to P-->Q, substitute into
   this implication, then apply impI to move P back into the assumptions.
   To specify P use something like
      eres_inst_tac [ ("P","ALL y. ?S(x,y)") ] rev_mp 1   *)
qed_goal "rev_mp" IFOL.thy "[| P;  P --> Q |] ==> Q"
 (fn prems=> [ (REPEAT (resolve_tac (prems@[mp]) 1)) ]);


(*Contrapositive of an inference rule*)
qed_goal "contrapos" IFOL.thy "[| ~Q;  P==>Q |] ==> ~P"
 (fn [major,minor]=> 
  [ (rtac (major RS notE RS notI) 1), 
    (etac minor 1) ]);


(*** Modus Ponens Tactics ***)

(*Finds P-->Q and P in the assumptions, replaces implication by Q *)
fun mp_tac i = eresolve_tac [notE,impE] i  THEN  assume_tac i;

(*Like mp_tac but instantiates no variables*)
fun eq_mp_tac i = eresolve_tac [notE,impE] i  THEN  eq_assume_tac i;


(*** If-and-only-if ***)

qed_goalw "iffI" IFOL.thy [iff_def]
   "[| P ==> Q;  Q ==> P |] ==> P<->Q"
 (fn prems=> [ (REPEAT (ares_tac (prems@[conjI, impI]) 1)) ]);


(*Observe use of rewrite_rule to unfold "<->" in meta-assumptions (prems) *)
qed_goalw "iffE" IFOL.thy [iff_def]
    "[| P <-> Q;  [| P-->Q; Q-->P |] ==> R |] ==> R"
 (fn prems => [ (rtac conjE 1), (REPEAT (ares_tac prems 1)) ]);

(* Destruct rules for <-> similar to Modus Ponens *)

qed_goalw "iffD1" IFOL.thy [iff_def] "[| P <-> Q;  P |] ==> Q"
 (fn prems => [ (rtac (conjunct1 RS mp) 1), (REPEAT (ares_tac prems 1)) ]);

qed_goalw "iffD2" IFOL.thy [iff_def] "[| P <-> Q;  Q |] ==> P"
 (fn prems => [ (rtac (conjunct2 RS mp) 1), (REPEAT (ares_tac prems 1)) ]);

qed_goal "iff_refl" IFOL.thy "P <-> P"
 (fn _ => [ (REPEAT (ares_tac [iffI] 1)) ]);

qed_goal "iff_sym" IFOL.thy "Q <-> P ==> P <-> Q"
 (fn [major] =>
  [ (rtac (major RS iffE) 1),
    (rtac iffI 1),
    (REPEAT (eresolve_tac [asm_rl,mp] 1)) ]);

qed_goal "iff_trans" IFOL.thy
    "!!P Q R. [| P <-> Q;  Q<-> R |] ==> P <-> R"
 (fn _ =>
  [ (rtac iffI 1),
    (REPEAT (eresolve_tac [asm_rl,iffE] 1 ORELSE mp_tac 1)) ]);


(*** Unique existence.  NOTE THAT the following 2 quantifications
   EX!x such that [EX!y such that P(x,y)]     (sequential)
   EX!x,y such that P(x,y)                    (simultaneous)
 do NOT mean the same thing.  The parser treats EX!x y.P(x,y) as sequential.
***)

qed_goalw "ex1I" IFOL.thy [ex1_def]
    "[| P(a);  !!x. P(x) ==> x=a |] ==> EX! x. P(x)"
 (fn prems => [ (REPEAT (ares_tac (prems@[exI,conjI,allI,impI]) 1)) ]);

(*Sometimes easier to use: the premises have no shared variables*)
qed_goal "ex_ex1I" IFOL.thy
    "[| EX x.P(x);  !!x y. [| P(x); P(y) |] ==> x=y |] ==> EX! x. P(x)"
 (fn [ex,eq] => [ (rtac (ex RS exE) 1),
                  (REPEAT (ares_tac [ex1I,eq] 1)) ]);

qed_goalw "ex1E" IFOL.thy [ex1_def]
    "[| EX! x.P(x);  !!x. [| P(x);  ALL y. P(y) --> y=x |] ==> R |] ==> R"
 (fn prems =>
  [ (cut_facts_tac prems 1),
    (REPEAT (eresolve_tac [exE,conjE] 1 ORELSE ares_tac prems 1)) ]);


(*** <-> congruence rules for simplification ***)

(*Use iffE on a premise.  For conj_cong, imp_cong, all_cong, ex_cong*)
fun iff_tac prems i =
    resolve_tac (prems RL [iffE]) i THEN
    REPEAT1 (eresolve_tac [asm_rl,mp] i);

qed_goal "conj_cong" IFOL.thy 
    "[| P <-> P';  P' ==> Q <-> Q' |] ==> (P&Q) <-> (P'&Q')"
 (fn prems =>
  [ (cut_facts_tac prems 1),
    (REPEAT  (ares_tac [iffI,conjI] 1
      ORELSE  eresolve_tac [iffE,conjE,mp] 1
      ORELSE  iff_tac prems 1)) ]);

(*Reversed congruence rule!   Used in ZF/Order*)
qed_goal "conj_cong2" IFOL.thy 
    "[| P <-> P';  P' ==> Q <-> Q' |] ==> (Q&P) <-> (Q'&P')"
 (fn prems =>
  [ (cut_facts_tac prems 1),
    (REPEAT  (ares_tac [iffI,conjI] 1
      ORELSE  eresolve_tac [iffE,conjE,mp] 1
      ORELSE  iff_tac prems 1)) ]);

qed_goal "disj_cong" IFOL.thy 
    "[| P <-> P';  Q <-> Q' |] ==> (P|Q) <-> (P'|Q')"
 (fn prems =>
  [ (cut_facts_tac prems 1),
    (REPEAT  (eresolve_tac [iffE,disjE,disjI1,disjI2] 1
      ORELSE  ares_tac [iffI] 1
      ORELSE  mp_tac 1)) ]);

qed_goal "imp_cong" IFOL.thy 
    "[| P <-> P';  P' ==> Q <-> Q' |] ==> (P-->Q) <-> (P'-->Q')"
 (fn prems =>
  [ (cut_facts_tac prems 1),
    (REPEAT   (ares_tac [iffI,impI] 1
      ORELSE  etac iffE 1
      ORELSE  mp_tac 1 ORELSE iff_tac prems 1)) ]);

qed_goal "iff_cong" IFOL.thy 
    "[| P <-> P';  Q <-> Q' |] ==> (P<->Q) <-> (P'<->Q')"
 (fn prems =>
  [ (cut_facts_tac prems 1),
    (REPEAT   (etac iffE 1
      ORELSE  ares_tac [iffI] 1
      ORELSE  mp_tac 1)) ]);

qed_goal "not_cong" IFOL.thy 
    "P <-> P' ==> ~P <-> ~P'"
 (fn prems =>
  [ (cut_facts_tac prems 1),
    (REPEAT   (ares_tac [iffI,notI] 1
      ORELSE  mp_tac 1
      ORELSE  eresolve_tac [iffE,notE] 1)) ]);

qed_goal "all_cong" IFOL.thy 
    "(!!x.P(x) <-> Q(x)) ==> (ALL x.P(x)) <-> (ALL x.Q(x))"
 (fn prems =>
  [ (REPEAT   (ares_tac [iffI,allI] 1
      ORELSE   mp_tac 1
      ORELSE   etac allE 1 ORELSE iff_tac prems 1)) ]);

qed_goal "ex_cong" IFOL.thy 
    "(!!x.P(x) <-> Q(x)) ==> (EX x.P(x)) <-> (EX x.Q(x))"
 (fn prems =>
  [ (REPEAT   (etac exE 1 ORELSE ares_tac [iffI,exI] 1
      ORELSE   mp_tac 1
      ORELSE   iff_tac prems 1)) ]);

qed_goal "ex1_cong" IFOL.thy 
    "(!!x.P(x) <-> Q(x)) ==> (EX! x.P(x)) <-> (EX! x.Q(x))"
 (fn prems =>
  [ (REPEAT   (eresolve_tac [ex1E, spec RS mp] 1 ORELSE ares_tac [iffI,ex1I] 1
      ORELSE   mp_tac 1
      ORELSE   iff_tac prems 1)) ]);

(*** Equality rules ***)

qed_goal "sym" IFOL.thy "a=b ==> b=a"
 (fn [major] => [ (rtac (major RS subst) 1), (rtac refl 1) ]);

qed_goal "trans" IFOL.thy "[| a=b;  b=c |] ==> a=c"
 (fn [prem1,prem2] => [ (rtac (prem2 RS subst) 1), (rtac prem1 1) ]);

(** ~ b=a ==> ~ a=b **)
val [not_sym] = compose(sym,2,contrapos);

(*Substitution: rule and tactic*)
bind_thm ("ssubst", sym RS subst);
fun stac th = CHANGED o rtac (th RS ssubst);

(*A special case of ex1E that would otherwise need quantifier expansion*)
qed_goal "ex1_equalsE" IFOL.thy
    "[| EX! x.P(x);  P(a);  P(b) |] ==> a=b"
 (fn prems =>
  [ (cut_facts_tac prems 1),
    (etac ex1E 1),
    (rtac trans 1),
    (rtac sym 2),
    (REPEAT (eresolve_tac [asm_rl, spec RS mp] 1)) ]);

(** Polymorphic congruence rules **)

qed_goal "subst_context" IFOL.thy 
   "[| a=b |]  ==>  t(a)=t(b)"
 (fn prems=>
  [ (resolve_tac (prems RL [ssubst]) 1),
    (rtac refl 1) ]);

qed_goal "subst_context2" IFOL.thy 
   "[| a=b;  c=d |]  ==>  t(a,c)=t(b,d)"
 (fn prems=>
  [ (EVERY1 (map rtac ((prems RL [ssubst]) @ [refl]))) ]);

qed_goal "subst_context3" IFOL.thy 
   "[| a=b;  c=d;  e=f |]  ==>  t(a,c,e)=t(b,d,f)"
 (fn prems=>
  [ (EVERY1 (map rtac ((prems RL [ssubst]) @ [refl]))) ]);

(*Useful with eresolve_tac for proving equalties from known equalities.
        a = b
        |   |
        c = d   *)
qed_goal "box_equals" IFOL.thy
    "[| a=b;  a=c;  b=d |] ==> c=d"  
 (fn prems=>
  [ (rtac trans 1),
    (rtac trans 1),
    (rtac sym 1),
    (REPEAT (resolve_tac prems 1)) ]);

(*Dual of box_equals: for proving equalities backwards*)
qed_goal "simp_equals" IFOL.thy
    "[| a=c;  b=d;  c=d |] ==> a=b"  
 (fn prems=>
  [ (rtac trans 1),
    (rtac trans 1),
    (REPEAT (resolve_tac (prems @ (prems RL [sym])) 1)) ]);

(** Congruence rules for predicate letters **)

qed_goal "pred1_cong" IFOL.thy
    "a=a' ==> P(a) <-> P(a')"
 (fn prems =>
  [ (cut_facts_tac prems 1),
    (rtac iffI 1),
    (DEPTH_SOLVE (eresolve_tac [asm_rl, subst, ssubst] 1)) ]);

qed_goal "pred2_cong" IFOL.thy
    "[| a=a';  b=b' |] ==> P(a,b) <-> P(a',b')"
 (fn prems =>
  [ (cut_facts_tac prems 1),
    (rtac iffI 1),
    (DEPTH_SOLVE (eresolve_tac [asm_rl, subst, ssubst] 1)) ]);

qed_goal "pred3_cong" IFOL.thy
    "[| a=a';  b=b';  c=c' |] ==> P(a,b,c) <-> P(a',b',c')"
 (fn prems =>
  [ (cut_facts_tac prems 1),
    (rtac iffI 1),
    (DEPTH_SOLVE (eresolve_tac [asm_rl, subst, ssubst] 1)) ]);

(*special cases for free variables P, Q, R, S -- up to 3 arguments*)

val pred_congs = 
    flat (map (fn c => 
               map (fn th => read_instantiate [("P",c)] th)
                   [pred1_cong,pred2_cong,pred3_cong])
               (explode"PQRS"));

(*special case for the equality predicate!*)
val eq_cong = read_instantiate [("P","op =")] pred2_cong;


(*** Simplifications of assumed implications.
     Roy Dyckhoff has proved that conj_impE, disj_impE, and imp_impE
     used with mp_tac (restricted to atomic formulae) is COMPLETE for 
     intuitionistic propositional logic.  See
   R. Dyckhoff, Contraction-free sequent calculi for intuitionistic logic
    (preprint, University of St Andrews, 1991)  ***)

qed_goal "conj_impE" IFOL.thy 
    "[| (P&Q)-->S;  P-->(Q-->S) ==> R |] ==> R"
 (fn major::prems=>
  [ (REPEAT (ares_tac ([conjI, impI, major RS mp]@prems) 1)) ]);

qed_goal "disj_impE" IFOL.thy 
    "[| (P|Q)-->S;  [| P-->S; Q-->S |] ==> R |] ==> R"
 (fn major::prems=>
  [ (DEPTH_SOLVE (ares_tac ([disjI1, disjI2, impI, major RS mp]@prems) 1)) ]);

(*Simplifies the implication.  Classical version is stronger. 
  Still UNSAFE since Q must be provable -- backtracking needed.  *)
qed_goal "imp_impE" IFOL.thy 
    "[| (P-->Q)-->S;  [| P; Q-->S |] ==> Q;  S ==> R |] ==> R"
 (fn major::prems=>
  [ (REPEAT (ares_tac ([impI, major RS mp]@prems) 1)) ]);

(*Simplifies the implication.  Classical version is stronger. 
  Still UNSAFE since ~P must be provable -- backtracking needed.  *)
qed_goal "not_impE" IFOL.thy
    "[| ~P --> S;  P ==> False;  S ==> R |] ==> R"
 (fn major::prems=>
  [ (REPEAT (ares_tac ([notI, impI, major RS mp]@prems) 1)) ]);

(*Simplifies the implication.   UNSAFE.  *)
qed_goal "iff_impE" IFOL.thy 
    "[| (P<->Q)-->S;  [| P; Q-->S |] ==> Q;  [| Q; P-->S |] ==> P;  \
\       S ==> R |] ==> R"
 (fn major::prems=>
  [ (REPEAT (ares_tac ([iffI, impI, major RS mp]@prems) 1)) ]);

(*What if (ALL x.~~P(x)) --> ~~(ALL x.P(x)) is an assumption? UNSAFE*)
qed_goal "all_impE" IFOL.thy 
    "[| (ALL x.P(x))-->S;  !!x.P(x);  S ==> R |] ==> R"
 (fn major::prems=>
  [ (REPEAT (ares_tac ([allI, impI, major RS mp]@prems) 1)) ]);

(*Unsafe: (EX x.P(x))-->S  is equivalent to  ALL x.P(x)-->S.  *)
qed_goal "ex_impE" IFOL.thy 
    "[| (EX x.P(x))-->S;  P(x)-->S ==> R |] ==> R"
 (fn major::prems=>
  [ (REPEAT (ares_tac ([exI, impI, major RS mp]@prems) 1)) ]);

(*** Courtesy of Krzysztof Grabczewski ***)

val major::prems = goal IFOL.thy "[| P|Q;  P==>R;  Q==>S |] ==> R|S";
by (rtac (major RS disjE) 1);
by (REPEAT (eresolve_tac (prems RL [disjI1, disjI2]) 1));
qed "disj_imp_disj";

(* The following two theorms are useful when rewriting only one instance  *) 
(* of a definition                                                        *)
(* first one for definitions of formulae and the second for terms         *)

val prems = goal IFOL.thy "(A == B) ==> A <-> B";
by (rewrite_goals_tac prems);
by (rtac iff_refl 1);
qed "def_imp_iff";

val prems = goal IFOL.thy "(A == B) ==> A = B";
by (rewrite_goals_tac prems);
by (rtac refl 1);
qed "def_imp_eq";

