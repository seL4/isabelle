(*  Title: 	FOLP/ifol.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Tactics and lemmas for ifol.thy (intuitionistic first-order logic)
*)

open IFOLP;

signature IFOLP_LEMMAS = 
  sig
  val allE: thm
  val all_cong: thm
  val all_dupE: thm
  val all_impE: thm
  val box_equals: thm
  val conjE: thm
  val conj_cong: thm
  val conj_impE: thm
  val contrapos: thm
  val disj_cong: thm
  val disj_impE: thm
  val eq_cong: thm
  val ex1I: thm
  val ex1E: thm
  val ex1_equalsE: thm
(*  val ex1_cong: thm****)
  val ex_cong: thm
  val ex_impE: thm
  val iffD1: thm
  val iffD2: thm
  val iffE: thm
  val iffI: thm
  val iff_cong: thm
  val iff_impE: thm
  val iff_refl: thm
  val iff_sym: thm
  val iff_trans: thm
  val impE: thm
  val imp_cong: thm
  val imp_impE: thm
  val mp_tac: int -> tactic
  val notE: thm
  val notI: thm
  val not_cong: thm
  val not_impE: thm
  val not_sym: thm
  val not_to_imp: thm
  val pred1_cong: thm
  val pred2_cong: thm
  val pred3_cong: thm
  val pred_congs: thm list
  val refl: thm
  val rev_mp: thm
  val simp_equals: thm
  val subst: thm
  val ssubst: thm
  val subst_context: thm
  val subst_context2: thm
  val subst_context3: thm
  val sym: thm
  val trans: thm
  val TrueI: thm
  val uniq_assume_tac: int -> tactic
  val uniq_mp_tac: int -> tactic
  end;


structure IFOLP_Lemmas : IFOLP_LEMMAS =
struct

val TrueI = TrueI;

(*** Sequent-style elimination rules for & --> and ALL ***)

val conjE = prove_goal IFOLP.thy 
    "[| p:P&Q; !!x y.[| x:P; y:Q |] ==> f(x,y):R |] ==> ?a:R"
 (fn prems=>
  [ (REPEAT (resolve_tac prems 1
      ORELSE (resolve_tac [conjunct1, conjunct2] 1 THEN
              resolve_tac prems 1))) ]);

val impE = prove_goal IFOLP.thy 
    "[| p:P-->Q;  q:P;  !!x.x:Q ==> r(x):R |] ==> ?p:R"
 (fn prems=> [ (REPEAT (resolve_tac (prems@[mp]) 1)) ]);

val allE = prove_goal IFOLP.thy 
    "[| p:ALL x.P(x); !!y.y:P(x) ==> q(y):R |] ==> ?p:R"
 (fn prems=> [ (REPEAT (resolve_tac (prems@[spec]) 1)) ]);

(*Duplicates the quantifier; for use with eresolve_tac*)
val all_dupE = prove_goal IFOLP.thy 
    "[| p:ALL x.P(x);  !!y z.[| y:P(x); z:ALL x.P(x) |] ==> q(y,z):R \
\    |] ==> ?p:R"
 (fn prems=> [ (REPEAT (resolve_tac (prems@[spec]) 1)) ]);


(*** Negation rules, which translate between ~P and P-->False ***)

val notI = prove_goalw IFOLP.thy [not_def]  "(!!x.x:P ==> q(x):False) ==> ?p:~P"
 (fn prems=> [ (REPEAT (ares_tac (prems@[impI]) 1)) ]);

val notE = prove_goalw IFOLP.thy [not_def] "[| p:~P;  q:P |] ==> ?p:R"
 (fn prems=>
  [ (resolve_tac [mp RS FalseE] 1),
    (REPEAT (resolve_tac prems 1)) ]);

(*This is useful with the special implication rules for each kind of P. *)
val not_to_imp = prove_goal IFOLP.thy 
    "[| p:~P;  !!x.x:(P-->False) ==> q(x):Q |] ==> ?p:Q"
 (fn prems=> [ (REPEAT (ares_tac (prems@[impI,notE]) 1)) ]);


(* For substitution int an assumption P, reduce Q to P-->Q, substitute into
   this implication, then apply impI to move P back into the assumptions.
   To specify P use something like
      eres_inst_tac [ ("P","ALL y. ?S(x,y)") ] rev_mp 1   *)
val rev_mp = prove_goal IFOLP.thy "[| p:P;  q:P --> Q |] ==> ?p:Q"
 (fn prems=> [ (REPEAT (resolve_tac (prems@[mp]) 1)) ]);


(*Contrapositive of an inference rule*)
val contrapos = prove_goal IFOLP.thy "[| p:~Q;  !!y.y:P==>q(y):Q |] ==> ?a:~P"
 (fn [major,minor]=> 
  [ (rtac (major RS notE RS notI) 1), 
    (etac minor 1) ]);

(** Unique assumption tactic.
    Ignores proof objects.
    Fails unless one assumption is equal and exactly one is unifiable 
**)

local
    fun discard_proof (Const("Proof",_) $ P $ _) = P;
in
val uniq_assume_tac =
  SUBGOAL
    (fn (prem,i) =>
      let val hyps = map discard_proof (Logic.strip_assums_hyp prem)
          and concl = discard_proof (Logic.strip_assums_concl prem)
      in  
	  if exists (fn hyp => hyp aconv concl) hyps
	  then case distinct (filter (fn hyp=> could_unify(hyp,concl)) hyps) of
	           [_] => assume_tac i
                 |  _  => no_tac
          else no_tac
      end);
end;


(*** Modus Ponens Tactics ***)

(*Finds P-->Q and P in the assumptions, replaces implication by Q *)
fun mp_tac i = eresolve_tac [notE,make_elim mp] i  THEN  assume_tac i;

(*Like mp_tac but instantiates no variables*)
fun uniq_mp_tac i = eresolve_tac [notE,impE] i  THEN  uniq_assume_tac i;


(*** If-and-only-if ***)

val iffI = prove_goalw IFOLP.thy [iff_def]
   "[| !!x.x:P ==> q(x):Q;  !!x.x:Q ==> r(x):P |] ==> ?p:P<->Q"
 (fn prems=> [ (REPEAT (ares_tac (prems@[conjI, impI]) 1)) ]);


(*Observe use of rewrite_rule to unfold "<->" in meta-assumptions (prems) *)
val iffE = prove_goalw IFOLP.thy [iff_def]
    "[| p:P <-> Q;  !!x y.[| x:P-->Q; y:Q-->P |] ==> q(x,y):R |] ==> ?p:R"
 (fn prems => [ (resolve_tac [conjE] 1), (REPEAT (ares_tac prems 1)) ]);

(* Destruct rules for <-> similar to Modus Ponens *)

val iffD1 = prove_goalw IFOLP.thy [iff_def] "[| p:P <-> Q;  q:P |] ==> ?p:Q"
 (fn prems => [ (rtac (conjunct1 RS mp) 1), (REPEAT (ares_tac prems 1)) ]);

val iffD2 = prove_goalw IFOLP.thy [iff_def] "[| p:P <-> Q;  q:Q |] ==> ?p:P"
 (fn prems => [ (rtac (conjunct2 RS mp) 1), (REPEAT (ares_tac prems 1)) ]);

val iff_refl = prove_goal IFOLP.thy "?p:P <-> P"
 (fn _ => [ (REPEAT (ares_tac [iffI] 1)) ]);

val iff_sym = prove_goal IFOLP.thy "p:Q <-> P ==> ?p:P <-> Q"
 (fn [major] =>
  [ (rtac (major RS iffE) 1),
    (rtac iffI 1),
    (REPEAT (eresolve_tac [asm_rl,mp] 1)) ]);

val iff_trans = prove_goal IFOLP.thy "[| p:P <-> Q; q:Q<-> R |] ==> ?p:P <-> R"
 (fn prems =>
  [ (cut_facts_tac prems 1),
    (rtac iffI 1),
    (REPEAT (eresolve_tac [asm_rl,iffE] 1 ORELSE mp_tac 1)) ]);


(*** Unique existence.  NOTE THAT the following 2 quantifications
   EX!x such that [EX!y such that P(x,y)]     (sequential)
   EX!x,y such that P(x,y)                    (simultaneous)
 do NOT mean the same thing.  The parser treats EX!x y.P(x,y) as sequential.
***)

val ex1I = prove_goalw IFOLP.thy [ex1_def]
    "[| p:P(a);  !!x u.u:P(x) ==> f(u) : x=a |] ==> ?p:EX! x. P(x)"
 (fn prems => [ (REPEAT (ares_tac (prems@[exI,conjI,allI,impI]) 1)) ]);

val ex1E = prove_goalw IFOLP.thy [ex1_def]
    "[| p:EX! x.P(x);  \
\       !!x u v. [| u:P(x);  v:ALL y. P(y) --> y=x |] ==> f(x,u,v):R |] ==>\
\    ?a : R"
 (fn prems =>
  [ (cut_facts_tac prems 1),
    (REPEAT (eresolve_tac [exE,conjE] 1 ORELSE ares_tac prems 1)) ]);


(*** <-> congruence rules for simplification ***)

(*Use iffE on a premise.  For conj_cong, imp_cong, all_cong, ex_cong*)
fun iff_tac prems i =
    resolve_tac (prems RL [iffE]) i THEN
    REPEAT1 (eresolve_tac [asm_rl,mp] i);

val conj_cong = prove_goal IFOLP.thy 
    "[| p:P <-> P';  !!x.x:P' ==> q(x):Q <-> Q' |] ==> ?p:(P&Q) <-> (P'&Q')"
 (fn prems =>
  [ (cut_facts_tac prems 1),
    (REPEAT  (ares_tac [iffI,conjI] 1
      ORELSE  eresolve_tac [iffE,conjE,mp] 1
      ORELSE  iff_tac prems 1)) ]);

val disj_cong = prove_goal IFOLP.thy 
    "[| p:P <-> P';  q:Q <-> Q' |] ==> ?p:(P|Q) <-> (P'|Q')"
 (fn prems =>
  [ (cut_facts_tac prems 1),
    (REPEAT  (eresolve_tac [iffE,disjE,disjI1,disjI2] 1
      ORELSE  ares_tac [iffI] 1
      ORELSE  mp_tac 1)) ]);

val imp_cong = prove_goal IFOLP.thy 
    "[| p:P <-> P';  !!x.x:P' ==> q(x):Q <-> Q' |] ==> ?p:(P-->Q) <-> (P'-->Q')"
 (fn prems =>
  [ (cut_facts_tac prems 1),
    (REPEAT   (ares_tac [iffI,impI] 1
      ORELSE  eresolve_tac [iffE] 1
      ORELSE  mp_tac 1 ORELSE iff_tac prems 1)) ]);

val iff_cong = prove_goal IFOLP.thy 
    "[| p:P <-> P';  q:Q <-> Q' |] ==> ?p:(P<->Q) <-> (P'<->Q')"
 (fn prems =>
  [ (cut_facts_tac prems 1),
    (REPEAT   (eresolve_tac [iffE] 1
      ORELSE  ares_tac [iffI] 1
      ORELSE  mp_tac 1)) ]);

val not_cong = prove_goal IFOLP.thy 
    "p:P <-> P' ==> ?p:~P <-> ~P'"
 (fn prems =>
  [ (cut_facts_tac prems 1),
    (REPEAT   (ares_tac [iffI,notI] 1
      ORELSE  mp_tac 1
      ORELSE  eresolve_tac [iffE,notE] 1)) ]);

val all_cong = prove_goal IFOLP.thy 
    "(!!x.f(x):P(x) <-> Q(x)) ==> ?p:(ALL x.P(x)) <-> (ALL x.Q(x))"
 (fn prems =>
  [ (REPEAT   (ares_tac [iffI,allI] 1
      ORELSE   mp_tac 1
      ORELSE   eresolve_tac [allE] 1 ORELSE iff_tac prems 1)) ]);

val ex_cong = prove_goal IFOLP.thy 
    "(!!x.f(x):P(x) <-> Q(x)) ==> ?p:(EX x.P(x)) <-> (EX x.Q(x))"
 (fn prems =>
  [ (REPEAT   (eresolve_tac [exE] 1 ORELSE ares_tac [iffI,exI] 1
      ORELSE   mp_tac 1
      ORELSE   iff_tac prems 1)) ]);

(*NOT PROVED
val ex1_cong = prove_goal IFOLP.thy 
    "(!!x.f(x):P(x) <-> Q(x)) ==> ?p:(EX! x.P(x)) <-> (EX! x.Q(x))"
 (fn prems =>
  [ (REPEAT   (eresolve_tac [ex1E, spec RS mp] 1 ORELSE ares_tac [iffI,ex1I] 1
      ORELSE   mp_tac 1
      ORELSE   iff_tac prems 1)) ]);
*)

(*** Equality rules ***)

val refl = ieqI;

val subst = prove_goal IFOLP.thy "[| p:a=b;  q:P(a) |] ==> ?p : P(b)"
 (fn [prem1,prem2] => [ rtac (prem2 RS rev_mp) 1, (rtac (prem1 RS ieqE) 1), 
                        rtac impI 1, atac 1 ]);

val sym = prove_goal IFOLP.thy "q:a=b ==> ?c:b=a"
 (fn [major] => [ (rtac (major RS subst) 1), (rtac refl 1) ]);

val trans = prove_goal IFOLP.thy "[| p:a=b;  q:b=c |] ==> ?d:a=c"
 (fn [prem1,prem2] => [ (rtac (prem2 RS subst) 1), (rtac prem1 1) ]);

(** ~ b=a ==> ~ a=b **)
val not_sym = prove_goal IFOLP.thy "p:~ b=a ==> ?q:~ a=b"
 (fn [prem] => [ (rtac (prem RS contrapos) 1), (etac sym 1) ]);

(*calling "standard" reduces maxidx to 0*)
val ssubst = standard (sym RS subst);

(*A special case of ex1E that would otherwise need quantifier expansion*)
val ex1_equalsE = prove_goal IFOLP.thy
    "[| p:EX! x.P(x);  q:P(a);  r:P(b) |] ==> ?d:a=b"
 (fn prems =>
  [ (cut_facts_tac prems 1),
    (etac ex1E 1),
    (rtac trans 1),
    (rtac sym 2),
    (REPEAT (eresolve_tac [asm_rl, spec RS mp] 1)) ]);

(** Polymorphic congruence rules **)

val subst_context = prove_goal IFOLP.thy 
   "[| p:a=b |]  ==>  ?d:t(a)=t(b)"
 (fn prems=>
  [ (resolve_tac (prems RL [ssubst]) 1),
    (resolve_tac [refl] 1) ]);

val subst_context2 = prove_goal IFOLP.thy 
   "[| p:a=b;  q:c=d |]  ==>  ?p:t(a,c)=t(b,d)"
 (fn prems=>
  [ (EVERY1 (map rtac ((prems RL [ssubst]) @ [refl]))) ]);

val subst_context3 = prove_goal IFOLP.thy 
   "[| p:a=b;  q:c=d;  r:e=f |]  ==>  ?p:t(a,c,e)=t(b,d,f)"
 (fn prems=>
  [ (EVERY1 (map rtac ((prems RL [ssubst]) @ [refl]))) ]);

(*Useful with eresolve_tac for proving equalties from known equalities.
	a = b
	|   |
	c = d	*)
val box_equals = prove_goal IFOLP.thy
    "[| p:a=b;  q:a=c;  r:b=d |] ==> ?p:c=d"  
 (fn prems=>
  [ (resolve_tac [trans] 1),
    (resolve_tac [trans] 1),
    (resolve_tac [sym] 1),
    (REPEAT (resolve_tac prems 1)) ]);

(*Dual of box_equals: for proving equalities backwards*)
val simp_equals = prove_goal IFOLP.thy
    "[| p:a=c;  q:b=d;  r:c=d |] ==> ?p:a=b"  
 (fn prems=>
  [ (resolve_tac [trans] 1),
    (resolve_tac [trans] 1),
    (REPEAT (resolve_tac (prems @ (prems RL [sym])) 1)) ]);

(** Congruence rules for predicate letters **)

val pred1_cong = prove_goal IFOLP.thy
    "p:a=a' ==> ?p:P(a) <-> P(a')"
 (fn prems =>
  [ (cut_facts_tac prems 1),
    (rtac iffI 1),
    (DEPTH_SOLVE (eresolve_tac [asm_rl, subst, ssubst] 1)) ]);

val pred2_cong = prove_goal IFOLP.thy
    "[| p:a=a';  q:b=b' |] ==> ?p:P(a,b) <-> P(a',b')"
 (fn prems =>
  [ (cut_facts_tac prems 1),
    (rtac iffI 1),
    (DEPTH_SOLVE (eresolve_tac [asm_rl, subst, ssubst] 1)) ]);

val pred3_cong = prove_goal IFOLP.thy
    "[| p:a=a';  q:b=b';  r:c=c' |] ==> ?p:P(a,b,c) <-> P(a',b',c')"
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

val conj_impE = prove_goal IFOLP.thy 
    "[| p:(P&Q)-->S;  !!x.x:P-->(Q-->S) ==> q(x):R |] ==> ?p:R"
 (fn major::prems=>
  [ (REPEAT (ares_tac ([conjI, impI, major RS mp]@prems) 1)) ]);

val disj_impE = prove_goal IFOLP.thy 
    "[| p:(P|Q)-->S;  !!x y.[| x:P-->S; y:Q-->S |] ==> q(x,y):R |] ==> ?p:R"
 (fn major::prems=>
  [ (DEPTH_SOLVE (ares_tac ([disjI1, disjI2, impI, major RS mp]@prems) 1)) ]);

(*Simplifies the implication.  Classical version is stronger. 
  Still UNSAFE since Q must be provable -- backtracking needed.  *)
val imp_impE = prove_goal IFOLP.thy 
    "[| p:(P-->Q)-->S;  !!x y.[| x:P; y:Q-->S |] ==> q(x,y):Q;  !!x.x:S ==> r(x):R |] ==> \
\    ?p:R"
 (fn major::prems=>
  [ (REPEAT (ares_tac ([impI, major RS mp]@prems) 1)) ]);

(*Simplifies the implication.  Classical version is stronger. 
  Still UNSAFE since ~P must be provable -- backtracking needed.  *)
val not_impE = prove_goal IFOLP.thy
    "[| p:~P --> S;  !!y.y:P ==> q(y):False;  !!y.y:S ==> r(y):R |] ==> ?p:R"
 (fn major::prems=>
  [ (REPEAT (ares_tac ([notI, impI, major RS mp]@prems) 1)) ]);

(*Simplifies the implication.   UNSAFE.  *)
val iff_impE = prove_goal IFOLP.thy 
    "[| p:(P<->Q)-->S;  !!x y.[| x:P; y:Q-->S |] ==> q(x,y):Q;  \
\       !!x y.[| x:Q; y:P-->S |] ==> r(x,y):P;  !!x.x:S ==> s(x):R |] ==> ?p:R"
 (fn major::prems=>
  [ (REPEAT (ares_tac ([iffI, impI, major RS mp]@prems) 1)) ]);

(*What if (ALL x.~~P(x)) --> ~~(ALL x.P(x)) is an assumption? UNSAFE*)
val all_impE = prove_goal IFOLP.thy 
    "[| p:(ALL x.P(x))-->S;  !!x.q:P(x);  !!y.y:S ==> r(y):R |] ==> ?p:R"
 (fn major::prems=>
  [ (REPEAT (ares_tac ([allI, impI, major RS mp]@prems) 1)) ]);

(*Unsafe: (EX x.P(x))-->S  is equivalent to  ALL x.P(x)-->S.  *)
val ex_impE = prove_goal IFOLP.thy 
    "[| p:(EX x.P(x))-->S;  !!y.y:P(a)-->S ==> q(y):R |] ==> ?p:R"
 (fn major::prems=>
  [ (REPEAT (ares_tac ([exI, impI, major RS mp]@prems) 1)) ]);

end;

open IFOLP_Lemmas;

