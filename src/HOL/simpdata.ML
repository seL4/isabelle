(*  Title:      HOL/simpdata.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1991  University of Cambridge

Instantiation of the generic simplifier
*)

open Simplifier;

local

fun prover s = prove_goal HOL.thy s (fn _ => [fast_tac HOL_cs 1]);

val P_imp_P_iff_True = prover "P --> (P = True)" RS mp;
val P_imp_P_eq_True = P_imp_P_iff_True RS eq_reflection;

val not_P_imp_P_iff_F = prover "~P --> (P = False)" RS mp;
val not_P_imp_P_eq_False = not_P_imp_P_iff_F RS eq_reflection;

fun atomize pairs =
  let fun atoms th =
        (case concl_of th of
           Const("Trueprop",_) $ p =>
             (case head_of p of
                Const(a,_) =>
                  (case assoc(pairs,a) of
                     Some(rls) => flat (map atoms ([th] RL rls))
                   | None => [th])
              | _ => [th])
         | _ => [th])
  in atoms end;

fun mk_meta_eq r = case concl_of r of
        Const("==",_)$_$_ => r
    |   _$(Const("op =",_)$_$_) => r RS eq_reflection
    |   _$(Const("not",_)$_) => r RS not_P_imp_P_eq_False
    |   _ => r RS P_imp_P_eq_True;
(* last 2 lines requires all formulae to be of the from Trueprop(.) *)

fun gen_all th = forall_elim_vars (#maxidx(rep_thm th)+1) th;

val imp_cong = impI RSN
    (2, prove_goal HOL.thy "(P=P')--> (P'--> (Q=Q'))--> ((P-->Q) = (P'-->Q'))"
        (fn _=> [fast_tac HOL_cs 1]) RS mp RS mp);

val o_apply = prove_goalw HOL.thy [o_def] "(f o g)(x) = f(g(x))"
 (fn _ => [rtac refl 1]);

val simp_thms = map prover
 [ "(x=x) = True",
   "(~True) = False", "(~False) = True", "(~ ~ P) = P",
   "(~P) ~= P", "P ~= (~P)", "(P ~= Q) = (P = (~Q))",
   "(True=P) = P", "(P=True) = P",
   "(True --> P) = P", "(False --> P) = True", 
   "(P --> True) = True", "(P --> P) = True",
   "(P --> False) = (~P)", "(P --> ~P) = (~P)",
   "(P & True) = P", "(True & P) = P", 
   "(P & False) = False", "(False & P) = False", "(P & P) = P",
   "(P | True) = True", "(True | P) = True", 
   "(P | False) = P", "(False | P) = P", "(P | P) = P",
   "(!x.P) = P", "(? x.P) = P", "? x. x=t", "(? x. x=t & P(x)) = P(t)",
   "(P|Q --> R) = ((P-->R)&(Q-->R))" ];

in

val meta_eq_to_obj_eq = prove_goal HOL.thy "x==y ==> x=y"
  (fn [prem] => [rewtac prem, rtac refl 1]);

val eq_sym_conv = prover "(x=y) = (y=x)";

val conj_assoc = prover "((P&Q)&R) = (P&(Q&R))";

val if_True = prove_goalw HOL.thy [if_def] "(if True then x else y) = x"
 (fn _=>[fast_tac (HOL_cs addIs [select_equality]) 1]);

val if_False = prove_goalw HOL.thy [if_def] "(if False then x else y) = y"
 (fn _=>[fast_tac (HOL_cs addIs [select_equality]) 1]);

val if_P = prove_goal HOL.thy "P ==> (if P then x else y) = x"
 (fn [prem] => [ stac (prem RS eqTrueI) 1, rtac if_True 1 ]);

val if_not_P = prove_goal HOL.thy "~P ==> (if P then x else y) = y"
 (fn [prem] => [ stac (prem RS not_P_imp_P_iff_F) 1, rtac if_False 1 ]);

val expand_if = prove_goal HOL.thy
    "P(if Q then x else y) = ((Q --> P(x)) & (~Q --> P(y)))"
 (fn _=> [ (res_inst_tac [("Q","Q")] (excluded_middle RS disjE) 1),
         rtac (if_P RS ssubst) 2,
         rtac (if_not_P RS ssubst) 1,
         REPEAT(fast_tac HOL_cs 1) ]);

val if_bool_eq = prove_goal HOL.thy
                   "(if P then Q else R) = ((P-->Q) & (~P-->R))"
                   (fn _ => [rtac expand_if 1]);

(*Add congruence rules for = (instead of ==) *)
infix 4 addcongs;
fun ss addcongs congs = ss addeqcongs (congs RL [eq_reflection]);

fun Addcongs congs = (simpset := !simpset addcongs congs);

(*Add a simpset to a classical set!*)
infix 4 addss;
fun cs addss ss = cs addbefore asm_full_simp_tac ss 1;

val mksimps_pairs =
  [("op -->", [mp]), ("op &", [conjunct1,conjunct2]),
   ("All", [spec]), ("True", []), ("False", []),
   ("If", [if_bool_eq RS iffD1])];

fun mksimps pairs = map mk_meta_eq o atomize pairs o gen_all;

val HOL_ss = empty_ss
      setmksimps (mksimps mksimps_pairs)
      setsolver (fn prems => resolve_tac (TrueI::refl::prems) ORELSE' atac
                             ORELSE' etac FalseE)
      setsubgoaler asm_simp_tac
      addsimps ([if_True, if_False, o_apply, conj_assoc] @ simp_thms)
      addcongs [imp_cong];

local val mktac = mk_case_split_tac (meta_eq_to_obj_eq RS iffD2)
in
fun split_tac splits = mktac (map mk_meta_eq splits)
end;


(* eliminiation of existential quantifiers in assumptions *)

val ex_all_equiv =
  let val lemma1 = prove_goal HOL.thy
        "(? x. P(x) ==> PROP Q) ==> (!!x. P(x) ==> PROP Q)"
        (fn prems => [resolve_tac prems 1, etac exI 1]);
      val lemma2 = prove_goalw HOL.thy [Ex_def]
        "(!!x. P(x) ==> PROP Q) ==> (? x. P(x) ==> PROP Q)"
        (fn prems => [REPEAT(resolve_tac prems 1)])
  in equal_intr lemma1 lemma2 end;

(* '&' congruence rule: not included by default!
   May slow rewrite proofs down by as much as 50% *)

val conj_cong = impI RSN
    (2, prove_goal HOL.thy "(P=P')--> (P'--> (Q=Q'))--> ((P&Q) = (P'&Q'))"
        (fn _=> [fast_tac HOL_cs 1]) RS mp RS mp);

val rev_conj_cong = impI RSN
    (2, prove_goal HOL.thy "(Q=Q')--> (Q'--> (P=P'))--> ((P&Q) = (P'&Q'))"
        (fn _=> [fast_tac HOL_cs 1]) RS mp RS mp);

(** 'if' congruence rules: neither included by default! *)

(*Simplifies x assuming c and y assuming ~c*)
val if_cong = prove_goal HOL.thy
  "[| b=c; c ==> x=u; ~c ==> y=v |] ==>\
\  (if b then x else y) = (if c then u else v)"
  (fn rew::prems =>
   [stac rew 1, stac expand_if 1, stac expand_if 1,
    fast_tac (HOL_cs addDs prems) 1]);

(*Prevents simplification of x and y: much faster*)
val if_weak_cong = prove_goal HOL.thy
  "b=c ==> (if b then x else y) = (if c then x else y)"
  (fn [prem] => [rtac (prem RS arg_cong) 1]);

(*Prevents simplification of t: much faster*)
val let_weak_cong = prove_goal HOL.thy
  "a = b ==> (let x=a in t(x)) = (let x=b in t(x))"
  (fn [prem] => [rtac (prem RS arg_cong) 1]);

end;

fun prove nm thm  = qed_goal nm HOL.thy thm (fn _ => [fast_tac HOL_cs 1]);

prove "conj_commute" "(P&Q) = (Q&P)";
prove "conj_left_commute" "(P&(Q&R)) = (Q&(P&R))";
val conj_comms = [conj_commute, conj_left_commute];

prove "conj_disj_distribL" "(P&(Q|R)) = (P&Q | P&R)";
prove "conj_disj_distribR" "((P|Q)&R) = (P&R | Q&R)";

prove "de_Morgan_disj" "(~(P | Q)) = (~P & ~Q)";
prove "de_Morgan_conj" "(~(P & Q)) = (~P | ~Q)";

prove "ex_disj_distrib" "(? x. P(x) | Q(x)) = ((? x. P(x)) | (? x. Q(x)))";
prove "all_conj_distrib" "(!x. P(x) & Q(x)) = ((! x. P(x)) & (! x. Q(x)))";

qed_goal "if_cancel" HOL.thy "(if c then x else x) = x"
  (fn _ => [simp_tac (HOL_ss setloop (split_tac [expand_if])) 1]);

qed_goal "if_distrib" HOL.thy
  "f(if c then x else y) = (if c then f x else f y)" 
  (fn _ => [simp_tac (HOL_ss setloop (split_tac [expand_if])) 1]);

qed_goalw "o_assoc" HOL.thy [o_def] "(f o g) o h = (f o g o h)"
  (fn _=>[rtac ext 1, rtac refl 1]);
