(*  Title: 	FOL/simpdata
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Simplification data for FOL
*)

(*** Rewrite rules ***)

fun int_prove_fun s = 
    (writeln s;  prove_goal IFOL.thy s
       (fn prems => [ (cut_facts_tac prems 1), (Int.fast_tac 1) ]));

val conj_rews = map int_prove_fun
 ["P & True <-> P", 	"True & P <-> P",
  "P & False <-> False", "False & P <-> False",
  "P & P <-> P",
  "P & ~P <-> False", 	"~P & P <-> False",
  "(P & Q) & R <-> P & (Q & R)"];

val disj_rews = map int_prove_fun
 ["P | True <-> True", 	"True | P <-> True",
  "P | False <-> P", 	"False | P <-> P",
  "P | P <-> P",
  "(P | Q) | R <-> P | (Q | R)"];

val not_rews = map int_prove_fun
 ["~ False <-> True",	"~ True <-> False"];

val imp_rews = map int_prove_fun
 ["(P --> False) <-> ~P",	"(P --> True) <-> True",
  "(False --> P) <-> True",	"(True --> P) <-> P", 
  "(P --> P) <-> True",		"(P --> ~P) <-> ~P"];

val iff_rews = map int_prove_fun
 ["(True <-> P) <-> P", 	"(P <-> True) <-> P",
  "(P <-> P) <-> True",
  "(False <-> P) <-> ~P", 	"(P <-> False) <-> ~P"];

val quant_rews = map int_prove_fun
 ["(ALL x.P) <-> P",	"(EX x.P) <-> P"];

(*These are NOT supplied by default!*)
val distrib_rews  = map int_prove_fun
 ["~(P|Q) <-> ~P & ~Q",
  "P & (Q | R) <-> P&Q | P&R", "(Q | R) & P <-> Q&P | R&P",
  "(P | Q --> R) <-> (P --> R) & (Q --> R)"];

val P_Imp_P_iff_T = int_prove_fun "P ==> (P <-> True)";

fun make_iff_T th = th RS P_Imp_P_iff_T;

val refl_iff_T = make_iff_T refl;

val notFalseI = int_prove_fun "~False";

(* Conversion into rewrite rules *)

val not_P_imp_P_iff_F = int_prove_fun "~P ==> (P <-> False)";

fun mk_meta_eq th = case concl_of th of
      _ $ (Const("op <->",_)$_$_) => th RS iff_reflection
    | _ $ (Const("op =",_)$_$_) => th RS eq_reflection
    | _ $ (Const("Not",_)$_) => (th RS not_P_imp_P_iff_F) RS iff_reflection
    | _ => (make_iff_T th) RS iff_reflection;

fun atomize th = case concl_of th of (*The operator below is Trueprop*)
      _ $ (Const("op -->",_) $ _ $ _) => atomize(th RS mp)
    | _ $ (Const("op &",_) $ _ $ _) => atomize(th RS conjunct1) @
				       atomize(th RS conjunct2)
    | _ $ (Const("All",_) $ _) => atomize(th RS spec)
    | _ $ (Const("True",_)) => []
    | _ $ (Const("False",_)) => []
    | _ => [th];

fun mk_rew_rules th = map mk_meta_eq (atomize th);

structure Induction = InductionFun(struct val spec=IFOL.spec end);

val IFOL_rews =
   [refl_iff_T] @ conj_rews @ disj_rews @ not_rews @ 
    imp_rews @ iff_rews @ quant_rews;

open Simplifier Induction;

val IFOL_ss = empty_ss
      setmksimps mk_rew_rules
      setsolver
        (fn prems => resolve_tac (TrueI::refl::iff_refl::notFalseI::prems))
      setsubgoaler asm_simp_tac
      addsimps IFOL_rews
      addcongs [imp_cong RS iff_reflection];

(*Classical version...*)
fun prove_fun s = 
    (writeln s;  prove_goal FOL.thy s
       (fn prems => [ (cut_facts_tac prems 1), (Cla.fast_tac FOL_cs 1) ]));

val cla_rews = map prove_fun
 ["P | ~P", 		"~P | P",
  "~ ~ P <-> P",	"(~P --> P) <-> P"];

val FOL_ss = IFOL_ss addsimps cla_rews;

(*** case splitting ***)

val split_tac =
  let val eq_reflection2 = prove_goal FOL.thy "x==y ==> x=y"
                             (fn [prem] => [rewtac prem, rtac refl 1])
      val iff_reflection2 = prove_goal FOL.thy "x==y ==> x<->y"
                              (fn [prem] => [rewtac prem, rtac iff_refl 1])
      val [iffD] = [eq_reflection2,iff_reflection2] RL [iffD2]
  in fn splits => mk_case_split_tac iffD (map mk_meta_eq splits) end;
