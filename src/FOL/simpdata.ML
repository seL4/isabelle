(*  Title: 	FOL/simpdata
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Simplification data for FOL
*)

(*** Rewrite rules ***)

fun int_prove_fun s = 
 (writeln s;  
  prove_goal IFOL.thy s
   (fn prems => [ (cut_facts_tac prems 1), 
		  (Int.fast_tac 1) ]));

val conj_rews = map int_prove_fun
 ["P & True <-> P", 	 "True & P <-> P",
  "P & False <-> False", "False & P <-> False",
  "P & P <-> P",
  "P & ~P <-> False", 	 "~P & P <-> False",
  "(P & Q) & R <-> P & (Q & R)"];

val disj_rews = map int_prove_fun
 ["P | True <-> True", 	"True | P <-> True",
  "P | False <-> P", 	"False | P <-> P",
  "P | P <-> P",
  "(P | Q) | R <-> P | (Q | R)"];

val not_rews = map int_prove_fun
 ["~(P|Q)  <-> ~P & ~Q",
  "~ False <-> True",	"~ True <-> False"];

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
 ["P & (Q | R) <-> P&Q | P&R", 
  "(Q | R) & P <-> Q&P | R&P",
  "(P | Q --> R) <-> (P --> R) & (Q --> R)"];

bind_thm("conj_commute", int_prove_fun "P&Q <-> Q&P");
bind_thm("disj_commute", int_prove_fun "P|Q <-> Q|P");

(** Conversion into rewrite rules **)

fun gen_all th = forall_elim_vars (#maxidx(rep_thm th)+1) th;

(*Make atomic rewrite rules*)
fun atomize r =
  case concl_of r of
    Const("Trueprop",_) $ p =>
      (case p of
	 Const("op -->",_)$_$_ => atomize(r RS mp)
       | Const("op &",_)$_$_   => atomize(r RS conjunct1) @
	  		          atomize(r RS conjunct2)
       | Const("All",_)$_      => atomize(r RS spec)
       | Const("True",_)       => []	(*True is DELETED*)
       | Const("False",_)      => []	(*should False do something?*)
       | _                     => [r])
  | _ => [r];


val P_iff_F = int_prove_fun "~P ==> (P <-> False)";
val iff_reflection_F = P_iff_F RS iff_reflection;

val P_iff_T = int_prove_fun "P ==> (P <-> True)";
val iff_reflection_T = P_iff_T RS iff_reflection;

(*Make meta-equalities.  The operator below is Trueprop*)
fun mk_meta_eq th = case concl_of th of
    Const("==",_)$_$_           => th
  | _ $ (Const("op =",_)$_$_)   => th RS eq_reflection
  | _ $ (Const("op <->",_)$_$_) => th RS iff_reflection
  | _ $ (Const("Not",_)$_)      => th RS iff_reflection_F
  | _                           => th RS iff_reflection_T;

structure Induction = InductionFun(struct val spec=IFOL.spec end);

open Simplifier Induction;

infix addcongs;
fun ss addcongs congs =
    ss addeqcongs (congs RL [eq_reflection,iff_reflection]);

val IFOL_rews =
   [refl RS P_iff_T] @ conj_rews @ disj_rews @ not_rews @ 
    imp_rews @ iff_rews @ quant_rews;

val notFalseI = int_prove_fun "~False";
val triv_rls = [TrueI,refl,iff_refl,notFalseI];

val IFOL_ss = 
  empty_ss 
  setmksimps (map mk_meta_eq o atomize o gen_all)
  setsolver  (fn prems => resolve_tac (triv_rls@prems) 
	                  ORELSE' assume_tac
	                  ORELSE' etac FalseE)
  setsubgoaler asm_simp_tac
  addsimps IFOL_rews
  addcongs [imp_cong];

(*Classical version...*)
fun prove_fun s = 
 (writeln s;  
  prove_goal FOL.thy s
   (fn prems => [ (cut_facts_tac prems 1), 
		  (Cla.fast_tac FOL_cs 1) ]));

val cla_rews = map prove_fun
 ["~(P&Q)  <-> ~P | ~Q",
  "P | ~P", 		"~P | P",
  "~ ~ P <-> P",	"(~P --> P) <-> P"];

val FOL_ss = IFOL_ss addsimps cla_rews;

(*** case splitting ***)

qed_goal "meta_iffD" FOL.thy "[| P==Q; Q |] ==> P"
        (fn [prem1,prem2] => [rewtac prem1, rtac prem2 1]);

fun split_tac splits =
    mk_case_split_tac meta_iffD (map mk_meta_eq splits);
