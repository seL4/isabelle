(*  Title:      FOL/simpdata
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Simplification data for FOL
*)

(*** Rewrite rules ***)

fun int_prove_fun_raw s = 
    (writeln s;  prove_goal IFOLP.thy s
       (fn prems => [ (cut_facts_tac prems 1), (Int.fast_tac 1) ]));

fun int_prove_fun s = int_prove_fun_raw ("?p : "^s);

val conj_rews = map int_prove_fun
 ["P & True <-> P",     "True & P <-> P",
  "P & False <-> False", "False & P <-> False",
  "P & P <-> P",
  "P & ~P <-> False",   "~P & P <-> False",
  "(P & Q) & R <-> P & (Q & R)"];

val disj_rews = map int_prove_fun
 ["P | True <-> True",  "True | P <-> True",
  "P | False <-> P",    "False | P <-> P",
  "P | P <-> P",
  "(P | Q) | R <-> P | (Q | R)"];

val not_rews = map int_prove_fun
 ["~ False <-> True",   "~ True <-> False"];

val imp_rews = map int_prove_fun
 ["(P --> False) <-> ~P",       "(P --> True) <-> True",
  "(False --> P) <-> True",     "(True --> P) <-> P", 
  "(P --> P) <-> True",         "(P --> ~P) <-> ~P"];

val iff_rews = map int_prove_fun
 ["(True <-> P) <-> P",         "(P <-> True) <-> P",
  "(P <-> P) <-> True",
  "(False <-> P) <-> ~P",       "(P <-> False) <-> ~P"];

val quant_rews = map int_prove_fun
 ["(ALL x.P) <-> P",    "(EX x.P) <-> P"];

(*These are NOT supplied by default!*)
val distrib_rews  = map int_prove_fun
 ["~(P|Q) <-> ~P & ~Q",
  "P & (Q | R) <-> P&Q | P&R", "(Q | R) & P <-> Q&P | R&P",
  "(P | Q --> R) <-> (P --> R) & (Q --> R)",
  "~(EX x.NORM(P(x))) <-> (ALL x. ~NORM(P(x)))",
  "((EX x.NORM(P(x))) --> Q) <-> (ALL x. NORM(P(x)) --> Q)",
  "(EX x.NORM(P(x))) & NORM(Q) <-> (EX x. NORM(P(x)) & NORM(Q))",
  "NORM(Q) & (EX x.NORM(P(x))) <-> (EX x. NORM(Q) & NORM(P(x)))"];

val P_Imp_P_iff_T = int_prove_fun_raw "p:P ==> ?p:(P <-> True)";

fun make_iff_T th = th RS P_Imp_P_iff_T;

val refl_iff_T = make_iff_T refl;

val norm_thms = [(norm_eq RS sym, norm_eq),
                 (NORM_iff RS iff_sym, NORM_iff)];


(* Conversion into rewrite rules *)

val not_P_imp_P_iff_F = int_prove_fun_raw "p:~P ==> ?p:(P <-> False)";

fun mk_eq th = case concl_of th of
      _ $ (Const("op <->",_)$_$_) $ _ => th
    | _ $ (Const("op =",_)$_$_) $ _ => th
    | _ $ (Const("Not",_)$_) $ _ => th RS not_P_imp_P_iff_F 
    | _ => make_iff_T th;

fun atomize th = case concl_of th of (*The operator below is "Proof $ P $ p"*)
      _ $ (Const("op -->",_) $ _ $ _) $ _ => atomize(th RS mp)
    | _ $ (Const("op &",_) $ _ $ _) $ _ => atomize(th RS conjunct1) @
                                       atomize(th RS conjunct2)
    | _ $ (Const("All",_) $ _) $ _ => atomize(th RS spec)
    | _ $ (Const("True",_)) $ _ => []
    | _ $ (Const("False",_)) $ _ => []
    | _ => [th];

fun mk_rew_rules th = map mk_eq (atomize th);

(*destruct function for analysing equations*)
fun dest_red(_ $ (red $ lhs $ rhs) $ _) = (red,lhs,rhs)
  | dest_red t = raise TERM("FOL/dest_red", [t]);

structure FOLP_SimpData : SIMP_DATA =
  struct
  val refl_thms         = [refl, iff_refl]
  val trans_thms        = [trans, iff_trans]
  val red1              = iffD1
  val red2              = iffD2
  val mk_rew_rules      = mk_rew_rules
  val case_splits       = []         (*NO IF'S!*)
  val norm_thms         = norm_thms
  val subst_thms        = [subst];
  val dest_red          = dest_red
  end;

structure FOLP_Simp = SimpFun(FOLP_SimpData);

(*not a component of SIMP_DATA, but an argument of SIMP_TAC *)
val FOLP_congs = 
   [all_cong,ex_cong,eq_cong,
    conj_cong,disj_cong,imp_cong,iff_cong,not_cong] @ pred_congs;

val IFOLP_rews =
   [refl_iff_T] @ conj_rews @ disj_rews @ not_rews @ 
    imp_rews @ iff_rews @ quant_rews;

open FOLP_Simp;

val auto_ss = empty_ss setauto ares_tac [TrueI];

val IFOLP_ss = auto_ss addcongs FOLP_congs addrews IFOLP_rews;

(*Classical version...*)
fun prove_fun s = 
    (writeln s;  prove_goal FOLP.thy s
       (fn prems => [ (cut_facts_tac prems 1), (Cla.fast_tac FOLP_cs 1) ]));

val cla_rews = map prove_fun
 ["?p:P | ~P",          "?p:~P | P",
  "?p:~ ~ P <-> P",     "?p:(~P --> P) <-> P"];

val FOLP_rews = IFOLP_rews@cla_rews;

val FOLP_ss = auto_ss addcongs FOLP_congs addrews FOLP_rews;


