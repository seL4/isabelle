(*  Title:      HOL/HOL.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1991  University of Cambridge

For HOL.thy
Derived rules from Appendix of Mike Gordons HOL Report, Cambridge TR 68 
*)

open HOL;


(** Equality **)

qed_goal "sym" HOL.thy "s=t ==> t=s"
 (fn prems => [cut_facts_tac prems 1, etac subst 1, rtac refl 1]);

(*calling "standard" reduces maxidx to 0*)
bind_thm ("ssubst", (sym RS subst));

qed_goal "trans" HOL.thy "[| r=s; s=t |] ==> r=t"
 (fn prems =>
        [rtac subst 1, resolve_tac prems 1, resolve_tac prems 1]);

(*Useful with eresolve_tac for proving equalties from known equalities.
        a = b
        |   |
        c = d   *)
qed_goal "box_equals" HOL.thy
    "[| a=b;  a=c;  b=d |] ==> c=d"  
 (fn prems=>
  [ (rtac trans 1),
    (rtac trans 1),
    (rtac sym 1),
    (REPEAT (resolve_tac prems 1)) ]);

(** Congruence rules for meta-application **)

(*similar to AP_THM in Gordon's HOL*)
qed_goal "fun_cong" HOL.thy "(f::'a=>'b) = g ==> f(x)=g(x)"
  (fn [prem] => [rtac (prem RS subst) 1, rtac refl 1]);

(*similar to AP_TERM in Gordon's HOL and FOL's subst_context*)
qed_goal "arg_cong" HOL.thy "x=y ==> f(x)=f(y)"
 (fn [prem] => [rtac (prem RS subst) 1, rtac refl 1]);

qed_goal "cong" HOL.thy
   "[| f = g; (x::'a) = y |] ==> f(x) = g(y)"
 (fn [prem1,prem2] =>
   [rtac (prem1 RS subst) 1, rtac (prem2 RS subst) 1, rtac refl 1]);

(** Equality of booleans -- iff **)

qed_goal "iffI" HOL.thy
   "[| P ==> Q;  Q ==> P |] ==> P=Q"
 (fn prems=> [ (REPEAT (ares_tac (prems@[impI, iff RS mp RS mp]) 1)) ]);

qed_goal "iffD2" HOL.thy "[| P=Q; Q |] ==> P"
 (fn prems =>
        [rtac ssubst 1, resolve_tac prems 1, resolve_tac prems 1]);

val iffD1 = sym RS iffD2;

qed_goal "iffE" HOL.thy
    "[| P=Q; [| P --> Q; Q --> P |] ==> R |] ==> R"
 (fn [p1,p2] => [REPEAT(ares_tac([p1 RS iffD2, p1 RS iffD1, p2, impI])1)]);

(** True **)

qed_goalw "TrueI" HOL.thy [True_def] "True"
  (fn _ => [rtac refl 1]);

qed_goal "eqTrueI " HOL.thy "P ==> P=True" 
 (fn prems => [REPEAT(resolve_tac ([iffI,TrueI]@prems) 1)]);

qed_goal "eqTrueE" HOL.thy "P=True ==> P" 
 (fn prems => [REPEAT(resolve_tac (prems@[TrueI,iffD2]) 1)]);

(** Universal quantifier **)

qed_goalw "allI" HOL.thy [All_def] "(!!x::'a. P(x)) ==> !x. P(x)"
 (fn prems => [resolve_tac (prems RL [eqTrueI RS ext]) 1]);

qed_goalw "spec" HOL.thy [All_def] "! x::'a.P(x) ==> P(x)"
 (fn prems => [rtac eqTrueE 1, resolve_tac (prems RL [fun_cong]) 1]);

qed_goal "allE" HOL.thy "[| !x.P(x);  P(x) ==> R |] ==> R"
 (fn major::prems=>
  [ (REPEAT (resolve_tac (prems @ [major RS spec]) 1)) ]);

qed_goal "all_dupE" HOL.thy 
    "[| ! x.P(x);  [| P(x); ! x.P(x) |] ==> R |] ==> R"
 (fn prems =>
  [ (REPEAT (resolve_tac (prems @ (prems RL [spec])) 1)) ]);


(** False ** Depends upon spec; it is impossible to do propositional logic
             before quantifiers! **)

qed_goalw "FalseE" HOL.thy [False_def] "False ==> P"
 (fn [major] => [rtac (major RS spec) 1]);

qed_goal "False_neq_True" HOL.thy "False=True ==> P"
 (fn [prem] => [rtac (prem RS eqTrueE RS FalseE) 1]);


(** Negation **)

qed_goalw "notI" HOL.thy [not_def] "(P ==> False) ==> ~P"
 (fn prems=> [rtac impI 1, eresolve_tac prems 1]);

qed_goalw "notE" HOL.thy [not_def] "[| ~P;  P |] ==> R"
 (fn prems => [rtac (prems MRS mp RS FalseE) 1]);

(** Implication **)

qed_goal "impE" HOL.thy "[| P-->Q;  P;  Q ==> R |] ==> R"
 (fn prems=> [ (REPEAT (resolve_tac (prems@[mp]) 1)) ]);

(* Reduces Q to P-->Q, allowing substitution in P. *)
qed_goal "rev_mp" HOL.thy "[| P;  P --> Q |] ==> Q"
 (fn prems=>  [ (REPEAT (resolve_tac (prems@[mp]) 1)) ]);

qed_goal "contrapos" HOL.thy "[| ~Q;  P==>Q |] ==> ~P"
 (fn [major,minor]=> 
  [ (rtac (major RS notE RS notI) 1), 
    (etac minor 1) ]);

qed_goal "rev_contrapos" HOL.thy "[| P==>Q; ~Q |] ==> ~P"
 (fn [major,minor]=> 
  [ (rtac (minor RS contrapos) 1), (etac major 1) ]);

(* ~(?t = ?s) ==> ~(?s = ?t) *)
bind_thm("not_sym", sym COMP rev_contrapos);


(** Existential quantifier **)

qed_goalw "exI" HOL.thy [Ex_def] "P(x) ==> ? x::'a.P(x)"
 (fn prems => [rtac selectI 1, resolve_tac prems 1]);

qed_goalw "exE" HOL.thy [Ex_def]
  "[| ? x::'a.P(x); !!x. P(x) ==> Q |] ==> Q"
  (fn prems => [REPEAT(resolve_tac prems 1)]);


(** Conjunction **)

qed_goalw "conjI" HOL.thy [and_def] "[| P; Q |] ==> P&Q"
 (fn prems =>
  [REPEAT (resolve_tac (prems@[allI,impI]) 1 ORELSE etac (mp RS mp) 1)]);

qed_goalw "conjunct1" HOL.thy [and_def] "[| P & Q |] ==> P"
 (fn prems =>
   [resolve_tac (prems RL [spec] RL [mp]) 1, REPEAT(ares_tac [impI] 1)]);

qed_goalw "conjunct2" HOL.thy [and_def] "[| P & Q |] ==> Q"
 (fn prems =>
   [resolve_tac (prems RL [spec] RL [mp]) 1, REPEAT(ares_tac [impI] 1)]);

qed_goal "conjE" HOL.thy "[| P&Q;  [| P; Q |] ==> R |] ==> R"
 (fn prems =>
         [cut_facts_tac prems 1, resolve_tac prems 1,
          etac conjunct1 1, etac conjunct2 1]);

(** Disjunction *)

qed_goalw "disjI1" HOL.thy [or_def] "P ==> P|Q"
 (fn [prem] => [REPEAT(ares_tac [allI,impI, prem RSN (2,mp)] 1)]);

qed_goalw "disjI2" HOL.thy [or_def] "Q ==> P|Q"
 (fn [prem] => [REPEAT(ares_tac [allI,impI, prem RSN (2,mp)] 1)]);

qed_goalw "disjE" HOL.thy [or_def] "[| P | Q; P ==> R; Q ==> R |] ==> R"
 (fn [a1,a2,a3] =>
        [rtac (mp RS mp) 1, rtac spec 1, rtac a1 1,
         rtac (a2 RS impI) 1, assume_tac 1, rtac (a3 RS impI) 1, assume_tac 1]);

(** CCONTR -- classical logic **)

qed_goalw "classical" HOL.thy [not_def]  "(~P ==> P) ==> P"
 (fn [prem] =>
   [rtac (True_or_False RS (disjE RS eqTrueE)) 1,  assume_tac 1,
    rtac (impI RS prem RS eqTrueI) 1,
    etac subst 1,  assume_tac 1]);

val ccontr = FalseE RS classical;

(*Double negation law*)
qed_goal "notnotD" HOL.thy "~~P ==> P"
 (fn [major]=>
  [ (rtac classical 1), (eresolve_tac [major RS notE] 1) ]);


(** Unique existence **)

qed_goalw "ex1I" HOL.thy [Ex1_def]
    "[| P(a);  !!x. P(x) ==> x=a |] ==> ?! x. P(x)"
 (fn prems =>
  [REPEAT (ares_tac (prems@[exI,conjI,allI,impI]) 1)]);

qed_goalw "ex1E" HOL.thy [Ex1_def]
    "[| ?! x.P(x);  !!x. [| P(x);  ! y. P(y) --> y=x |] ==> R |] ==> R"
 (fn major::prems =>
  [rtac (major RS exE) 1, REPEAT (etac conjE 1 ORELSE ares_tac prems 1)]);


(** Select: Hilbert's Epsilon-operator **)

(*Easier to apply than selectI: conclusion has only one occurrence of P*)
qed_goal "selectI2" HOL.thy
    "[| P(a);  !!x. P(x) ==> Q(x) |] ==> Q(@x.P(x))"
 (fn prems => [ resolve_tac prems 1, 
                rtac selectI 1, 
                resolve_tac prems 1 ]);

qed_goal "select_equality" HOL.thy
    "[| P(a);  !!x. P(x) ==> x=a |] ==> (@x.P(x)) = a"
 (fn prems => [ rtac selectI2 1, 
                REPEAT (ares_tac prems 1) ]);


(** Classical intro rules for disjunction and existential quantifiers *)

qed_goal "disjCI" HOL.thy "(~Q ==> P) ==> P|Q"
 (fn prems=>
  [ (rtac classical 1),
    (REPEAT (ares_tac (prems@[disjI1,notI]) 1)),
    (REPEAT (ares_tac (prems@[disjI2,notE]) 1)) ]);

qed_goal "excluded_middle" HOL.thy "~P | P"
 (fn _ => [ (REPEAT (ares_tac [disjCI] 1)) ]);

(*For disjunctive case analysis*)
fun excluded_middle_tac sP =
    res_inst_tac [("Q",sP)] (excluded_middle RS disjE);

(*Classical implies (-->) elimination. *)
qed_goal "impCE" HOL.thy "[| P-->Q; ~P ==> R; Q ==> R |] ==> R" 
 (fn major::prems=>
  [ rtac (excluded_middle RS disjE) 1,
    REPEAT (DEPTH_SOLVE_1 (ares_tac (prems @ [major RS mp]) 1))]);

(*Classical <-> elimination. *)
qed_goal "iffCE" HOL.thy
    "[| P=Q;  [| P; Q |] ==> R;  [| ~P; ~Q |] ==> R |] ==> R"
 (fn major::prems =>
  [ (rtac (major RS iffE) 1),
    (REPEAT (DEPTH_SOLVE_1 
        (eresolve_tac ([asm_rl,impCE,notE]@prems) 1))) ]);

qed_goal "exCI" HOL.thy "(! x. ~P(x) ==> P(a)) ==> ? x.P(x)"
 (fn prems=>
  [ (rtac ccontr 1),
    (REPEAT (ares_tac (prems@[exI,allI,notI,notE]) 1))  ]);


(* case distinction *)

qed_goal "case_split_thm" HOL.thy "[| P ==> Q; ~P ==> Q |] ==> Q"
  (fn [p1,p2] => [cut_facts_tac [excluded_middle] 1, etac disjE 1,
                  etac p2 1, etac p1 1]);

fun case_tac a = res_inst_tac [("P",a)] case_split_thm;

(** Standard abbreviations **)

fun stac th = rtac(th RS ssubst);
fun sstac ths = EVERY' (map stac ths);
fun strip_tac i = REPEAT(resolve_tac [impI,allI] i); 


(*** Load simpdata.ML to be able to initialize HOL's simpset ***)

(** Applying HypsubstFun to generate hyp_subst_tac **)

structure Hypsubst_Data =
  struct
  structure Simplifier = Simplifier
  (*Take apart an equality judgement; otherwise raise Match!*)
  fun dest_eq (Const("Trueprop",_) $ (Const("op =",_)  $ t $ u)) = (t,u);
  val eq_reflection = eq_reflection
  val imp_intr = impI
  val rev_mp = rev_mp
  val subst = subst
  val sym = sym
  end;

structure Hypsubst = HypsubstFun(Hypsubst_Data);
open Hypsubst;

(*** Applying ClassicalFun to create a classical prover ***)
structure Classical_Data = 
  struct
  val sizef     = size_of_thm
  val mp        = mp
  val not_elim  = notE
  val classical = classical
  val hyp_subst_tacs=[hyp_subst_tac]
  end;

structure Classical = ClassicalFun(Classical_Data);
open Classical;

(*Propositional rules*)
val prop_cs = empty_cs addSIs [refl,TrueI,conjI,disjCI,impI,notI,iffI]
                       addSEs [conjE,disjE,impCE,FalseE,iffE];

(*Quantifier rules*)
val HOL_cs = prop_cs addSIs [allI] addIs [exI,ex1I]
                     addSEs [exE,ex1E] addEs [allE];

use     "simpdata.ML";
simpset := HOL_ss;


(** Install simpsets and datatypes in theory structure **)
exception SS_DATA of simpset;

let fun merge [] = SS_DATA empty_ss
      | merge ss = let val ss = map (fn SS_DATA x => x) ss;
                   in SS_DATA (foldl merge_ss (hd ss, tl ss)) end;

    fun put (SS_DATA ss) = simpset := ss;

    fun get () = SS_DATA (!simpset);
in add_thydata HOL.thy
     ("simpset", ThyMethods {merge = merge, put = put, get = get})
end;

exception DT_DATA of string list;
val datatypes = ref [] : string list ref;

let fun merge [] = DT_DATA []
      | merge ds = let val ds = map (fn DT_DATA x => x) ds;
                   in DT_DATA (foldl (op union) (hd ds, tl ds)) end;

    fun put (DT_DATA ds) = datatypes := ds;

    fun get () = DT_DATA (!datatypes);
in add_thydata HOL.thy
     ("datatypes", ThyMethods {merge = merge, put = put, get = get})
end;


add_thy_reader_file "thy_data.ML";
