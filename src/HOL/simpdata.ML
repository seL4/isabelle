(*  Title:      HOL/simpdata.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1991  University of Cambridge

Instantiation of the generic simplifier
*)

section "Simplifier";

open Simplifier;

(*** Integration of simplifier with classical reasoner ***)

(*Add a simpset to a classical set!*)
infix 4 addss;
fun cs addss ss = cs addbefore asm_full_simp_tac ss 1;

fun Addss ss = (claset := !claset addbefore asm_full_simp_tac ss 1);

(*Designed to be idempotent, except if best_tac instantiates variables
  in some of the subgoals*)
fun auto_tac (cs,ss) = 
    ALLGOALS (asm_full_simp_tac ss) THEN
    REPEAT (safe_tac cs THEN ALLGOALS (asm_full_simp_tac ss)) THEN
    REPEAT (FIRSTGOAL (best_tac (cs addss ss))) THEN
    prune_params_tac;

fun Auto_tac() = auto_tac (!claset, !simpset);

fun auto() = by (Auto_tac());


(*** Addition of rules to simpsets and clasets simultaneously ***)

(*Takes UNCONDITIONAL theorems of the form A<->B to 
        the Safe Intr     rule B==>A and 
        the Safe Destruct rule A==>B.
  Also ~A goes to the Safe Elim rule A ==> ?R
  Failing other cases, A is added as a Safe Intr rule*)
local
  val iff_const = HOLogic.eq_const HOLogic.boolT;

  fun addIff th = 
      (case HOLogic.dest_Trueprop (#prop(rep_thm th)) of
                (Const("not",_) $ A) =>
                    AddSEs [zero_var_indexes (th RS notE)]
              | (con $ _ $ _) =>
                    if con=iff_const
                    then (AddSIs [zero_var_indexes (th RS iffD2)];  
                          AddSDs [zero_var_indexes (th RS iffD1)])
                    else  AddSIs [th]
              | _ => AddSIs [th];
       Addsimps [th])
      handle _ => error ("AddIffs: theorem must be unconditional\n" ^ 
                         string_of_thm th)

  fun delIff th = 
      (case HOLogic.dest_Trueprop (#prop(rep_thm th)) of
                (Const("not",_) $ A) =>
                    Delrules [zero_var_indexes (th RS notE)]
              | (con $ _ $ _) =>
                    if con=iff_const
                    then Delrules [zero_var_indexes (th RS iffD2),
                                   zero_var_indexes (th RS iffD1)]
                    else Delrules [th]
              | _ => Delrules [th];
       Delsimps [th])
      handle _ => warning("DelIffs: ignoring conditional theorem\n" ^ 
                          string_of_thm th)
in
val AddIffs = seq addIff
val DelIffs = seq delIff
end;


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

in

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
   "((~P) = (~Q)) = (P=Q)",
   "(!x.P) = P", "(? x.P) = P", "? x. x=t", "? x. t=x", 
   "(? x. x=t & P(x)) = P(t)", "(? x. t=x & P(x)) = P(t)", 
   "(! x. x=t --> P(x)) = P(t)", "(! x. t=x --> P(x)) = P(t)" ];

val meta_eq_to_obj_eq = prove_goal HOL.thy "x==y ==> x=y"
  (fn [prem] => [rewtac prem, rtac refl 1]);

val eq_sym_conv = prover "(x=y) = (y=x)";

val conj_assoc = prover "((P&Q)&R) = (P&(Q&R))";

val disj_assoc = prover "((P|Q)|R) = (P|(Q|R))";

val imp_disj   = prover "(P|Q --> R) = ((P-->R)&(Q-->R))";

(*Avoids duplication of subgoals after expand_if, when the true and false 
  cases boil down to the same thing.*) 
val cases_simp = prover "((P --> Q) & (~P --> Q)) = Q";

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
         stac if_P 2,
         stac if_not_P 1,
         REPEAT(fast_tac HOL_cs 1) ]);

val if_bool_eq = prove_goal HOL.thy
                   "(if P then Q else R) = ((P-->Q) & (~P-->R))"
                   (fn _ => [rtac expand_if 1]);

(*Add congruence rules for = (instead of ==) *)
infix 4 addcongs;
fun ss addcongs congs = ss addeqcongs (congs RL [eq_reflection]);

fun Addcongs congs = (simpset := !simpset addcongs congs);

val mksimps_pairs =
  [("op -->", [mp]), ("op &", [conjunct1,conjunct2]),
   ("All", [spec]), ("True", []), ("False", []),
   ("If", [if_bool_eq RS iffD1])];

fun mksimps pairs = map mk_meta_eq o atomize pairs o gen_all;

val imp_cong = impI RSN
    (2, prove_goal HOL.thy "(P=P')--> (P'--> (Q=Q'))--> ((P-->Q) = (P'-->Q'))"
        (fn _=> [fast_tac HOL_cs 1]) RS mp RS mp);

val o_apply = prove_goalw HOL.thy [o_def] "(f o g) x = f (g x)"
 (fn _ => [rtac refl 1]);

(*Miniscoping: pushing in existential quantifiers*)
val ex_simps = map prover 
                ["(EX x. P x & Q)   = ((EX x.P x) & Q)",
                 "(EX x. P & Q x)   = (P & (EX x.Q x))",
                 "(EX x. P x | Q)   = ((EX x.P x) | Q)",
                 "(EX x. P | Q x)   = (P | (EX x.Q x))",
                 "(EX x. P x --> Q) = ((ALL x.P x) --> Q)",
                 "(EX x. P --> Q x) = (P --> (EX x.Q x))"];

(*Miniscoping: pushing in universal quantifiers*)
val all_simps = map prover
                ["(ALL x. P x & Q)   = ((ALL x.P x) & Q)",
                 "(ALL x. P & Q x)   = (P & (ALL x.Q x))",
                 "(ALL x. P x | Q)   = ((ALL x.P x) | Q)",
                 "(ALL x. P | Q x)   = (P | (ALL x.Q x))",
                 "(ALL x. P x --> Q) = ((EX x.P x) --> Q)",
                 "(ALL x. P --> Q x) = (P --> (ALL x.Q x))"];

(*In general it seems wrong to add distributive laws by default: they
  might cause exponential blow-up.  But imp_disj has been in for a while
  and cannot be removed without affecting existing proofs.  Moreover, 
  rewriting by "(P|Q --> R) = ((P-->R)&(Q-->R))" might be justified on the
  grounds that it allows simplification of R in the two cases.*)


local val mktac = mk_case_split_tac (meta_eq_to_obj_eq RS iffD2)
in
fun split_tac splits = mktac (map mk_meta_eq splits)
end;

local val mktac = mk_case_split_inside_tac (meta_eq_to_obj_eq RS iffD2)
in
fun split_inside_tac splits = mktac (map mk_meta_eq splits)
end;


(* elimination of existential quantifiers in assumptions *)

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

val conj_cong = 
  let val th = prove_goal HOL.thy 
                "(P=P')--> (P'--> (Q=Q'))--> ((P&Q) = (P'&Q'))"
                (fn _=> [fast_tac HOL_cs 1])
  in  standard (impI RSN (2, th RS mp RS mp))  end;

val rev_conj_cong =
  let val th = prove_goal HOL.thy 
                "(Q=Q')--> (Q'--> (P=P'))--> ((P&Q) = (P'&Q'))"
                (fn _=> [fast_tac HOL_cs 1])
  in  standard (impI RSN (2, th RS mp RS mp))  end;

(* '|' congruence rule: not included by default! *)

val disj_cong = 
  let val th = prove_goal HOL.thy 
                "(P=P')--> (~P'--> (Q=Q'))--> ((P|Q) = (P'|Q'))"
                (fn _=> [fast_tac HOL_cs 1])
  in  standard (impI RSN (2, th RS mp RS mp))  end;

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

prove "disj_commute" "(P|Q) = (Q|P)";
prove "disj_left_commute" "(P|(Q|R)) = (Q|(P|R))";
val disj_comms = [disj_commute, disj_left_commute];

prove "conj_disj_distribL" "(P&(Q|R)) = (P&Q | P&R)";
prove "conj_disj_distribR" "((P|Q)&R) = (P&R | Q&R)";

prove "disj_conj_distribL" "(P|(Q&R)) = ((P|Q) & (P|R))";
prove "disj_conj_distribR" "((P&Q)|R) = ((P|R) & (Q|R))";

prove "imp_conj_distrib" "(P --> (Q&R)) = ((P-->Q) & (P-->R))";
prove "imp_conj"         "((P&Q)-->R)   = (P --> (Q --> R))";

prove "de_Morgan_disj" "(~(P | Q)) = (~P & ~Q)";
prove "de_Morgan_conj" "(~(P & Q)) = (~P | ~Q)";
prove "not_iff" "(P~=Q) = (P = (~Q))";

prove "not_all" "(~ (! x.P(x))) = (? x.~P(x))";
prove "imp_all" "((! x. P x) --> Q) = (? x. P x --> Q)";
prove "not_ex"  "(~ (? x.P(x))) = (! x.~P(x))";
prove "imp_ex" "((? x. P x) --> Q) = (! x. P x --> Q)";

prove "ex_disj_distrib" "(? x. P(x) | Q(x)) = ((? x. P(x)) | (? x. Q(x)))";
prove "all_conj_distrib" "(!x. P(x) & Q(x)) = ((! x. P(x)) & (! x. Q(x)))";


val HOL_ss = empty_ss
      setmksimps (mksimps mksimps_pairs)
      setsolver (fn prems => resolve_tac (TrueI::refl::prems) ORELSE' atac
                             ORELSE' etac FalseE)
      setsubgoaler asm_simp_tac
      addsimps ([if_True, if_False, o_apply, imp_disj, conj_assoc, disj_assoc,
                 de_Morgan_conj, de_Morgan_disj, not_all, not_ex, cases_simp]
        @ ex_simps @ all_simps @ simp_thms)
      addcongs [imp_cong];


qed_goal "if_cancel" HOL.thy "(if c then x else x) = x"
  (fn _ => [simp_tac (HOL_ss setloop (split_tac [expand_if])) 1]);

qed_goal "if_distrib" HOL.thy
  "f(if c then x else y) = (if c then f x else f y)" 
  (fn _ => [simp_tac (HOL_ss setloop (split_tac [expand_if])) 1]);

bind_thm ("o_apply", o_apply);

qed_goalw "o_assoc" HOL.thy [o_def] "f o (g o h) = f o g o h"
  (fn _ => [rtac ext 1, rtac refl 1]);




(*** Install simpsets and datatypes in theory structure ***)

simpset := HOL_ss;

exception SS_DATA of simpset;

let fun merge [] = SS_DATA empty_ss
      | merge ss = let val ss = map (fn SS_DATA x => x) ss;
                   in SS_DATA (foldl merge_ss (hd ss, tl ss)) end;

    fun put (SS_DATA ss) = simpset := ss;

    fun get () = SS_DATA (!simpset);
in add_thydata "HOL"
     ("simpset", ThyMethods {merge = merge, put = put, get = get})
end;

type dtype_info = {case_const:term, case_rewrites:thm list,
                   constructors:term list, nchotomy:thm, case_cong:thm};

exception DT_DATA of (string * dtype_info) list;
val datatypes = ref [] : (string * dtype_info) list ref;

let fun merge [] = DT_DATA []
      | merge ds =
          let val ds = map (fn DT_DATA x => x) ds;
          in DT_DATA (foldl (gen_union eq_fst) (hd ds, tl ds)) end;

    fun put (DT_DATA ds) = datatypes := ds;

    fun get () = DT_DATA (!datatypes);
in add_thydata "HOL"
     ("datatypes", ThyMethods {merge = merge, put = put, get = get})
end;


add_thy_reader_file "thy_data.ML";
