(*  Title:      HOL/ind_syntax.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Abstract Syntax functions for Inductive Definitions
See also hologic.ML and ../Pure/section-utils.ML
*)

(*The structure protects these items from redeclaration (somewhat!).  The 
  datatype definitions in theory files refer to these items by name!
*)
structure Ind_Syntax =
struct

(** Abstract syntax definitions for HOL **)

open HOLogic;

fun Int_const T = 
  let val sT = mk_setT T
  in  Const("op Int", [sT,sT]--->sT)  end;

fun mk_exists (Free(x,T),P) = exists_const T $ (absfree (x,T,P));

fun mk_all (Free(x,T),P) = all_const T $ (absfree (x,T,P));

(*Creates All(%v.v:A --> P(v)) rather than Ball(A,P) *)
fun mk_all_imp (A,P) = 
  let val T = dest_setT (fastype_of A)
  in  all_const T $ Abs("v", T, imp $ (mk_mem (Bound 0, A)) $ (P $ Bound 0))
  end;

(** Disjoint sum type **)

fun mk_sum (T1,T2) = Type("+", [T1,T2]);
val Inl = Const("Inl", dummyT)
and Inr = Const("Inr", dummyT);         (*correct types added later!*)
(*val elim      = Const("case", [iT-->iT, iT-->iT, iT]--->iT)*)

fun summands (Type("+", [T1,T2])) = summands T1 @ summands T2
  | summands T                    = [T];

(*Given the destination type, fills in correct types of an Inl/Inr nest*)
fun mend_sum_types (h,T) =
    (case (h,T) of
         (Const("Inl",_) $ h1, Type("+", [T1,T2])) =>
             Const("Inl", T1 --> T) $ (mend_sum_types (h1, T1))
       | (Const("Inr",_) $ h2, Type("+", [T1,T2])) =>
             Const("Inr", T2 --> T) $ (mend_sum_types (h2, T2))
       | _ => h);



(*simple error-checking in the premises of an inductive definition*)
fun chk_prem rec_hd (Const("op &",_) $ _ $ _) =
        error"Premises may not be conjuctive"
  | chk_prem rec_hd (Const("op :",_) $ t $ X) = 
        deny (Logic.occs(rec_hd,t)) "Recursion term on left of member symbol"
  | chk_prem rec_hd t = 
        deny (Logic.occs(rec_hd,t)) "Recursion term in side formula";

(*Return the conclusion of a rule, of the form t:X*)
fun rule_concl rl = 
    let val Const("Trueprop",_) $ (Const("op :",_) $ t $ X) = 
                Logic.strip_imp_concl rl
    in  (t,X)  end;

(*As above, but return error message if bad*)
fun rule_concl_msg sign rl = rule_concl rl
    handle Bind => error ("Ill-formed conclusion of introduction rule: " ^ 
                          Sign.string_of_term sign rl);

(*For simplifying the elimination rule*)
val sumprod_free_SEs = 
    Pair_inject ::
    map make_elim [(*Inl_neq_Inr, Inr_neq_Inl, Inl_inject, Inr_inject*)];

(*For deriving cases rules.  
  read_instantiate replaces a propositional variable by a formula variable*)
val equals_CollectD = 
    read_instantiate [("W","?Q")]
        (make_elim (equalityD1 RS subsetD RS CollectD));

(*Delete needless equality assumptions*)
val refl_thin = prove_goal HOL.thy "!!P. [| a=a;  P |] ==> P"
     (fn _ => [assume_tac 1]);

(*Includes rules for Suc and Pair since they are common constructions*)
val elim_rls = [asm_rl, FalseE, (*Suc_neq_Zero, Zero_neq_Suc,
                make_elim Suc_inject, *)
                refl_thin, conjE, exE, disjE];

end;
