(*  Title:      HOL/inductive.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

(Co)Inductive Definitions for HOL

Inductive definitions use least fixedpoints with standard products and sums
Coinductive definitions use greatest fixedpoints with Quine products and sums

Sums are used only for mutual recursion;
Products are used only to derive "streamlined" induction rules for relations
*)

fun gen_fp_oper a (X,T,t) = 
    let val setT = Ind_Syntax.mk_setT T
    in Const(a, (setT-->setT)-->setT) $ absfree(X, setT, t)  end;

structure Lfp_items =
  struct
  val checkThy	= (fn thy => require_thy thy "Lfp" "inductive definitions")
  val oper      = gen_fp_oper "lfp"
  val Tarski    = def_lfp_Tarski
  val induct    = def_induct
  end;

structure Gfp_items =
  struct
  val checkThy	= (fn thy => require_thy thy "Gfp" "coinductive definitions")
  val oper      = gen_fp_oper "gfp"
  val Tarski    = def_gfp_Tarski
  val induct    = def_Collect_coinduct
  end;


functor Ind_section_Fun (Inductive: sig include INDUCTIVE_ARG INDUCTIVE_I end) 
  : sig include INTR_ELIM INDRULE end =
let
  structure Intr_elim = Intr_elim_Fun(structure Inductive=Inductive and 
                                          Fp=Lfp_items);

  structure Indrule = Indrule_Fun
      (structure Inductive=Inductive and Intr_elim=Intr_elim);
in 
   struct 
   val thy      = Intr_elim.thy
   val defs     = Intr_elim.defs
   val mono     = Intr_elim.mono
   val intrs    = Intr_elim.intrs
   val elim     = Intr_elim.elim
   val mk_cases = Intr_elim.mk_cases
   open Indrule 
   end
end;


structure Ind = Add_inductive_def_Fun (Lfp_items);


signature INDUCTIVE_STRING =
  sig
  val thy_name   : string               (*name of the new theory*)
  val srec_tms   : string list          (*recursion terms*)
  val sintrs     : string list          (*desired introduction rules*)
  end;


(*Called by the theory sections or directly from ML*)
functor Inductive_Fun
 (Inductive: sig include INDUCTIVE_STRING INDUCTIVE_ARG end)
   : sig include INTR_ELIM INDRULE end =
Ind_section_Fun
   (open Inductive Ind_Syntax
    val sign = sign_of thy;
    val rec_tms = map (readtm sign termTVar) srec_tms
    and intr_tms = map (readtm sign propT) sintrs;
    val thy = thy |> Ind.add_fp_def_i(rec_tms, intr_tms) 
                  |> add_thyname thy_name);



signature COINDRULE =
  sig
  val coinduct : thm
  end;


functor CoInd_section_Fun
 (Inductive: sig include INDUCTIVE_ARG INDUCTIVE_I end) 
    : sig include INTR_ELIM COINDRULE end =
struct
structure Intr_elim = Intr_elim_Fun(structure Inductive=Inductive and Fp=Gfp_items);

open Intr_elim 
val coinduct = raw_induct
end;


structure CoInd = Add_inductive_def_Fun(Gfp_items);
