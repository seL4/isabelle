(*  Title:      HOL/Tools/function_package/inductive_wrap.ML
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen


This is a wrapper around the inductive package which corrects some of its
slightly annoying behaviours and makes the whole business more controllable.

Specifically:

- Following newer Isar conventions, declaration and definition are done in one step

- The specification is expected in fully quantified form. This allows the client to 
  control the variable order. The variables will appear in the result in the same order.
  This is especially relevant for the elimination rule, where the order usually *does* matter.


All this will probably become obsolete in the near future, when the new "predicate" package
is in place.

*)

signature FUNDEF_INDUCTIVE_WRAP =
sig
  val inductive_def :  term list 
                       -> ((bstring * typ) * mixfix) * local_theory
                       -> thm list * (term * thm * local_theory)
end

structure FundefInductiveWrap =
struct

open FundefLib

fun requantify ctxt lfix (qs, t) thm =
    let
      val thy = theory_of_thm thm
      val frees = frees_in_term ctxt t 
                                  |> remove (op =) lfix
      val vars = Term.add_vars (prop_of thm) [] |> rev
                 
      val varmap = frees ~~ vars
    in
      fold_rev (fn Free (n, T) => 
                   forall_intr_rename (n, cterm_of thy (Var (the_default (("",0), T) (AList.lookup (op =) varmap (n, T))))))
               qs
               thm
    end             
  
  

fun inductive_def defs (((R, T), mixfix), lthy) =
    let
      val qdefs = map dest_all_all defs
                  
      val (lthy, {intrs = intrs_gen, elims = [elim_gen], preds = [ Rdef ], ...}) =
          InductivePackage.add_inductive_i true (*verbose*)
                                           "" (* no altname *)
                                           false (* no coind *)
                                           false (* elims, please *)
                                           false (* induction thm please *)
                                           [(R, SOME T, NoSyn)] (* the relation *)
                                           [] (* no parameters *)
                                           (map (fn t => (("", []), t)) defs) (* the intros *)
                                           [] (* no special monos *)
                                           lthy

      val thy = ProofContext.theory_of lthy
                
      fun inst qdef intr_gen =
          intr_gen
            |> Thm.freezeT
            |> requantify lthy (R, T) qdef 
          
      val intrs = map2 inst qdefs intrs_gen
                  
      val elim = elim_gen
                   |> Thm.freezeT
                   |> forall_intr_vars (* FIXME... *)

      val Rdef_real = prop_of (Thm.freezeT elim_gen)
                       |> Logic.dest_implies |> fst
                       |> Term.strip_comb |> snd |> hd (* Trueprop *)
                       |> Term.strip_comb |> fst
    in
      (intrs, (Rdef_real, elim, lthy))
    end
    
end

