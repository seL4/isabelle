(*  Title:      HOL/Tools/Function/inductive_wrap.ML
    Author:     Alexander Krauss, TU Muenchen


A wrapper around the inductive package, restoring the quantifiers in
the introduction and elimination rules.
*)

signature FUNCTION_INDUCTIVE_WRAP =
sig
  val inductive_def :  term list 
                       -> ((bstring * typ) * mixfix) * local_theory
                       -> thm list * (term * thm * thm * local_theory)
end

structure Function_Inductive_Wrap: FUNCTION_INDUCTIVE_WRAP =
struct

open Function_Lib

fun requantify ctxt lfix orig_def thm =
    let
      val (qs, t) = dest_all_all orig_def
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
      val ({intrs = intrs_gen, elims = [elim_gen], preds = [ Rdef ], induct, ...}, lthy) =
          Inductive.add_inductive_i
            {quiet_mode = false,
              verbose = ! Toplevel.debug,
              kind = Thm.internalK,
              alt_name = Binding.empty,
              coind = false,
              no_elim = false,
              no_ind = false,
              skip_mono = true,
              fork_mono = false}
            [((Binding.name R, T), NoSyn)] (* the relation *)
            [] (* no parameters *)
            (map (fn t => (Attrib.empty_binding, t)) defs) (* the intros *)
            [] (* no special monos *)
            lthy

      val intrs = map2 (requantify lthy (R, T)) defs intrs_gen
                  
      val elim = elim_gen
                   |> forall_intr_vars (* FIXME... *)

    in
      (intrs, (Rdef, elim, induct, lthy))
    end
    
end
