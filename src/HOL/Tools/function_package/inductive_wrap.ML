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


fun inst_forall (Free (n,_)) (_ $ Abs (_, T, b)) = subst_bound (Free (n, T), b)
  | inst_forall t1 t2 = sys_error ((Sign.string_of_term (the_context ()) t1))

fun permute_bounds_in_premises thy [] impl = impl
  | permute_bounds_in_premises thy ((oldvs, newvs) :: perms) impl =
    let
      val (prem, concl) = dest_implies (cprop_of impl)

      val newprem = term_of prem
                      |> fold inst_forall oldvs
                      |> fold_rev mk_forall newvs
                      |> cterm_of thy
    in
      assume newprem
             |> fold (forall_elim o cterm_of thy) newvs
             |> fold_rev (forall_intr o cterm_of thy) oldvs
             |> implies_elim impl
             |> permute_bounds_in_premises thy perms
             |> implies_intr newprem
    end


fun inductive_def defs (((R, T), mixfix), lthy) =
    let
      fun wrap1 thy =
          let
            val thy = Sign.add_consts_i [(R, T, mixfix)] thy
            val RC = Const (Sign.full_name thy R, T)

            val cdefs = map (Pattern.rewrite_term thy [(Free (R, T), RC)] []) defs
            val qdefs = map dest_all_all cdefs

            val (thy, {intrs = intrs_gen, elims = [elim_gen], ...}) =
                OldInductivePackage.add_inductive_i true (*verbose*)
                                                 false (* dont add_consts *)
                                                 "" (* no altname *)
                                                 false (* no coind *)
                                                 false (* elims, please *)
                                                 false (* induction thm please *)
                                                 [RC] (* the constant *)
                                                 (map (fn (_,t) => (("", t),[])) qdefs) (* the intros *)
                                                 [] (* no special monos *)
                                                 thy

            val perms = map (fn (qs, t) => ((term_frees t) inter qs, qs)) qdefs

            fun inst (qs, _) intr_gen =
                intr_gen
                  |> Thm.freezeT
                  |> fold_rev (forall_intr o (fn Free (n, T) => cterm_of thy (Var ((n,0), T)))) qs


            val a = cterm_of thy (Free ("a0123", HOLogic.dest_setT T)) (* Let's just hope there are no clashes :-} *)
            val P = cterm_of thy (Free ("P0123", HOLogic.boolT))
                
            val intrs = map2 inst qdefs intrs_gen

            val elim = elim_gen
                         |> Thm.freezeT
                         |> forall_intr_vars (* FIXME... *)
                         |> forall_elim a
                         |> forall_elim P
                         |> permute_bounds_in_premises thy (([],[]) :: perms)
                         |> forall_intr P
                         |> forall_intr a
          in
            ((RC, (intrs, elim)), thy)
          end

      val ((RC, (intrs, elim)), lthy) = LocalTheory.theory_result wrap1 lthy
    in
      (intrs, (RC, elim, lthy))
    end


end

