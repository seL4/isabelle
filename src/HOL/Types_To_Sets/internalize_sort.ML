(*  Title:      HOL/Types_To_Sets/internalize_sort.ML
    Author:     Ondřej Kunčar, TU München

A derived rule (by using Thm.unconstrainT) that internalizes
type class annotations.
*)


(*
                     \<phi>['a::{c_1, ..., c_n} / 'a]
---------------------------------------------------------------------
  class.c_1 ops_1 \<Longrightarrow> ... \<Longrightarrow> class.c_n ops_n \<Longrightarrow> \<phi>['a::type / 'a]

where class.c is the locale predicate associated with type class c and
ops are operations associated with type class c. For example:
If c = semigroup_add, then ops = op-, op+, 0, uminus.
If c = finite, then ops = TYPE('a::type).
*)

signature INTERNALIZE_SORT =
sig
  val internalize_sort:  ctyp -> thm -> typ * thm
  val internalize_sort_attr: typ -> attribute
end;

structure Internalize_Sort : INTERNALIZE_SORT =
struct

fun internalize_sort ctvar thm =
  let
    val thy = Thm.theory_of_thm thm;
    val tvar = Thm.typ_of ctvar;

    val ((_, assms, classes),_) = Logic.unconstrainT [] (Thm.prop_of thm);

    fun is_proper_class thy = can (Axclass.get_info thy); (* trick by FH *)
    fun reduce_to_non_proper_sort (TVar (name, sort)) =
        TVar (name, Sign.minimize_sort thy (filter_out (is_proper_class thy) (Sign.complete_sort thy sort)))
      | reduce_to_non_proper_sort _ = error "not supported";

    val data = (map fst classes) ~~ assms;

    val new_tvar = get_first (fn (tvar', ((ren_tvar, _), _)) => if tvar = tvar'
      then SOME (reduce_to_non_proper_sort ren_tvar) else NONE) data
      |> the_default tvar;

    fun localify class = Class.rules thy class |> snd |> Thm.transfer thy;

    fun discharge_of_class tvar class = Thm.of_class (Thm.global_ctyp_of thy tvar, class);

    val rules = map (fn (tvar', ((ren_tvar, class), _)) => if tvar = tvar'
      then (if Class.is_class thy class then localify class else discharge_of_class ren_tvar class)
      else discharge_of_class ren_tvar class) data;
  in
    (new_tvar, (Thm.unconstrainT (Thm.strip_shyps thm) OF rules) |> Drule.zero_var_indexes)
  end;

val tvar = Args.context -- Args.typ >> (fn (_, v as TFree _) => Logic.varifyT_global v
  | (ctxt, t) => error ("Not a type variable: " ^ Syntax.string_of_typ ctxt t));

fun internalize_sort_attr tvar =
  Thm.rule_attribute [] (fn context => fn thm =>
    (snd (internalize_sort (Thm.ctyp_of (Context.proof_of context) tvar) thm)));

val _ = Context.>> (Context.map_theory (Attrib.setup \<^binding>\<open>internalize_sort\<close>
  (tvar >> internalize_sort_attr) "internalize a sort"));

end;
