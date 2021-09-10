(*  Title:      HOL/Types_To_Sets/unoverload_type.ML
    Author:     Fabian Immler, TU München

Internalize sorts and unoverload parameters of a type variable.
*)

signature UNOVERLOAD_TYPE =
sig
  val unoverload_type: Context.generic -> indexname list -> thm -> thm
  val unoverload_type_attr: indexname list -> attribute
end;

structure Unoverload_Type : UNOVERLOAD_TYPE =
struct

fun params_of_class thy class = try (Axclass.get_info thy #> #params) class |> these

fun params_of_super_classes thy class =
  class::Sorts.super_classes (Sign.classes_of thy) class |> maps (params_of_class thy)

fun params_of_sort thy sort = maps (params_of_super_classes thy) sort

fun subst_TFree n' ty' ty = map_type_tfree (fn x as (n, _) => if n = n' then ty' else TFree x) ty

fun unoverload_single_type context tvar thm =
  let
    val tvars = Term.add_tvars (Thm.prop_of thm) []
    val thy = Context.theory_of context
  in
  case find_first (fn (y, _) => tvar = y) tvars of NONE =>
    raise TYPE ("unoverload_type: no such type variable in theorem", [TVar (tvar,[])], [])
  | SOME (x as (_, sort)) =>
    let
      val (_, thm') = Internalize_Sort.internalize_sort (Thm.global_ctyp_of thy (TVar x)) thm
      val prop' =
        fold (fn _ => Term.dest_comb #> #2)
          (replicate (Thm.nprems_of thm' - Thm.nprems_of thm) ()) (Thm.prop_of thm')
      val (tyenv, _) = Pattern.first_order_match thy ((prop', Thm.prop_of thm))
        (Vartab.empty, Vartab.empty)
      val tyenv_list = tyenv |> Vartab.dest
        |> map (fn (x, (s, TVar (x', _))) =>
          ((x, s), Thm.ctyp_of (Context.proof_of context) (TVar(x', s))))
      val thm'' = Drule.instantiate_normalize (TVars.make tyenv_list, Vars.empty) thm'
      val varify_const =
        apsnd (subst_TFree "'a" (TVar (tvar, @{sort type}))) #> Const #> Thm.global_cterm_of thy
      val consts = params_of_sort thy sort
        |> map varify_const
    in
      fold Unoverloading.unoverload consts thm''
      |> Raw_Simplifier.norm_hhf (Context.proof_of context)
    end
  end

fun unoverload_type context xs = fold (unoverload_single_type context) xs

fun unoverload_type_attr xs = Thm.rule_attribute [] (fn context => unoverload_type context xs)

val _ = Context.>> (Context.map_theory (Attrib.setup \<^binding>\<open>unoverload_type\<close>
  (Scan.lift (Scan.repeat Args.var) >> unoverload_type_attr)
    "internalize and unoverload type class parameters"))

end