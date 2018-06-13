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

fun internalize_sort' ctvar thm =
  let
    val (_, thm') = Internalize_Sort.internalize_sort ctvar thm
    val class_premise = case Thm.prems_of thm' of t::_=> t | [] =>
      raise THM ("internalize_sort': no premise?", 0, [thm'])
    val class_vars = Term.add_tvars class_premise []
    val tvar = case class_vars of [x] => TVar x | _ =>
      raise TERM ("internalize_sort': not one type class variable.", [class_premise])
  in
    (tvar, thm')
  end

fun params_of_class thy class = try (Axclass.get_info thy #> #params) class |> these

fun params_of_super_classes thy class =
  Sorts.super_classes (Sign.classes_of thy) class |> maps (params_of_class thy)

fun params_of_sort thy sort = maps (params_of_super_classes thy) sort

fun subst_TFree n' ty' ty = map_type_tfree (fn x as (n, _) => if n = n' then ty' else TFree x) ty

fun unoverload_single_type context x thm =
  let
    val tvars = Term.add_tvars (Thm.prop_of thm) []
    val thy = Context.theory_of context
  in
  case find_first (fn (y, _) => x = y) tvars of NONE =>
    raise THM ("unoverload_type: type variable ("^(@{make_string} x)^") not in theorem", 0, [thm])
  | SOME (x as (_, sort)) =>
    let
      val (tvar, thm') = internalize_sort' (Thm.global_ctyp_of thy (TVar x)) thm
      val consts = params_of_sort thy sort
        |> map (apsnd (subst_TFree "'a" tvar) #> Const #> Thm.global_cterm_of thy)
    in
      fold Unoverloading.unoverload consts thm'
      |> Raw_Simplifier.norm_hhf (Context.proof_of context)
    end
  end

fun unoverload_type context xs = fold (unoverload_single_type context) xs

fun unoverload_type_attr xs = Thm.rule_attribute [] (fn context => unoverload_type context xs)

val _ = Context.>> (Context.map_theory (Attrib.setup @{binding unoverload_type}
  (Scan.lift (Scan.repeat Args.var) >> unoverload_type_attr)
    "internalize and unoverload type class parameters"))

end