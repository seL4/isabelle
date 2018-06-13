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

fun those [] = []
  | those (NONE::xs) = those xs
  | those (SOME x::xs) = x::those xs

fun params_of_sort context sort =
  let
    val algebra = Sign.classes_of (Context.theory_of context)
    val params = List.concat (map (Sorts.super_classes algebra) sort) |>
      map (try (Axclass.get_info (Context.theory_of context))) |>
      those |>
      map #params |>
      List.concat
  in params end

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
      val consts = params_of_sort context sort |>
        map (apsnd (map_type_tfree (fn ("'a", _) =>  tvar | x => TFree x)))
    in
      fold (fn c => Unoverloading.unoverload (Thm.global_cterm_of thy (Const c))) consts thm'
    end
  end

fun unoverload_type context xs = fold (unoverload_single_type context) xs

fun unoverload_type_attr xs = Thm.rule_attribute [] (fn context => unoverload_type context xs)

val _ = Context.>> (Context.map_theory (Attrib.setup @{binding unoverload_type}
  (Scan.lift (Scan.repeat Args.var) >> unoverload_type_attr)
    "internalize and unoverload type class parameters"))

end