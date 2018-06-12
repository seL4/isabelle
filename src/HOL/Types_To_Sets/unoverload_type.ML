(*  Title:      HOL/Types_To_Sets/unoverload_type.ML
    Author:     Fabian Immler, TU München

Internalize sorts and unoverload parameters of a type variable.
*)

signature UNOVERLOAD_TYPE =
sig
  val unoverload_type: Context.generic -> string -> thm -> thm
  val unoverload_type_attr: string -> attribute
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

fun unoverload_type context s thm =
  let
    val tvars = Term.add_tvars (Thm.prop_of thm) []
    val thy = Context.theory_of context
  in
  case find_first (fn ((n,_), _) => n = s) tvars of NONE =>
    raise THM ("unoverload_internalize_deps: type variable ("^s^") not in theorem", 0, [thm])
  | SOME (x as (_, sort)) =>
    let
      val (tvar, thm') = Internalize_Sort.internalize_sort (Thm.global_ctyp_of thy (TVar x)) thm
      val consts = params_of_sort context sort |>
        map (apsnd (map_type_tfree (fn ("'a", _) =>  tvar | x => TFree x)))
    in
      fold (fn c => Unoverloading.unoverload (Thm.global_cterm_of thy (Const c))) consts thm'
    end
  end

val tyN = (Args.context -- Args.typ) >>
  (fn (_, TFree (n, _)) => n
  | (ctxt, t) => error ("Not a type variable: " ^ Syntax.string_of_typ ctxt t))

fun unoverload_type_attr n = Thm.rule_attribute [] (fn context => unoverload_type context n)

val _ = Context.>> (Context.map_theory (Attrib.setup @{binding unoverload_type}
  (tyN >> unoverload_type_attr) "internalize a sort"))

end