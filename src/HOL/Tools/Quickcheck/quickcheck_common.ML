(*  Title:      HOL/Tools/Quickcheck/quickcheck_common.ML
    Author:     Florian Haftmann, Lukas Bulwahn, TU Muenchen

Common functions for quickcheck's generators

*)

signature QUICKCHECK_COMMON =
sig
  val perhaps_constrain: theory -> (typ * sort) list -> (string * sort) list
    -> (string * sort -> string * sort) option
  val ensure_sort_datatype:
    sort * (Datatype.config -> Datatype.descr -> (string * sort) list -> string list -> string ->
      string list * string list -> typ list * typ list -> theory -> theory)
    -> Datatype.config -> string list -> theory -> theory
end;

structure Quickcheck_Common : QUICKCHECK_COMMON =
struct

fun perhaps_constrain thy insts raw_vs =
  let
    fun meet (T, sort) = Sorts.meet_sort (Sign.classes_of thy) 
      (Logic.varifyT_global T, sort);
    val vtab = Vartab.empty
      |> fold (fn (v, sort) => Vartab.update ((v, 0), sort)) raw_vs
      |> fold meet insts;
  in SOME (fn (v, _) => (v, (the o Vartab.lookup vtab) (v, 0)))
  end handle Sorts.CLASS_ERROR _ => NONE;

fun ensure_sort_datatype (sort, instantiate_datatype) config raw_tycos thy =
  let
    val algebra = Sign.classes_of thy;
    val (descr, raw_vs, tycos, prfx, (names, auxnames), raw_TUs) =
      Datatype.the_descr thy raw_tycos;
    val typerep_vs = (map o apsnd)
      (curry (Sorts.inter_sort algebra) @{sort typerep}) raw_vs;
    val sort_insts = (map (rpair sort) o flat o maps snd o maps snd)
      (Datatype_Aux.interpret_construction descr typerep_vs
        { atyp = single, dtyp = (K o K o K) [] });
    val term_of_insts = (map (rpair @{sort term_of}) o flat o maps snd o maps snd)
      (Datatype_Aux.interpret_construction descr typerep_vs
        { atyp = K [], dtyp = K o K });
    val has_inst = exists (fn tyco =>
      can (Sorts.mg_domain algebra tyco) sort) tycos;
  in if has_inst then thy
    else case perhaps_constrain thy (sort_insts @ term_of_insts) typerep_vs
     of SOME constrain => instantiate_datatype config descr
          (map constrain typerep_vs) tycos prfx (names, auxnames)
            ((pairself o map o map_atyps) (fn TFree v => TFree (constrain v)) raw_TUs) thy
      | NONE => thy
  end;

end;
