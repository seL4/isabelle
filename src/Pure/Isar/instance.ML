(*  Title:      Pure/Isar/instance.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

A primitive instance command, based on instantiation target.
*)

signature INSTANCE =
sig
  val instantiation_cmd: xstring list * sort * xstring -> theory -> local_theory
  val instance_cmd: xstring * sort * xstring -> ((bstring * Attrib.src list) * xstring) list
    -> theory -> Proof.state
end;

structure Instance : INSTANCE =
struct

fun read_single_arity thy (raw_tyco, raw_sorts, raw_sort) =
  let
    val (tyco, sorts, sort) = Sign.read_arity thy (raw_tyco, raw_sorts, raw_sort);
    val vs = Name.names Name.context Name.aT sorts;
  in (tyco, vs, sort) end;

fun read_multi_arity thy (raw_tycos, raw_sorts, raw_sort) =
  let
    val all_arities = map (fn raw_tyco => Sign.read_arity thy
      (raw_tyco, raw_sorts, raw_sort)) raw_tycos;
    val tycos = map #1 all_arities;
    val (_, sorts, sort) = hd all_arities;
    val vs = Name.names Name.context Name.aT sorts;
  in (tycos, vs, sort) end;

fun instantiation_cmd raw_arities thy =
  TheoryTarget.instantiation (read_multi_arity thy raw_arities) thy;

fun instance_cmd raw_arities defs thy =
  let
    val (tyco, vs, sort) = read_single_arity thy raw_arities;
    fun mk_def ctxt ((name, raw_attr), raw_t) =
      let
        val attr = map (Attrib.intern_src thy) raw_attr;
        val t = Syntax.parse_prop ctxt raw_t;
      in (NONE, ((name, attr), t)) end;
    fun define def ctxt =
      let
        val def' = (apsnd o apsnd) (Syntax.check_prop ctxt) def;
      in Specification.definition def' ctxt end;
    val _ = if not (null defs) then Output.legacy_feature
      "Instance command with attached definitions; use instantiation instead." else ();
  in if not (null defs) orelse forall (Class.is_class thy) sort
  then
    thy
    |> TheoryTarget.instantiation ([tyco], vs, sort)
    |> `(fn ctxt => map (mk_def ctxt) defs)
    |-> (fn defs => fold_map Specification.definition defs)
    |> snd
    |> LocalTheory.restore
    |> Class.instantiation_instance Class.conclude_instantiation
  else
    thy
    |> Class.instance_arity I (tyco, map snd vs, sort)
  end;

end;
