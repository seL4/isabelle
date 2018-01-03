(*  Title:      HOL/Tools/Old_Datatype/old_datatype.ML
    Author:     Stefan Berghofer, TU Muenchen

Pieces left from the old datatype package.
*)

signature OLD_DATATYPE =
sig
  include OLD_DATATYPE_COMMON

  val distinct_lemma: thm
  type spec_cmd =
    (binding * (string * string option) list * mixfix) * (binding * string list * mixfix) list
  val read_specs: spec_cmd list -> theory -> spec list * Proof.context
  val check_specs: spec list -> theory -> spec list * Proof.context
end;

structure Old_Datatype : OLD_DATATYPE =
struct

val distinct_lemma = @{lemma "f x \<noteq> f y ==> x \<noteq> y" by iprover};

type spec_cmd =
  (binding * (string * string option) list * mixfix) * (binding * string list * mixfix) list;

fun parse_spec ctxt ((b, args, mx), constrs) =
  ((b, map (apsnd (Typedecl.read_constraint ctxt)) args, mx),
    constrs |> map (fn (c, Ts, mx') => (c, map (Syntax.parse_typ ctxt) Ts, mx')));

fun check_specs ctxt (specs: Old_Datatype_Aux.spec list) =
  let
    fun prep_spec ((tname, args, mx), constrs) tys =
      let
        val (args', tys1) = chop (length args) tys;
        val (constrs', tys3) = (constrs, tys1) |-> fold_map (fn (cname, cargs, mx') => fn tys2 =>
          let val (cargs', tys3) = chop (length cargs) tys2;
          in ((cname, cargs', mx'), tys3) end);
      in (((tname, map dest_TFree args', mx), constrs'), tys3) end;

    val all_tys =
      specs |> maps (fn ((_, args, _), cs) => map TFree args @ maps #2 cs)
      |> Syntax.check_typs ctxt;

  in #1 (fold_map prep_spec specs all_tys) end;

fun prep_specs parse raw_specs thy =
  let
    val ctxt = thy
      |> Sign.add_types_global (map (fn ((b, args, mx), _) => (b, length args, mx)) raw_specs)
      |> Proof_Context.init_global
      |> fold (fn ((_, args, _), _) => fold (fn (a, _) =>
          Variable.declare_typ (TFree (a, dummyS))) args) raw_specs;
    val specs = check_specs ctxt (map (parse ctxt) raw_specs);
  in (specs, ctxt) end;

val read_specs = prep_specs parse_spec;
val check_specs = prep_specs (K I);

open Old_Datatype_Aux;

end;
