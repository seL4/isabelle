(*  Title:      Pure/Isar/instance.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

A primitive instance command, based on instantiation target.
*)

signature INSTANCE =
sig
  val instantiate: string list * sort list * sort -> (local_theory -> 'a * local_theory)
    -> (Proof.context -> 'a -> tactic) -> theory -> theory

  val instantiation_cmd: xstring list * sort * xstring -> theory -> local_theory
  val instance_cmd: xstring * sort * xstring -> ((bstring * Attrib.src list) * xstring) list
    -> theory -> Proof.state
end;

structure Instance : INSTANCE =
struct

fun read_multi_arity thy (raw_tycos, raw_sorts, raw_sort) =
  let
    val all_arities = map (fn raw_tyco => Sign.read_arity thy
      (raw_tyco, raw_sorts, raw_sort)) raw_tycos;
    val tycos = map #1 all_arities;
    val (_, sorts, sort) = hd all_arities;
  in (tycos, sorts, sort) end;

fun instantiation_cmd raw_arities thy =
  TheoryTarget.instantiation (read_multi_arity thy raw_arities) thy;

fun instantiate arities f tac =
  TheoryTarget.instantiation arities
  #> f
  #-> (fn result => Class.prove_instantiation_instance (fn ctxt => tac ctxt result))
  #> LocalTheory.exit
  #> ProofContext.theory_of;

fun gen_instance prep_arity prep_attr parse_term do_proof do_proof' raw_arities defs thy =
  let
    val (tyco, sorts, sort) = prep_arity thy raw_arities;
    fun export_defs ctxt = 
      let
        val ctxt_thy = ProofContext.init (ProofContext.theory_of ctxt);
      in
        map (snd o snd)
        #> map (Assumption.export false ctxt ctxt_thy)
        #> Variable.export ctxt ctxt_thy
      end;
    fun mk_def ctxt ((name, raw_attr), raw_t) =
      let
        val attr = map (prep_attr thy) raw_attr;
        val t = parse_term ctxt raw_t;
      in (NONE, ((name, attr), t)) end;
    fun define def ctxt =
      let
        val def' = (apsnd o apsnd) (Syntax.check_prop ctxt) def;
      in Specification.definition def' ctxt end;
  in if not (null defs) orelse forall (Class.is_class thy) sort
  then
    thy
    |> TheoryTarget.instantiation ([tyco], sorts, sort)
    |> `(fn ctxt => map (mk_def ctxt) defs)
    |-> (fn defs => fold_map Specification.definition defs)
    |-> (fn defs => `(fn ctxt => export_defs ctxt defs))
    ||> LocalTheory.reinit
    |-> (fn defs => do_proof defs)
  else
    thy
    |> do_proof' (tyco, sorts, sort)
  end;

val instance_cmd = gen_instance Sign.read_arity Attrib.intern_src Syntax.parse_prop
  (fn _ => Class.instantiation_instance Class.conclude_instantiation) (Class.instance_arity I);

end;
