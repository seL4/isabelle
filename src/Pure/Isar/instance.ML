(*  Title:      Pure/Isar/instance.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

A primitive instance command, based on instantiation target.
*)

signature INSTANCE =
sig
  val instantiate: arity list -> (local_theory -> local_theory)
    -> (Proof.context -> tactic) -> theory -> theory
  val instance: arity list -> ((bstring * Attrib.src list) * term) list
    -> (thm list -> theory -> theory)
    -> theory -> Proof.state
  val prove_instance: tactic -> arity list -> ((bstring * Attrib.src list) * term) list
    -> theory -> thm list * theory

  val instantiation_cmd: (xstring * sort * xstring) list
    -> theory -> local_theory
  val instance_cmd: (xstring * sort * xstring) list -> ((bstring * Attrib.src list) * xstring) list
    -> (thm list -> theory -> theory)
    -> theory -> Proof.state
end;

structure Instance : INSTANCE =
struct

fun instantiation_cmd raw_arities thy =
  TheoryTarget.instantiation (map (Sign.read_arity thy) raw_arities) thy;

fun instantiate arities f tac =
  TheoryTarget.instantiation arities
  #> f
  #> Class.prove_instantiation_instance tac
  #> LocalTheory.exit
  #> ProofContext.theory_of;

fun gen_instance prep_arity prep_attr parse_term do_proof raw_arities defs after_qed thy =
  let
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
    val arities = map (prep_arity thy) raw_arities;
  in
    thy
    |> TheoryTarget.instantiation arities
    |> `(fn ctxt => map (mk_def ctxt) defs)
    |-> (fn defs => fold_map Specification.definition defs)
    |-> (fn defs => `(fn ctxt => export_defs ctxt defs))
    ||> LocalTheory.exit
    ||> ProofContext.theory_of
    ||> TheoryTarget.instantiation arities
    |-> (fn defs => do_proof defs (LocalTheory.theory (after_qed defs)))
  end;

val instance = gen_instance Sign.cert_arity (K I) (K I)
  (fn _ => fn after_qed => Class.instantiation_instance (after_qed #> Class.conclude_instantiation));
val instance_cmd = gen_instance Sign.read_arity Attrib.intern_src Syntax.parse_prop
  (fn _ => fn after_qed => Class.instantiation_instance (after_qed #> Class.conclude_instantiation));
fun prove_instance tac arities defs = gen_instance Sign.cert_arity (K I) (K I)
  (fn defs => fn after_qed => Class.prove_instantiation_instance (K tac)
    #> after_qed #> Class.conclude_instantiation #> ProofContext.theory_of #> pair defs) arities defs (K I);

end;
