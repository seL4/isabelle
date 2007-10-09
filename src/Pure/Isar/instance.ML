(*  Title:      Pure/Isar/instance.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

User-level instantiation interface for classes.
FIXME not operative for the moment
*)

signature INSTANCE =
sig
  val begin_instantiation: arity list -> theory -> local_theory
  val begin_instantiation_cmd: (xstring * string list * string) list
    -> theory -> local_theory
  val proof_instantiation: local_theory -> Proof.state
end;

structure Instance : INSTANCE =
struct

structure Instantiation = ProofDataFun
(
  type T = ((string * (string * sort) list) * sort) list * ((string * typ) * string) list;
  fun init _ = ([], []);
);

local

fun gen_begin_instantiation prep_arity raw_arities thy =
  let
    fun prep_arity' raw_arity names =
      let
        val arity as (tyco, sorts, sort) = prep_arity thy raw_arity;
        val vs = Name.invents names Name.aT (length sorts);
        val names' = fold Name.declare vs names;
      in (((tyco, vs ~~ sorts), sort), names') end;
    val (arities, _) = fold_map prep_arity' raw_arities Name.context;
    fun get_param tyco ty_subst (param, (c, ty)) =
      ((param ^ "_" ^ NameSpace.base tyco, map_atyps (K ty_subst) ty),
        Class.unoverload_const thy (c, ty));
    fun get_params ((tyco, vs), sort) =
      Class.params_of_sort thy sort
      |> map (get_param tyco (Type (tyco, map TFree vs)));
    val params = maps get_params arities;
    val ctxt =
      ProofContext.init thy
      |> Instantiation.put (arities, params);
    val thy_target = TheoryTarget.begin "" ctxt;
    val operations = {
        pretty = LocalTheory.pretty,
        consts = LocalTheory.consts,
        axioms = LocalTheory.axioms,
        abbrev = LocalTheory.abbrev,
        def = LocalTheory.def,
        notes = LocalTheory.notes,
        type_syntax = LocalTheory.type_syntax,
        term_syntax = LocalTheory.term_syntax,
        declaration = LocalTheory.pretty,
        target_naming = LocalTheory.target_naming,
        reinit = LocalTheory.reinit,
        exit = LocalTheory.exit
      };
  in TheoryTarget.begin "" ctxt end;

in

val begin_instantiation = gen_begin_instantiation Sign.cert_arity;
val begin_instantiation_cmd = gen_begin_instantiation Sign.read_arity;

end;

fun gen_proof_instantiation do_proof after_qed lthy =
  let
    val ctxt = LocalTheory.target_of lthy;
    val arities = case Instantiation.get ctxt
     of ([], _) => error "no instantiation target"
      | (arities, _) => map (fn ((tyco, vs), sort) => (tyco, map snd vs, sort)) arities;
    val thy = ProofContext.theory_of ctxt;
  in (do_proof after_qed arities) thy end;

val proof_instantiation = gen_proof_instantiation Class.instance_arity I;

end;
