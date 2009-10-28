(*  Title:      Pure/Isar/local_theory.ML
    Author:     Makarius

Local theory operations, with abstract target context.
*)

type local_theory = Proof.context;

signature LOCAL_THEORY =
sig
  type operations
  val affirm: local_theory -> local_theory
  val naming_of: local_theory -> Name_Space.naming
  val full_name: local_theory -> binding -> string
  val map_naming: (Name_Space.naming -> Name_Space.naming) -> local_theory -> local_theory
  val conceal: local_theory -> local_theory
  val set_group: serial -> local_theory -> local_theory
  val restore_naming: local_theory -> local_theory -> local_theory
  val target_of: local_theory -> Proof.context
  val raw_theory_result: (theory -> 'a * theory) -> local_theory -> 'a * local_theory
  val raw_theory: (theory -> theory) -> local_theory -> local_theory
  val checkpoint: local_theory -> local_theory
  val theory_result: (theory -> 'a * theory) -> local_theory -> 'a * local_theory
  val theory: (theory -> theory) -> local_theory -> local_theory
  val target_result: (Proof.context -> 'a * Proof.context) -> local_theory -> 'a * local_theory
  val target: (Proof.context -> Proof.context) -> local_theory -> local_theory
  val map_contexts: (Context.generic -> Context.generic) -> local_theory -> local_theory
  val pretty: local_theory -> Pretty.T list
  val abbrev: Syntax.mode -> (binding * mixfix) * term -> local_theory ->
    (term * term) * local_theory
  val define: string -> (binding * mixfix) * (Attrib.binding * term) -> local_theory ->
    (term * (string * thm)) * local_theory
  val note: string -> Attrib.binding * thm list -> local_theory -> (string * thm list) * local_theory
  val notes: string -> (Attrib.binding * (thm list * Attrib.src list) list) list ->
    local_theory -> (string * thm list) list * local_theory
  val type_syntax: declaration -> local_theory -> local_theory
  val term_syntax: declaration -> local_theory -> local_theory
  val declaration: declaration -> local_theory -> local_theory
  val notation: bool -> Syntax.mode -> (term * mixfix) list -> local_theory -> local_theory
  val target_morphism: local_theory -> morphism
  val init: string -> operations -> Proof.context -> local_theory
  val restore: local_theory -> local_theory
  val reinit: local_theory -> local_theory
  val exit: local_theory -> Proof.context
  val exit_global: local_theory -> theory
  val exit_result: (morphism -> 'a -> 'b) -> 'a * local_theory -> 'b * Proof.context
  val exit_result_global: (morphism -> 'a -> 'b) -> 'a * local_theory -> 'b * theory
end;

structure LocalTheory: LOCAL_THEORY =
struct

(** local theory data **)

(* type lthy *)

type operations =
 {pretty: local_theory -> Pretty.T list,
  abbrev: Syntax.mode -> (binding * mixfix) * term -> local_theory ->
    (term * term) * local_theory,
  define: string ->
    (binding * mixfix) * (Attrib.binding * term) -> local_theory ->
    (term * (string * thm)) * local_theory,
  notes: string ->
    (Attrib.binding * (thm list * Attrib.src list) list) list ->
    local_theory -> (string * thm list) list * local_theory,
  type_syntax: declaration -> local_theory -> local_theory,
  term_syntax: declaration -> local_theory -> local_theory,
  declaration: declaration -> local_theory -> local_theory,
  reinit: local_theory -> local_theory,
  exit: local_theory -> Proof.context};

datatype lthy = LThy of
 {naming: Name_Space.naming,
  theory_prefix: string,
  operations: operations,
  target: Proof.context};

fun make_lthy (naming, theory_prefix, operations, target) =
  LThy {naming = naming, theory_prefix = theory_prefix,
    operations = operations, target = target};


(* context data *)

structure Data = ProofDataFun
(
  type T = lthy option;
  fun init _ = NONE;
);

fun get_lthy lthy =
  (case Data.get lthy of
    NONE => error "No local theory context"
  | SOME (LThy data) => data);

fun map_lthy f lthy =
  let val {naming, theory_prefix, operations, target} = get_lthy lthy
  in Data.put (SOME (make_lthy (f (naming, theory_prefix, operations, target)))) lthy end;

val affirm = tap get_lthy;


(* naming *)

val naming_of = #naming o get_lthy;
val full_name = Name_Space.full_name o naming_of;

fun map_naming f = map_lthy (fn (naming, theory_prefix, operations, target) =>
  (f naming, theory_prefix, operations, target));

val conceal = map_naming Name_Space.conceal;
val set_group = map_naming o Name_Space.set_group;

val restore_naming = map_naming o K o naming_of;


(* target *)

val target_of = #target o get_lthy;

fun map_target f = map_lthy (fn (naming, theory_prefix, operations, target) =>
  (naming, theory_prefix, operations, f target));


(* substructure mappings *)

fun raw_theory_result f lthy =
  let
    val (res, thy') = f (ProofContext.theory_of lthy);
    val lthy' = lthy
      |> map_target (ProofContext.transfer thy')
      |> ProofContext.transfer thy';
  in (res, lthy') end;

fun raw_theory f = #2 o raw_theory_result (f #> pair ());

val checkpoint = raw_theory Theory.checkpoint;

fun theory_result f lthy =
  lthy |> raw_theory_result (fn thy =>
    thy
    |> Sign.map_naming (K (naming_of lthy))
    |> f
    ||> Sign.restore_naming thy);

fun theory f = #2 o theory_result (f #> pair ());

fun target_result f lthy =
  let
    val (res, ctxt') = target_of lthy
      |> ContextPosition.set_visible false
      |> f
      ||> ContextPosition.restore_visible lthy;
    val thy' = ProofContext.theory_of ctxt';
    val lthy' = lthy
      |> map_target (K ctxt')
      |> ProofContext.transfer thy';
  in (res, lthy') end;

fun target f = #2 o target_result (f #> pair ());

fun map_contexts f =
  theory (Context.theory_map f) #>
  target (Context.proof_map f) #>
  Context.proof_map f;


(* basic operations *)

fun operation f lthy = f (#operations (get_lthy lthy)) lthy;
fun operation1 f x = operation (fn ops => f ops x);
fun operation2 f x y lthy = operation (fn ops => f ops x y) lthy;

val pretty = operation #pretty;
val abbrev = apsnd checkpoint ooo operation2 #abbrev;
val define = apsnd checkpoint ooo operation2 #define;
val notes = apsnd checkpoint ooo operation2 #notes;
val type_syntax = checkpoint oo operation1 #type_syntax;
val term_syntax = checkpoint oo operation1 #term_syntax;
val declaration = checkpoint oo operation1 #declaration;

fun note kind (a, ths) = notes kind [(a, [(ths, [])])] #>> the_single;

fun target_morphism lthy =
  ProofContext.norm_export_morphism lthy (target_of lthy);

fun notation add mode raw_args lthy =
  let val args = map (apfst (Morphism.term (target_morphism lthy))) raw_args
  in term_syntax (ProofContext.target_notation add mode args) lthy end;


(* init *)

fun init theory_prefix operations target =
  let val naming =
    Sign.naming_of (ProofContext.theory_of target)
    |> Name_Space.mandatory_path theory_prefix;
  in
    target |> Data.map
      (fn NONE => SOME (make_lthy (naming, theory_prefix, operations, target))
        | SOME _ => error "Local theory already initialized")
    |> checkpoint
  end;

fun restore lthy =
  let val {theory_prefix, operations, target, ...} = get_lthy lthy
  in init theory_prefix operations target end;

val reinit = checkpoint o operation #reinit;


(* exit *)

val exit = ProofContext.theory Theory.checkpoint o operation #exit;
val exit_global = ProofContext.theory_of o exit;

fun exit_result f (x, lthy) =
  let
    val ctxt = exit lthy;
    val phi = ProofContext.norm_export_morphism lthy ctxt;
  in (f phi x, ctxt) end;

fun exit_result_global f (x, lthy) =
  let
    val thy = exit_global lthy;
    val thy_ctxt = ProofContext.init thy;
    val phi = ProofContext.norm_export_morphism lthy thy_ctxt;
  in (f phi x, thy) end;

end;
