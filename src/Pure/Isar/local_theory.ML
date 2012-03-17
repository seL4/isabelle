(*  Title:      Pure/Isar/local_theory.ML
    Author:     Makarius

Local theory operations, with abstract target context.
*)

type local_theory = Proof.context;
type generic_theory = Context.generic;

signature LOCAL_THEORY =
sig
  type operations
  val affirm: local_theory -> local_theory
  val naming_of: local_theory -> Name_Space.naming
  val full_name: local_theory -> binding -> string
  val map_naming: (Name_Space.naming -> Name_Space.naming) -> local_theory -> local_theory
  val conceal: local_theory -> local_theory
  val new_group: local_theory -> local_theory
  val reset_group: local_theory -> local_theory
  val restore_naming: local_theory -> local_theory -> local_theory
  val target_of: local_theory -> Proof.context
  val raw_theory_result: (theory -> 'a * theory) -> local_theory -> 'a * local_theory
  val raw_theory: (theory -> theory) -> local_theory -> local_theory
  val background_theory_result: (theory -> 'a * theory) -> local_theory -> 'a * local_theory
  val background_theory: (theory -> theory) -> local_theory -> local_theory
  val target_result: (Proof.context -> 'a * Proof.context) -> local_theory -> 'a * local_theory
  val target: (Proof.context -> Proof.context) -> local_theory -> local_theory
  val map_contexts: (Context.generic -> Context.generic) -> local_theory -> local_theory
  val propagate_ml_env: generic_theory -> generic_theory
  val standard_morphism: local_theory -> Proof.context -> morphism
  val target_morphism: local_theory -> morphism
  val global_morphism: local_theory -> morphism
  val define: (binding * mixfix) * (Attrib.binding * term) -> local_theory ->
    (term * (string * thm)) * local_theory
  val define_internal: (binding * mixfix) * (Attrib.binding * term) -> local_theory ->
    (term * (string * thm)) * local_theory
  val note: Attrib.binding * thm list -> local_theory -> (string * thm list) * local_theory
  val notes: (Attrib.binding * (thm list * Attrib.src list) list) list ->
    local_theory -> (string * thm list) list * local_theory
  val notes_kind: string -> (Attrib.binding * (thm list * Attrib.src list) list) list ->
    local_theory -> (string * thm list) list * local_theory
  val abbrev: Syntax.mode -> (binding * mixfix) * term -> local_theory ->
    (term * term) * local_theory
  val declaration: {syntax: bool, pervasive: bool} -> declaration -> local_theory -> local_theory
  val pretty: local_theory -> Pretty.T list
  val set_defsort: sort -> local_theory -> local_theory
  val type_notation: bool -> Syntax.mode -> (typ * mixfix) list -> local_theory -> local_theory
  val notation: bool -> Syntax.mode -> (term * mixfix) list -> local_theory -> local_theory
  val class_alias: binding -> class -> local_theory -> local_theory
  val type_alias: binding -> string -> local_theory -> local_theory
  val const_alias: binding -> string -> local_theory -> local_theory
  val init: serial option -> string -> operations -> Proof.context -> local_theory
  val restore: local_theory -> local_theory
  val exit: local_theory -> Proof.context
  val exit_global: local_theory -> theory
  val exit_result: (morphism -> 'a -> 'b) -> 'a * local_theory -> 'b * Proof.context
  val exit_result_global: (morphism -> 'a -> 'b) -> 'a * local_theory -> 'b * theory
end;

structure Local_Theory: LOCAL_THEORY =
struct

(** local theory data **)

(* type lthy *)

type operations =
 {define: bool -> (binding * mixfix) * (Attrib.binding * term) -> local_theory ->
    (term * (string * thm)) * local_theory,
  notes: string ->
    (Attrib.binding * (thm list * Attrib.src list) list) list ->
    local_theory -> (string * thm list) list * local_theory,
  abbrev: Syntax.mode -> (binding * mixfix) * term -> local_theory ->
    (term * term) * local_theory,
  declaration: {syntax: bool, pervasive: bool} -> declaration -> local_theory -> local_theory,
  pretty: local_theory -> Pretty.T list,
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

structure Data = Proof_Data
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
val new_group = map_naming Name_Space.new_group;
val reset_group = map_naming Name_Space.reset_group;

val restore_naming = map_naming o K o naming_of;


(* target *)

val target_of = #target o get_lthy;

fun map_target f = map_lthy (fn (naming, theory_prefix, operations, target) =>
  (naming, theory_prefix, operations, f target));


(* substructure mappings *)

fun raw_theory_result f lthy =
  let
    val (res, thy') = f (Proof_Context.theory_of lthy);
    val lthy' = lthy
      |> map_target (Proof_Context.transfer thy')
      |> Proof_Context.transfer thy';
  in (res, lthy') end;

fun raw_theory f = #2 o raw_theory_result (f #> pair ());

val checkpoint = raw_theory Theory.checkpoint;

fun background_theory_result f lthy =
  lthy |> raw_theory_result (fn thy =>
    thy
    |> Sign.map_naming (K (naming_of lthy))
    |> f
    ||> Sign.restore_naming thy
    ||> Theory.checkpoint);

fun background_theory f = #2 o background_theory_result (f #> pair ());

fun target_result f lthy =
  let
    val (res, ctxt') = target_of lthy
      |> Context_Position.set_visible false
      |> f
      ||> Context_Position.restore_visible lthy;
    val thy' = Proof_Context.theory_of ctxt';
    val lthy' = lthy
      |> map_target (K ctxt')
      |> Proof_Context.transfer thy';
  in (res, lthy') end;

fun target f = #2 o target_result (f #> pair ());

fun map_contexts f =
  background_theory (Context.theory_map f) #>
  target (Context.proof_map f) #>
  Context.proof_map f;

fun propagate_ml_env (context as Context.Proof lthy) =
      Context.Proof (map_contexts (ML_Env.inherit context) lthy)
  | propagate_ml_env context = context;


(* morphisms *)

fun standard_morphism lthy ctxt =
  Proof_Context.norm_export_morphism lthy ctxt $>
  Morphism.binding_morphism (Name_Space.transform_binding (naming_of lthy));

fun target_morphism lthy = standard_morphism lthy (target_of lthy);
fun global_morphism lthy =
  standard_morphism lthy (Proof_Context.init_global (Proof_Context.theory_of lthy));


(* primitive operations *)

fun operation f lthy = f (#operations (get_lthy lthy)) lthy;
fun operation1 f x = operation (fn ops => f ops x);
fun operation2 f x y lthy = operation (fn ops => f ops x y) lthy;

val pretty = operation #pretty;
val abbrev = apsnd checkpoint ooo operation2 #abbrev;
val define = apsnd checkpoint oo operation2 #define false;
val define_internal = apsnd checkpoint oo operation2 #define true;
val notes_kind = apsnd checkpoint ooo operation2 #notes;
val declaration = checkpoint ooo operation2 #declaration;



(** basic derived operations **)

val notes = notes_kind "";
fun note (a, ths) = notes [(a, [(ths, [])])] #>> the_single;

fun set_defsort S =
  declaration {syntax = true, pervasive = false}
    (K (Context.mapping (Sign.set_defsort S) (Proof_Context.set_defsort S)));


(* notation *)

fun type_notation add mode raw_args lthy =
  let val args = map (apfst (Morphism.typ (target_morphism lthy))) raw_args in
    declaration {syntax = true, pervasive = false}
      (Proof_Context.target_type_notation add mode args) lthy
  end;

fun notation add mode raw_args lthy =
  let val args = map (apfst (Morphism.term (target_morphism lthy))) raw_args in
    declaration {syntax = true, pervasive = false}
      (Proof_Context.target_notation add mode args) lthy
  end;


(* name space aliases *)

fun alias global_alias local_alias b name =
  declaration {syntax = true, pervasive = false} (fn phi =>
    let val b' = Morphism.binding phi b
    in Context.mapping (global_alias b' name) (local_alias b' name) end);

val class_alias = alias Sign.class_alias Proof_Context.class_alias;
val type_alias = alias Sign.type_alias Proof_Context.type_alias;
val const_alias = alias Sign.const_alias Proof_Context.const_alias;



(** init and exit **)

(* init *)

fun init group theory_prefix operations target =
  let val naming =
    Sign.naming_of (Proof_Context.theory_of target)
    |> Name_Space.set_group group
    |> Name_Space.mandatory_path theory_prefix;
  in
    target |> Data.map
      (fn NONE => SOME (make_lthy (naming, theory_prefix, operations, target))
        | SOME _ => error "Local theory already initialized")
    |> checkpoint
  end;

fun restore lthy =
  let val {naming, theory_prefix, operations, target} = get_lthy lthy
  in init (Name_Space.get_group naming) theory_prefix operations target end;


(* exit *)

val exit = Proof_Context.background_theory Theory.checkpoint o operation #exit;
val exit_global = Proof_Context.theory_of o exit;

fun exit_result f (x, lthy) =
  let
    val ctxt = exit lthy;
    val phi = standard_morphism lthy ctxt;
  in (f phi x, ctxt) end;

fun exit_result_global f (x, lthy) =
  let
    val thy = exit_global lthy;
    val thy_ctxt = Proof_Context.init_global thy;
    val phi = standard_morphism lthy thy_ctxt;
  in (f phi x, thy) end;

end;
