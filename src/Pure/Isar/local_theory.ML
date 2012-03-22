(*  Title:      Pure/Isar/local_theory.ML
    Author:     Makarius

Local theory operations, with abstract target context.
*)

type local_theory = Proof.context;
type generic_theory = Context.generic;

signature LOCAL_THEORY =
sig
  type operations
  val map_contexts: (Proof.context -> Proof.context) -> local_theory -> local_theory
  val assert: local_theory -> local_theory
  val level: Proof.context -> int
  val assert_bottom: bool -> local_theory -> local_theory
  val open_target: Name_Space.naming -> operations -> local_theory -> local_theory
  val close_target: local_theory -> local_theory
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
  val propagate_ml_env: generic_theory -> generic_theory
  val standard_morphism: local_theory -> Proof.context -> morphism
  val target_morphism: local_theory -> morphism
  val standard_form: local_theory -> Proof.context -> (morphism -> 'a) -> 'a
  val operations_of: local_theory -> operations
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
  val init: Name_Space.naming -> operations -> Proof.context -> local_theory
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

type lthy =
 {naming: Name_Space.naming,
  operations: operations,
  target: Proof.context};

fun make_lthy (naming, operations, target) : lthy =
  {naming = naming, operations = operations, target = target};


(* context data *)

structure Data = Proof_Data
(
  type T = lthy list;
  fun init _ = [];
);

fun map_contexts f =
  (Data.map o map) (fn {naming, operations, target} =>
    make_lthy (naming, operations,
      target
      |> Context_Position.set_visible false
      |> f
      |> Context_Position.restore_visible target))
  #> f;

fun assert lthy =
  if null (Data.get lthy) then error "Missing local theory context" else lthy;

val get_lthy = hd o Data.get o assert;

fun map_lthy f = assert #>
  Data.map (fn {naming, operations, target} :: parents =>
    make_lthy (f (naming, operations, target)) :: parents);


(* nested structure *)

val level = length o Data.get;

fun assert_bottom b lthy =
  let
    val _ = assert lthy;
    val b' = level lthy <= 1;
  in
    if b andalso not b' then error "Not at bottom of local theory nesting"
    else if not b andalso b' then error "Already at bottom of local theory nesting"
    else lthy
  end;

fun open_target naming operations target = assert target
  |> Data.map (cons (make_lthy (naming, operations, target)));

fun close_target lthy =
  assert_bottom false lthy |> Data.map tl;


(* naming *)

val naming_of = #naming o get_lthy;
val full_name = Name_Space.full_name o naming_of;

fun map_naming f = map_lthy (fn (naming, operations, target) => (f naming, operations, target));

val conceal = map_naming Name_Space.conceal;
val new_group = map_naming Name_Space.new_group;
val reset_group = map_naming Name_Space.reset_group;

val restore_naming = map_naming o K o naming_of;


(* target *)

val target_of = #target o get_lthy;

fun map_target f = map_lthy (fn (naming, operations, target) => (naming, operations, f target));


(* substructure mappings *)

fun raw_theory_result f lthy =
  let
    val (res, thy') = f (Proof_Context.theory_of lthy);
    val lthy' = map_contexts (Proof_Context.transfer thy') lthy;
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
    val target = target_of lthy;
    val (res, ctxt') = target
      |> Context_Position.set_visible false
      |> f
      ||> Context_Position.restore_visible target;
    val thy' = Proof_Context.theory_of ctxt';
    val lthy' = lthy
      |> map_target (K ctxt')
      |> map_contexts (Proof_Context.transfer thy');
  in (res, lthy') end;

fun target f = #2 o target_result (f #> pair ());

fun propagate_ml_env (context as Context.Proof lthy) =
      let val inherit = ML_Env.inherit context in
        lthy
        |> background_theory (Context.theory_map inherit)
        |> map_contexts (Context.proof_map inherit)
        |> Context.Proof
      end
  | propagate_ml_env context = context;


(* morphisms *)

fun standard_morphism lthy ctxt =
  Proof_Context.norm_export_morphism lthy ctxt $>
  Morphism.binding_morphism (Name_Space.transform_binding (naming_of lthy));

fun target_morphism lthy = standard_morphism lthy (target_of lthy);

fun standard_form lthy ctxt x =
  Morphism.form (Morphism.transform (standard_morphism lthy ctxt) x);



(** operations **)

val operations_of = #operations o get_lthy;


(* primitives *)

fun operation f lthy = f (operations_of lthy) lthy;
fun operation2 f x y = operation (fn ops => f ops x y);

val pretty = operation #pretty;
val abbrev = apsnd checkpoint ooo operation2 #abbrev;
val define = apsnd checkpoint oo operation2 #define false;
val define_internal = apsnd checkpoint oo operation2 #define true;
val notes_kind = apsnd checkpoint ooo operation2 #notes;
val declaration = checkpoint ooo operation2 #declaration;


(* basic derived operations *)

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

fun init naming operations target =
  target |> Data.map
    (fn [] => [make_lthy (naming, operations, target)]
      | _ => error "Local theory already initialized")
  |> checkpoint;

fun restore lthy =
  let val {naming, operations, target} = get_lthy lthy
  in init naming operations target end;


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
