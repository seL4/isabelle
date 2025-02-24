(*  Title:      Pure/Isar/local_theory.ML
    Author:     Makarius

Local theory operations, with abstract target context.
*)

type local_theory = Proof.context;
type generic_theory = Context.generic;

structure Attrib =
struct
  type binding = binding * Token.src list;
  type thms = (thm list * Token.src list) list;
  type fact = binding * thms;
end;

structure Locale =
struct
  type registration = {inst: string * morphism, mixin: (morphism * bool) option, export: morphism};
end;

signature LOCAL_THEORY =
sig
  type operations
  val assert: local_theory -> local_theory
  val level: Proof.context -> int
  val map_contexts: (int -> Proof.context -> Proof.context) -> local_theory -> local_theory
  val background_naming_of: local_theory -> Name_Space.naming
  val map_background_naming: (Name_Space.naming -> Name_Space.naming) ->
    local_theory -> local_theory
  val restore_background_naming: local_theory -> local_theory -> local_theory
  val full_name: local_theory -> binding -> string
  val full_name_pos: local_theory -> binding -> string * Position.T
  val new_group: local_theory -> local_theory
  val reset_group: local_theory -> local_theory
  val standard_morphism: local_theory -> Proof.context -> morphism
  val standard_morphism_theory: local_theory -> morphism
  val standard_form: local_theory -> Proof.context -> 'a Morphism.entity -> 'a
  val raw_theory_result: (theory -> 'a * theory) -> local_theory -> 'a * local_theory
  val raw_theory: (theory -> theory) -> local_theory -> local_theory
  val background_theory_result: (theory -> 'a * theory) -> local_theory -> 'a * local_theory
  val background_theory: (theory -> theory) -> local_theory -> local_theory
  val target_of: local_theory -> Proof.context
  val target: (Proof.context -> Proof.context) -> local_theory -> local_theory
  val target_morphism: local_theory -> morphism
  val propagate_ml_env: generic_theory -> generic_theory
  val touch_ml_env: generic_theory -> generic_theory
  val operations_of: local_theory -> operations
  val define: (binding * mixfix) * (Attrib.binding * term) -> local_theory ->
    (term * (string * thm)) * local_theory
  val define_internal: (binding * mixfix) * (Attrib.binding * term) -> local_theory ->
    (term * (string * thm)) * local_theory
  val note: Attrib.binding * thm list -> local_theory -> (string * thm list) * local_theory
  val notes: Attrib.fact list -> local_theory -> (string * thm list) list * local_theory
  val notes_kind: string -> Attrib.fact list -> local_theory ->
    (string * thm list) list * local_theory
  val abbrev: Syntax.mode -> (binding * mixfix) * term -> local_theory ->
    (term * term) * local_theory
  val declaration: {syntax: bool, pervasive: bool, pos: Position.T} -> Morphism.declaration ->
    local_theory -> local_theory
  val theory_registration: Locale.registration -> local_theory -> local_theory
  val locale_dependency: Locale.registration -> local_theory -> local_theory
  val pretty: local_theory -> Pretty.T list
  val add_thms_dynamic: binding * (Context.generic -> thm list) -> local_theory -> local_theory
  val set_defsort: sort -> local_theory -> local_theory
  val syntax: bool -> Syntax.mode -> (string * typ * mixfix) list ->
    local_theory -> local_theory
  val syntax_cmd: bool -> Syntax.mode -> (string * string * mixfix) list ->
    local_theory -> local_theory
  val syntax_deps: (string * string list) list -> Proof.context -> local_theory
  val translations: bool -> Ast.ast Syntax.trrule list -> local_theory -> local_theory
  val translations_cmd: bool -> (string * string) Syntax.trrule list -> local_theory -> local_theory
  val type_notation: bool -> Syntax.mode -> (typ * mixfix) list -> local_theory -> local_theory
  val type_notation_cmd: bool -> Syntax.mode -> (string * mixfix) list ->
    local_theory -> local_theory
  val notation: bool -> Syntax.mode -> (term * mixfix) list -> local_theory -> local_theory
  val notation_cmd: bool -> Syntax.mode -> (string * mixfix) list -> local_theory -> local_theory
  val type_alias: binding -> string -> local_theory -> local_theory
  val const_alias: binding -> string -> local_theory -> local_theory
  val init: {background_naming: Name_Space.naming, setup: theory -> Proof.context,
    conclude: local_theory -> Proof.context} -> operations -> theory -> local_theory
  val exit: local_theory -> Proof.context
  val exit_global: local_theory -> theory
  val exit_result: (morphism -> 'a -> 'b) -> 'a * local_theory -> 'b * Proof.context
  val exit_result_global: (morphism -> 'a -> 'b) -> 'a * local_theory -> 'b * theory
  val begin_nested: local_theory -> Binding.scope * local_theory
  val end_nested: local_theory -> local_theory
  val end_nested_result: (morphism -> 'a -> 'b) ->  'a * local_theory -> 'b * local_theory
end;

signature PRIVATE_LOCAL_THEORY =
sig
  include LOCAL_THEORY
  val reset: local_theory -> local_theory
end

structure Local_Theory: PRIVATE_LOCAL_THEORY =
struct

(** local theory data **)

(* type lthy *)

type operations =
 {define: bool -> (binding * mixfix) * (Attrib.binding * term) -> local_theory ->
    (term * (string * thm)) * local_theory,
  notes: string -> Attrib.fact list -> local_theory -> (string * thm list) list * local_theory,
  abbrev: Syntax.mode -> (binding * mixfix) * term -> local_theory ->
    (term * term) * local_theory,
  declaration: {syntax: bool, pervasive: bool, pos: Position.T} -> Morphism.declaration_entity ->
    local_theory -> local_theory,
  theory_registration: Locale.registration -> local_theory -> local_theory,
  locale_dependency: Locale.registration -> local_theory -> local_theory,
  pretty: local_theory -> Pretty.T list};

type lthy =
 {background_naming: Name_Space.naming,
  operations: operations,
  conclude: Proof.context -> Proof.context,
  target: Proof.context};

fun make_lthy (background_naming, operations, conclude, target) : lthy =
  {background_naming = background_naming, operations = operations,
    conclude = conclude, target = target};


(* context data *)

structure Data = Proof_Data
(
  type T = lthy list;
  fun init _ = [];
);


(* nested structure *)

val level = length o Data.get;  (*1: main target at bottom, >= 2: nested target context*)

fun assert lthy =
  if level lthy = 0 then error "Missing local theory context" else lthy;

fun assert_bottom lthy =
  let
    val _ = assert lthy;
  in
    if level lthy > 1 then error "Not at bottom of local theory nesting"
    else lthy
  end;

fun assert_not_bottom lthy =
  let
    val _ = assert lthy;
  in
    if level lthy = 1 then error "Already at bottom of local theory nesting"
    else lthy
  end;

val bottom_of = List.last o Data.get o assert;
val top_of = hd o Data.get o assert;

fun map_top f =
  assert #>
  Data.map (fn {background_naming, operations, conclude, target} :: parents =>
    make_lthy (f (background_naming, operations, conclude, target)) :: parents);

fun reset lthy = #target (top_of lthy) |> Data.put (Data.get lthy);

fun map_contexts f lthy =
  let val n = level lthy in
    lthy |> (Data.map o map_index)
      (fn (i, {background_naming, operations, conclude, target}) =>
        make_lthy (background_naming, operations, conclude,
          target
          |> Context_Position.set_visible false
          |> f (n - i - 1)
          |> Context_Position.restore_visible target))
      |> f n
  end;


(* naming for background theory *)

val background_naming_of = #background_naming o top_of;

fun map_background_naming f =
  map_top (fn (background_naming, operations, conclude, target) =>
    (f background_naming, operations, conclude, target));

val restore_background_naming = map_background_naming o K o background_naming_of;

val full_name = Name_Space.full_name o background_naming_of;
fun full_name_pos lthy b = (full_name lthy b, Binding.default_pos_of b);

val new_group = map_background_naming Name_Space.new_group;
val reset_group = map_background_naming Name_Space.reset_group;


(* standard morphisms *)

fun standard_morphism lthy ctxt =
  Morphism.set_context' lthy
   (Proof_Context.export_morphism lthy ctxt $>
    Morphism.thm_morphism' "Local_Theory.standard" (Goal.norm_result o Proof_Context.init_global) $>
    Morphism.binding_morphism "Local_Theory.standard_binding"
      (Name_Space.transform_binding (Proof_Context.naming_of lthy)));

fun standard_morphism_theory lthy =
  standard_morphism lthy (Proof_Context.init_global (Proof_Context.theory_of lthy));

fun standard_form lthy ctxt x =
  Morphism.form (Morphism.transform (standard_morphism lthy ctxt) x);


(* background theory *)

fun raw_theory_result f lthy =
  let
    val (res, thy') = f (Proof_Context.theory_of lthy);
    val lthy' = map_contexts (K (Proof_Context.transfer thy')) lthy;
  in (res, lthy') end;

fun raw_theory f = #2 o raw_theory_result (f #> pair ());

fun background_theory_result f lthy =
  let
    val naming =
      background_naming_of lthy
      |> Name_Space.transform_naming (Proof_Context.naming_of lthy);
  in
    lthy |> raw_theory_result (fn thy =>
      thy
      |> Sign.map_naming (K naming)
      |> f
      ||> Sign.restore_naming thy)
  end;

fun background_theory f = #2 o background_theory_result (f #> pair ());


(* target contexts *)

val target_of = #target o bottom_of;

fun target f lthy =
  let
    val ctxt = target_of lthy;
    val ctxt' = ctxt
      |> Context_Position.set_visible false
      |> f
      |> Context_Position.restore_visible ctxt;
    val thy' = Proof_Context.theory_of ctxt';
  in map_contexts (fn 0 => K ctxt' | _ => Proof_Context.transfer thy') lthy end;

fun target_morphism lthy = standard_morphism lthy (target_of lthy);

fun propagate_ml_env (context as Context.Proof lthy) =
      let val inherit = ML_Env.inherit [context] in
        lthy
        |> background_theory (Context.theory_map inherit)
        |> map_contexts (K (Context.proof_map inherit))
        |> Context.Proof
      end
  | propagate_ml_env context = context;

fun touch_ml_env context =
  if Context.enabled_tracing () then
    (case context of
      Context.Theory _ => ML_Env.touch context
    | Context.Proof _ => context)
  else context;



(** operations **)

val operations_of = #operations o top_of;

fun operation f lthy = f (operations_of lthy) lthy;
fun operation1 f x = operation (fn ops => f ops x);
fun operation2 f x y = operation (fn ops => f ops x y);


(* primitives *)

val pretty = operation #pretty;
val abbrev = operation2 #abbrev;
val define = operation2 #define false;
val define_internal = operation2 #define true;
val notes_kind = operation2 #notes;
fun declaration args = operation2 #declaration args o Morphism.entity;
val theory_registration = operation1 #theory_registration;
fun locale_dependency registration =
  assert_bottom #> operation1 #locale_dependency registration;


(* theorems *)

val notes = notes_kind "";
fun note (a, ths) = notes [(a, [(ths, [])])] #>> the_single;

fun add_thms_dynamic (binding, f) lthy =
  lthy
  |> background_theory_result (fn thy => thy
      |> Global_Theory.add_thms_dynamic' (Sign.inherit_naming thy lthy) (binding, f))
  |-> (fn name =>
    map_contexts (fn _ => fn ctxt =>
      Proof_Context.transfer_facts (Proof_Context.theory_of ctxt) ctxt) #>
    declaration {syntax = false, pervasive = false, pos = Binding.pos_of binding} (fn phi =>
      let val binding' = Morphism.binding phi binding in
        Context.mapping
          (Global_Theory.alias_fact binding' name)
          (Proof_Context.alias_fact binding' name)
      end));


(* default sort *)

fun set_defsort S =
  declaration {syntax = true, pervasive = false, pos = Position.thread_data ()}
    (K (Context.mapping (Sign.set_defsort S) (Proof_Context.set_defsort S)));


(* syntax *)

fun gen_syntax prep_type add mode raw_args lthy =
  let
    val args = map (fn (c, T, mx) => (c, prep_type lthy T, mx)) raw_args;
    val args' = map (fn (c, T, mx) => (c, T, Mixfix.reset_pos mx)) args;
    val _ = lthy |> Context_Position.is_visible lthy ? Proof_Context.syntax add mode args;
  in
    declaration {syntax = true, pervasive = false, pos = Position.thread_data ()}
      (fn _ => Proof_Context.generic_syntax add mode args') lthy
  end;

val syntax = gen_syntax (K I);
val syntax_cmd = gen_syntax Proof_Context.read_typ_syntax;

fun syntax_deps args =
  declaration {syntax = true, pervasive = false, pos = Position.thread_data ()}
    (fn _ => Proof_Context.generic_syntax_deps args);


(* translations *)

fun gen_translations prep_trrule add raw_args lthy =
  let
    val args = map (prep_trrule lthy) raw_args;
    val _ = Sign.check_translations lthy args;
  in
    declaration {syntax = true, pervasive = false, pos = Position.thread_data ()}
      (fn _ => Proof_Context.generic_translations add args) lthy
  end;

val translations = gen_translations (K I);
val translations_cmd = gen_translations Syntax.parse_trrule;


(* notation *)

local

fun gen_type_notation prep_type add mode raw_args lthy =
  let
    val prepare = prep_type lthy #> Logic.type_map (Assumption.export_term lthy (target_of lthy));
    val args = map (apfst prepare) raw_args;
    val args' = map (apsnd Mixfix.reset_pos) args;
    val _ = lthy |> Context_Position.is_visible lthy ? Proof_Context.type_notation add mode args;
  in
    declaration {syntax = true, pervasive = false, pos = Position.thread_data ()}
      (Proof_Context.generic_type_notation add mode args') lthy
  end;

fun gen_notation prep_const add mode raw_args lthy =
  let
    val prepare = prep_const lthy #> Assumption.export_term lthy (target_of lthy);
    val args = map (apfst prepare) raw_args;
    val args' = map (apsnd Mixfix.reset_pos) args;
    val _ = lthy |> Context_Position.is_visible lthy ? Proof_Context.notation add mode args;
  in
    declaration {syntax = true, pervasive = false, pos = Position.thread_data ()}
      (Proof_Context.generic_notation add mode args') lthy
  end;

in

val type_notation = gen_type_notation (K I);
val type_notation_cmd =
  gen_type_notation (Proof_Context.read_type_name {proper = true, strict = false});

val notation = gen_notation (K I);
val notation_cmd = gen_notation (Proof_Context.read_const {proper = false, strict = false});

end;


(* name space aliases *)

fun syntax_alias global_alias local_alias b name =
  declaration {syntax = true, pervasive = false, pos = Position.thread_data ()} (fn phi =>
    let val b' = Morphism.binding phi b
    in Context.mapping (global_alias b' name) (local_alias b' name) end);

val type_alias = syntax_alias Sign.type_alias Proof_Context.type_alias;
val const_alias = syntax_alias Sign.const_alias Proof_Context.const_alias;



(** manage targets **)

(* main target *)

fun init_target background_naming conclude operations target =
  Data.map (K [make_lthy (background_naming, operations, conclude, target)]) target

fun init {background_naming, setup, conclude} operations thy =
  thy
  |> Sign.change_begin
  |> setup
  |> init_target background_naming (conclude #> target_of #> Sign.change_end_local) operations;

val exit_of = #conclude o bottom_of;

fun exit lthy = exit_of lthy (assert_bottom lthy);
val exit_global = Proof_Context.theory_of o exit;

fun exit_result decl (x, lthy) =
  let
    val ctxt = exit lthy;
    val phi = standard_morphism lthy ctxt;
  in (decl phi x, ctxt) end;

fun exit_result_global decl (x, lthy) =
  let
    val thy = exit_global lthy;
    val thy_ctxt = Proof_Context.init_global thy;
    val phi = standard_morphism lthy thy_ctxt;
  in (decl phi x, thy) end;


(* nested targets *)

fun begin_nested lthy =
  let
    val _ = assert lthy;
    val (scope, target) = Proof_Context.new_scope lthy;
    val entry = make_lthy (background_naming_of lthy, operations_of lthy,
      Proof_Context.restore_naming lthy, target);
    val lthy' = Data.map (cons entry) target;
  in (scope, lthy') end;

fun end_nested lthy =
  let
    val _ = assert_not_bottom lthy;
    val ({conclude, ...} :: rest) = Data.get lthy;
  in lthy |> Data.put rest |> reset |> conclude end;

fun end_nested_result decl (x, lthy) =
   let
    val outer_lthy = end_nested lthy;
    val phi = Proof_Context.export_morphism lthy outer_lthy;
  in (decl phi x, outer_lthy) end;

end;
