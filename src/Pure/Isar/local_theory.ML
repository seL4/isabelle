(*  Title:      Pure/Isar/local_theory.ML
    ID:         $Id$
    Author:     Makarius

Local theory operations, with abstract target context.
*)

type local_theory = Proof.context;

signature LOCAL_THEORY =
sig
  type operations
  val target_of: local_theory -> Proof.context
  val raw_theory_result: (theory -> 'a * theory) -> local_theory -> 'a * local_theory
  val raw_theory: (theory -> theory) -> local_theory -> local_theory
  val full_naming: local_theory -> NameSpace.naming
  val full_name: local_theory -> bstring -> string
  val theory_result: (theory -> 'a * theory) -> local_theory -> 'a * local_theory
  val theory: (theory -> theory) -> local_theory -> local_theory
  val target_result: (Proof.context -> 'a * Proof.context) -> local_theory -> 'a * local_theory
  val target: (Proof.context -> Proof.context) -> local_theory -> local_theory
  val affirm: local_theory -> local_theory
  val pretty: local_theory -> Pretty.T list
  val axioms: string ->
    ((bstring * typ) * mixfix) list * ((bstring * Attrib.src list) * term list) list -> local_theory
    -> (term list * (bstring * thm list) list) * local_theory
  val abbrev: Syntax.mode -> (bstring * mixfix) * term -> local_theory ->
    (term * (bstring * thm)) * local_theory
  val define: string -> (bstring * mixfix) * ((bstring * Attrib.src list) * term) -> local_theory ->
    (term * (bstring * thm)) * local_theory
  val notes: string -> ((bstring * Attrib.src list) * (thm list * Attrib.src list) list) list ->
    local_theory -> (bstring * thm list) list * local_theory
  val type_syntax: declaration -> local_theory -> local_theory
  val term_syntax: declaration -> local_theory -> local_theory
  val declaration: declaration -> local_theory -> local_theory
  val note: string -> (bstring * Attrib.src list) * thm list ->
    local_theory -> (bstring * thm list) * local_theory
  val notation: bool -> Syntax.mode -> (term * mixfix) list -> local_theory -> local_theory
  val target_morphism: local_theory -> morphism
  val target_naming: local_theory -> NameSpace.naming
  val target_name: local_theory -> bstring -> string
  val init: string -> operations -> Proof.context -> local_theory
  val restore: local_theory -> local_theory
  val reinit: local_theory -> theory -> local_theory
  val exit: local_theory -> Proof.context
end;

structure LocalTheory: LOCAL_THEORY =
struct

(** local theory data **)

(* type lthy *)

type operations =
 {pretty: local_theory -> Pretty.T list,
  axioms: string ->
    ((bstring * typ) * mixfix) list * ((bstring * Attrib.src list) * term list) list -> local_theory
    -> (term list * (bstring * thm list) list) * local_theory,
  abbrev: Syntax.mode -> (bstring * mixfix) * term -> local_theory ->
    (term * (bstring * thm)) * local_theory,
  define: string -> (bstring * mixfix) * ((bstring * Attrib.src list) * term) -> local_theory ->
    (term * (bstring * thm)) * local_theory,
  notes: string ->
    ((bstring * Attrib.src list) * (thm list * Attrib.src list) list) list ->
    local_theory -> (bstring * thm list) list * local_theory,
  type_syntax: declaration -> local_theory -> local_theory,
  term_syntax: declaration -> local_theory -> local_theory,
  declaration: declaration -> local_theory -> local_theory,
  target_naming: local_theory -> NameSpace.naming,
  reinit: local_theory -> theory -> local_theory,
  exit: local_theory -> Proof.context};

datatype lthy = LThy of
 {theory_prefix: string,
  operations: operations,
  target: Proof.context};

fun make_lthy (theory_prefix, operations, target) =
  LThy {theory_prefix = theory_prefix, operations = operations, target = target};


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
  let val {theory_prefix, operations, target} = get_lthy lthy
  in Data.put (SOME (make_lthy (f (theory_prefix, operations, target)))) lthy end;

val target_of = #target o get_lthy;
val affirm = tap target_of;

fun map_target f = map_lthy (fn (theory_prefix, operations, target) =>
  (theory_prefix, operations, f target));


(* substructure mappings *)

fun raw_theory_result f lthy =
  let
    val (res, thy') = f (ProofContext.theory_of lthy);
    val lthy' = lthy
      |> map_target (ProofContext.transfer thy')
      |> ProofContext.transfer thy';
  in (res, lthy') end;

fun raw_theory f = #2 o raw_theory_result (f #> pair ());

fun full_naming lthy =
  Sign.naming_of (ProofContext.theory_of lthy)
  |> NameSpace.sticky_prefix (#theory_prefix (get_lthy lthy))
  |> NameSpace.qualified_names;

val full_name = NameSpace.full o full_naming;

fun theory_result f lthy = lthy |> raw_theory_result (fn thy => thy
  |> Sign.sticky_prefix (#theory_prefix (get_lthy lthy))
  |> Sign.qualified_names
  |> f
  ||> Sign.restore_naming thy);

fun theory f = #2 o theory_result (f #> pair ());

fun target_result f lthy =
  let
    val (res, ctxt') = f (#target (get_lthy lthy));
    val thy' = ProofContext.theory_of ctxt';
    val lthy' = lthy
      |> map_target (K ctxt')
      |> ProofContext.transfer thy';
  in (res, lthy') end;

fun target f = #2 o target_result (f #> pair ());


(* basic operations *)

fun operation f lthy = f (#operations (get_lthy lthy)) lthy;
fun operation1 f x = operation (fn ops => f ops x);
fun operation2 f x y = operation (fn ops => f ops x y);

val pretty = operation #pretty;
val axioms = operation2 #axioms;
val abbrev = operation2 #abbrev;
val define = operation2 #define;
val notes = operation2 #notes;
val type_syntax = operation1 #type_syntax;
val term_syntax = operation1 #term_syntax;
val declaration = operation1 #declaration;
val target_naming = operation #target_naming;

fun note kind (a, ths) lthy = lthy |> notes kind [(a, [(ths, [])])] |>> hd;

fun target_morphism lthy =
  ProofContext.export_morphism lthy (target_of lthy) $>
  Morphism.thm_morphism Goal.norm_result;

fun notation add mode raw_args lthy =
  let val args = map (apfst (Morphism.term (target_morphism lthy))) raw_args
  in term_syntax (ProofContext.target_notation add mode args) lthy end;

val target_name = NameSpace.full o target_naming;


(* init -- exit *)

fun init theory_prefix operations target = target |> Data.map
  (fn NONE => SOME (make_lthy (theory_prefix, operations, target))
    | SOME _ => error "Local theory already initialized");

fun restore lthy =
  let val {theory_prefix, operations, target} = get_lthy lthy
  in init theory_prefix operations target end;

val reinit = operation #reinit;
val exit = operation #exit;

end;
