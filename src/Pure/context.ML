(*  Title:      Pure/context.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Generic theory contexts with unique identity, arbitrarily typed data,
linear and graph development.  Implicit ML theory context.
*)

signature BASIC_CONTEXT =
sig
  type theory
  type theory_ref
  exception THEORY of string * theory list
  val context: theory -> unit
  val the_context: unit -> theory
end;

signature CONTEXT =
sig
  include BASIC_CONTEXT
  (*theory context*)
  val parents_of: theory -> theory list
  val ancestors_of: theory -> theory list
  val is_stale: theory -> bool
  val ProtoPureN: string
  val PureN: string
  val CPureN: string
  val draftN: string
  val is_draft: theory -> bool
  val exists_name: string -> theory -> bool
  val names_of: theory -> string list
  val pretty_thy: theory -> Pretty.T
  val string_of_thy: theory -> string
  val pprint_thy: theory -> pprint_args -> unit
  val pretty_abbrev_thy: theory -> Pretty.T
  val str_of_thy: theory -> string
  val check_thy: string -> theory -> theory
  val eq_thy: theory * theory -> bool
  val subthy: theory * theory -> bool
  val self_ref: theory -> theory_ref
  val deref: theory_ref -> theory
  exception DATA_FAIL of exn * string
  val theory_data: theory -> string list
  val print_all_data: theory -> unit
  val copy_thy: theory -> theory
  val checkpoint_thy: theory -> theory
  val pre_pure: theory
  val merge: theory * theory -> theory                     (*exception TERM*)
  val merge_refs: theory_ref * theory_ref -> theory_ref    (*exception TERM*)
  val theory_name: theory -> string
  val begin_theory: (theory -> Pretty.pp) -> string -> theory list -> theory
  val end_theory: theory -> theory

  (*ML context*)
  val get_context: unit -> theory option
  val set_context: theory option -> unit
  val reset_context: unit -> unit
  val setmp: theory option -> ('a -> 'b) -> 'a -> 'b
  val pass: theory option -> ('a -> 'b) -> 'a -> 'b * theory option
  val pass_theory: theory -> ('a -> 'b) -> 'a -> 'b * theory
  val save: ('a -> 'b) -> 'a -> 'b
  val >> : (theory -> theory) -> unit
  val ml_output: (string -> unit) * (string -> unit)
  val use_mltext: string -> bool -> theory option -> unit
  val use_mltext_theory: string -> bool -> theory -> theory
  val use_let: string -> string -> string -> theory -> theory
  val add_setup: (theory -> theory) list -> unit
  val setup: unit -> (theory -> theory) list
end;

signature PRIVATE_CONTEXT =
sig
  include CONTEXT
  structure TheoryData:
  sig
    val declare: string -> Object.T -> (Object.T -> Object.T) ->
      (Object.T -> Object.T) -> (Pretty.pp -> Object.T * Object.T -> Object.T) ->
      (theory -> Object.T -> unit) -> serial
    val init: serial -> theory -> theory
    val print: serial -> theory -> unit
    val get: serial -> (Object.T -> 'a) -> theory -> 'a
    val put: serial -> ('a -> Object.T) -> 'a -> theory -> theory
  end;
end;

structure Context: PRIVATE_CONTEXT =
struct

(*** theory context ***)

datatype theory =
  Theory of
  (*identity*)
   {self: theory ref option,
    id: serial * string,
    ids: string Inttab.table} *
  (*data*)
  Object.T Inttab.table *
  (*history of linear development*)
   {name: string,
    version: int,
    intermediates: theory list} *
  (*ancestry of graph development*)
   {parents: theory list,
    ancestors: theory list};

exception THEORY of string * theory list;

fun rep_theory (Theory args) = args;

val identity_of = #1 o rep_theory;
val data_of     = #2 o rep_theory;
val history_of  = #3 o rep_theory;
val ancestry_of = #4 o rep_theory;

fun make_identity self id ids = {self = self, id = id, ids = ids};
fun make_history name vers ints = {name = name, version = vers, intermediates = ints};
fun make_ancestry parents ancestors = {parents = parents, ancestors = ancestors};

val parents_of = #parents o ancestry_of;
val ancestors_of = #ancestors o ancestry_of;



(** theory identity **)

(* staleness *)

fun eq_id ((i: int, _), (j, _)) = i = j;

fun is_stale
    (Theory ({self = SOME (ref (Theory ({id = id', ...}, _, _, _))), id, ...}, _, _, _)) =
      not (eq_id (id, id'))
  | is_stale (Theory ({self = NONE, ...}, _, _, _)) = true;

fun vitalize (thy as Theory ({self = SOME r, ...}, _, _, _)) = (r := thy; thy)
  | vitalize (thy as Theory ({self = NONE, id, ids}, data, history, ancestry)) =
      let
        val r = ref thy;
        val thy' = Theory (make_identity (SOME r) id ids, data, history, ancestry);
      in r := thy'; thy' end;


(* names *)

val ProtoPureN = "ProtoPure";
val PureN = "Pure";
val CPureN = "CPure";

val draftN = "#";
fun draft_id (_, name) = (name = draftN);
val is_draft = draft_id o #id o identity_of;

fun exists_name name (Theory ({id, ids, ...}, _, _, _)) =
  name = #2 id orelse Inttab.exists (equal name o #2) ids;

fun names_of (Theory ({id, ids, ...}, _, _, _)) =
  map #2 (Inttab.dest ids @ [id]);

fun pretty_thy thy =
  Pretty.str_list "{" "}" (names_of thy @ (if is_stale thy then ["!"] else []));

val string_of_thy = Pretty.string_of o pretty_thy;
val pprint_thy = Pretty.pprint o pretty_thy;

fun pretty_abbrev_thy thy =
  let
    val names = names_of thy;
    val n = length names;
    val abbrev = if n > 5 then "..." :: List.drop (names, n - 5) else names;
  in Pretty.str_list "{" "}" abbrev end;

val str_of_thy = Pretty.str_of o pretty_abbrev_thy;


(* consistency *)

fun check_thy pos thy =
  if is_stale thy then
    raise TERM ("Stale theory encountered (see " ^ pos ^ "):\n" ^ string_of_thy thy, [])
  else thy;

fun check_insert id ids =
  if draft_id id orelse is_some (Inttab.lookup (ids, #1 id)) then ids
  else if Inttab.exists (equal (#2 id) o #2) ids then
    raise TERM ("Different versions of theory component " ^ quote (#2 id), [])
  else Inttab.update (id, ids);

fun check_merge thy1 thy2 =
  let
    val {id = id1, ids = ids1, ...} = identity_of thy1;
    val {id = id2, ids = ids2, ...} = identity_of thy2;
  in check_insert id2 (Inttab.fold check_insert ids2 (check_insert id1 ids1)) end;


(* equality and inclusion *)

local

fun exists_ids (Theory ({id, ids, ...}, _, _, _)) (i, _) =
  i = #1 id orelse is_some (Inttab.lookup (ids, i));

fun member_ids (Theory ({id, ...}, _, _, _), thy) = exists_ids thy id;

fun subset_ids (Theory ({id, ids, ...}, _, _, _), thy) =
  exists_ids thy id andalso Inttab.forall (exists_ids thy) ids;

in

val eq_thy = eq_id o pairself (#id o identity_of o check_thy "Context.eq_thy");
fun subthy thys = eq_thy thys orelse member_ids thys;
fun subthy_internal thys = eq_thy thys orelse subset_ids thys;

end;


(* external references *)

datatype theory_ref = TheoryRef of theory ref;

val self_ref = TheoryRef o the o #self o identity_of o check_thy "Context.self_ref";
fun deref (TheoryRef (ref thy)) = thy;



(** theory data **)

(* data kinds and access methods *)

exception DATA_FAIL of exn * string;

local

type kind =
 {name: string,
  empty: Object.T,
  copy: Object.T -> Object.T,
  extend: Object.T -> Object.T,
  merge: Pretty.pp -> Object.T * Object.T -> Object.T,
  print: theory -> Object.T -> unit};

val kinds = ref (Inttab.empty: kind Inttab.table);

fun invoke meth_name meth_fn k =
  (case Inttab.lookup (! kinds, k) of
    SOME kind => meth_fn kind |> transform_failure (fn exn =>
      DATA_FAIL (exn, "Theory data method " ^ #name kind ^ "." ^ meth_name ^ " failed"))
  | NONE => sys_error ("Invalid theory data identifier " ^ string_of_int k));

in

fun invoke_name k    = invoke "name" (K o #name) k ();
fun invoke_empty k   = invoke "empty" (K o #empty) k ();
val invoke_copy      = invoke "copy" #copy;
val invoke_extend    = invoke "extend" #extend;
fun invoke_merge pp  = invoke "merge" (fn kind => #merge kind pp);
fun invoke_print thy = invoke "print" (fn kind => #print kind thy);

fun declare name e cp ext mrg prt =
  let
    val k = serial ();
    val kind = {name = name, empty = e, copy = cp, extend = ext, merge = mrg, print = prt};
    val _ = conditional (Inttab.exists (equal name o #name o #2) (! kinds)) (fn () =>
      warning ("Duplicate declaration of theory data " ^ quote name));
    val _ = kinds := Inttab.update ((k, kind), ! kinds);
  in k end;

val copy_data = Inttab.map' invoke_copy;
val extend_data = Inttab.map' invoke_extend;
fun merge_data pp = Inttab.join (SOME oo invoke_merge pp) o pairself extend_data;

fun theory_data thy =
  map invoke_name (Inttab.keys (data_of thy))
  |> map (rpair ()) |> Symtab.make_multi |> Symtab.dest
  |> map (apsnd length)
  |> map (fn (name, 1) => name | (name, n) => name ^ enclose "[" "]" (string_of_int n));

fun print_all_data thy =
  List.app (uncurry (invoke_print thy)) (Inttab.dest (data_of thy));

end;



(** build theories **)

(* primitives *)

fun create_thy name self id ids data history ancestry =
  let
    val ids' = check_insert id ids;
    val id' = (serial (), name);
    val _ = check_insert id' ids';
    val identity' = make_identity self id' ids';
  in vitalize (Theory (identity', data, history, ancestry)) end;

fun copy_thy (thy as Theory ({id, ids, ...}, data, history, ancestry)) =
  let val _ = check_thy "Context.copy_thy" thy;
  in create_thy draftN NONE id ids (copy_data data) history ancestry end;

fun change_thy name f (thy as Theory ({self, id, ids}, data, history, ancestry)) =
  let
    val _ = check_thy "Context.change_thy" thy;
    val (self', data', ancestry') =
      if is_draft thy then (self, data, ancestry)
      else (NONE, extend_data data, make_ancestry [thy] (thy :: #ancestors ancestry));
  in create_thy name self' id ids (f data') history ancestry' end;

fun name_thy name = change_thy name I;
val map_thy = change_thy draftN;
val extend_thy = map_thy I;

fun checkpoint_thy thy =
  if not (is_draft thy) then thy
  else
    let
      val {name, version, intermediates} = history_of thy;
      val thy' as Theory (identity', data', _, ancestry') =
        name_thy (name ^ ":" ^ string_of_int version) thy;
      val history' = make_history name (version + 1) (thy' :: intermediates);
    in vitalize (Theory (identity', data', history', ancestry')) end;


(* theory data *)

structure TheoryData =
struct

val declare = declare;

fun get k dest thy =
  (case Inttab.lookup (data_of thy, k) of
    SOME x => (dest x handle Match =>
      error ("Failed to access theory data " ^ quote (invoke_name k)))
  | NONE => error ("Uninitialized theory data " ^ quote (invoke_name k)));

fun print k thy = invoke_print thy k (get k I thy);
fun put k mk x = map_thy (curry Inttab.update (k, mk x));
fun init k = put k I (invoke_empty k);

end;


(* pre_pure *)

val pre_pure = create_thy draftN NONE (serial (), draftN) Inttab.empty
  Inttab.empty (make_history ProtoPureN 0 []) (make_ancestry [] []);


(* trivial merge *)

fun merge (thy1, thy2) =
  if subthy (thy2, thy1) then thy1
  else if subthy (thy1, thy2) then thy2
  else (check_merge thy1 thy2;
    raise TERM (cat_lines ["Attempt to perform non-trivial merge of theories:",
      str_of_thy thy1, str_of_thy thy2], []));

fun merge_refs (ref1, ref2) = self_ref (merge (deref ref1, deref ref2));


(* non-trivial merge *)

fun merge_internal pp (thy1, thy2) =
  if subthy_internal (thy2, thy1) then thy1
  else if subthy_internal (thy1, thy2) then thy2
  else if exists_name CPureN thy1 <> exists_name CPureN thy2 then
    error "Cannot merge Pure and CPure developments"
  else
    let
      val ids = check_merge thy1 thy2;
      val data = merge_data (pp thy1) (data_of thy1, data_of thy2);
      val history = make_history "" 0 [];
      val ancestry = make_ancestry [] [];
    in create_thy draftN NONE (serial (), draftN) ids data history ancestry end;


(* named theory nodes *)

val theory_name = #name o history_of;

fun begin_theory pp name imports =
  if name = draftN then
    error ("Illegal theory name: " ^ quote draftN)
  else if exists is_draft imports then
    error "Attempt to import draft theories"
  else
    let
      val parents = gen_distinct eq_thy imports;
      val ancestors = gen_distinct eq_thy (parents @ List.concat (map ancestors_of parents));
      val Theory ({id, ids, ...}, data, _, _) =
        (case parents of
          [] => error "No parent theories"
        | thy :: thys => extend_thy (Library.foldl (merge_internal pp) (thy, thys)));
      val history = make_history name 0 [];
      val ancestry = make_ancestry parents ancestors;
    in create_thy draftN NONE id ids data history ancestry end;

fun end_theory thy =
  thy
(*|> purge_thy  FIXME *)
  |> name_thy (theory_name thy);




(*** ML theory context ***)

local
  val current_theory = ref (NONE: theory option);
in
  fun get_context () = ! current_theory;
  fun set_context opt_thy = current_theory := opt_thy;
  fun setmp opt_thy f x = Library.setmp current_theory opt_thy f x;
end;

fun the_context () =
  (case get_context () of
    SOME thy => thy
  | _ => error "Unknown theory context");

fun context thy = set_context (SOME thy);
fun reset_context () = set_context NONE;

fun pass opt_thy f x =
  setmp opt_thy (fn x => let val y = f x in (y, get_context ()) end) x;

fun pass_theory thy f x =
  (case pass (SOME thy) f x of
    (y, SOME thy') => (y, thy')
  | (_, NONE) => error "Lost theory context in ML");

fun save f x = setmp (get_context ()) f x;


(* map context *)

nonfix >>;
fun >> f = set_context (SOME (f (the_context ())));


(* use ML text *)

val ml_output = (writeln, error_msg);

fun use_output verb txt = use_text ml_output verb (Symbol.escape txt);

fun use_mltext txt verb opt_thy = setmp opt_thy (fn () => use_output verb txt) ();
fun use_mltext_theory txt verb thy = #2 (pass_theory thy (use_output verb) txt);

fun use_context txt = use_mltext_theory ("Context.>> (" ^ txt ^ ");") false;

fun use_let bind body txt =
  use_context ("let " ^ bind ^ " = " ^ txt ^ " in\n" ^ body ^ " end");


(* delayed theory setup *)

local
  val setup_fns = ref ([]: (theory -> theory) list);
in
  fun add_setup fns = setup_fns := ! setup_fns @ fns;
  fun setup () = let val fns = ! setup_fns in setup_fns := []; fns end;
end;

end;

structure BasicContext: BASIC_CONTEXT = Context;
open BasicContext;



(*** type-safe interface for theory data ***)

signature THEORY_DATA_ARGS =
sig
  val name: string
  type T
  val empty: T
  val copy: T -> T
  val extend: T -> T
  val merge: Pretty.pp -> T * T -> T
  val print: theory -> T -> unit
end;

signature THEORY_DATA =
sig
  type T
  val init: theory -> theory
  val print: theory -> unit
  val get: theory -> T
  val put: T -> theory -> theory
  val map: (T -> T) -> theory -> theory
end;

functor TheoryDataFun(Data: THEORY_DATA_ARGS): THEORY_DATA =
struct

structure TheoryData = Context.TheoryData;

type T = Data.T;
exception Data of T;

val kind = TheoryData.declare Data.name
  (Data Data.empty)
  (fn Data x => Data (Data.copy x))
  (fn Data x => Data (Data.extend x))
  (fn pp => fn (Data x1, Data x2) => Data (Data.merge pp (x1, x2)))
  (fn thy => fn Data x => Data.print thy x);

val init = TheoryData.init kind;
val print = TheoryData.print kind;
val get = TheoryData.get kind (fn Data x => x);
val get_sg = get;    (*obsolete*)
val put = TheoryData.put kind Data;
fun map f thy = put (f (get thy)) thy;

end;

(*hide private interface!*)
structure Context: CONTEXT = Context;
