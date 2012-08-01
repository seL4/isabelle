(*  Title:      Pure/context.ML
    Author:     Markus Wenzel, TU Muenchen

Generic theory contexts with unique identity, arbitrarily typed data,
monotonic development graph and history support.  Generic proof
contexts with arbitrarily typed data.

Firm naming conventions:
   thy, thy', thy1, thy2: theory
   ctxt, ctxt', ctxt1, ctxt2: Proof.context
   context: Context.generic
*)

signature BASIC_CONTEXT =
sig
  type theory
  type theory_ref
  exception THEORY of string * theory list
  structure Proof: sig type context end
  structure Proof_Context:
  sig
    val theory_of: Proof.context -> theory
    val init_global: theory -> Proof.context
  end
end;

signature CONTEXT =
sig
  include BASIC_CONTEXT
  (*theory context*)
  val timing: bool Unsynchronized.ref
  type pretty
  val parents_of: theory -> theory list
  val ancestors_of: theory -> theory list
  val theory_name: theory -> string
  val is_stale: theory -> bool
  val is_draft: theory -> bool
  val reject_draft: theory -> theory
  val PureN: string
  val display_names: theory -> string list
  val pretty_thy: theory -> Pretty.T
  val string_of_thy: theory -> string
  val pretty_abbrev_thy: theory -> Pretty.T
  val str_of_thy: theory -> string
  val get_theory: theory -> string -> theory
  val this_theory: theory -> string -> theory
  val deref: theory_ref -> theory
  val check_thy: theory -> theory_ref
  val eq_thy: theory * theory -> bool
  val subthy: theory * theory -> bool
  val joinable: theory * theory -> bool
  val merge: theory * theory -> theory
  val merge_refs: theory_ref * theory_ref -> theory_ref
  val copy_thy: theory -> theory
  val checkpoint_thy: theory -> theory
  val finish_thy: theory -> theory
  val begin_thy: (theory -> pretty) -> string -> theory list -> theory
  (*proof context*)
  val raw_transfer: theory -> Proof.context -> Proof.context
  (*generic context*)
  datatype generic = Theory of theory | Proof of Proof.context
  val cases: (theory -> 'a) -> (Proof.context -> 'a) -> generic -> 'a
  val mapping: (theory -> theory) -> (Proof.context -> Proof.context) -> generic -> generic
  val mapping_result: (theory -> 'a * theory) -> (Proof.context -> 'a * Proof.context) ->
    generic -> 'a * generic
  val the_theory: generic -> theory
  val the_proof: generic -> Proof.context
  val map_theory: (theory -> theory) -> generic -> generic
  val map_proof: (Proof.context -> Proof.context) -> generic -> generic
  val map_theory_result: (theory -> 'a * theory) -> generic -> 'a * generic
  val map_proof_result: (Proof.context -> 'a * Proof.context) -> generic -> 'a * generic
  val theory_map: (generic -> generic) -> theory -> theory
  val proof_map: (generic -> generic) -> Proof.context -> Proof.context
  val theory_of: generic -> theory  (*total*)
  val proof_of: generic -> Proof.context  (*total*)
  (*pretty printing context*)
  val pretty: Proof.context -> pretty
  val pretty_global: theory -> pretty
  val pretty_generic: generic -> pretty
  val pretty_context: (theory -> Proof.context) -> pretty -> Proof.context
  (*thread data*)
  val thread_data: unit -> generic option
  val the_thread_data: unit -> generic
  val set_thread_data: generic option -> unit
  val setmp_thread_data: generic option -> ('a -> 'b) -> 'a -> 'b
  val >> : (generic -> generic) -> unit
  val >>> : (generic -> 'a * generic) -> 'a
end;

signature PRIVATE_CONTEXT =
sig
  include CONTEXT
  structure Theory_Data:
  sig
    val declare: Position.T -> Object.T -> (Object.T -> Object.T) ->
      (pretty -> Object.T * Object.T -> Object.T) -> serial
    val get: serial -> (Object.T -> 'a) -> theory -> 'a
    val put: serial -> ('a -> Object.T) -> 'a -> theory -> theory
  end
  structure Proof_Data:
  sig
    val declare: (theory -> Object.T) -> serial
    val get: serial -> (Object.T -> 'a) -> Proof.context -> 'a
    val put: serial -> ('a -> Object.T) -> 'a -> Proof.context -> Proof.context
  end
end;

structure Context: PRIVATE_CONTEXT =
struct

(*** theory context ***)

(** theory data **)

(* data kinds and access methods *)

val timing = Unsynchronized.ref false;

(*private copy avoids potential conflict of table exceptions*)
structure Datatab = Table(type key = int val ord = int_ord);

datatype pretty = Pretty of Object.T;

local

type kind =
 {pos: Position.T,
  empty: Object.T,
  extend: Object.T -> Object.T,
  merge: pretty -> Object.T * Object.T -> Object.T};

val kinds = Synchronized.var "Theory_Data" (Datatab.empty: kind Datatab.table);

fun invoke name f k x =
  (case Datatab.lookup (Synchronized.value kinds) k of
    SOME kind =>
      if ! timing andalso name <> "" then
        Timing.cond_timeit true ("Theory_Data." ^ name ^ Position.str_of (#pos kind))
          (fn () => f kind x)
      else f kind x
  | NONE => raise Fail "Invalid theory data identifier");

in

fun invoke_empty k = invoke "" (K o #empty) k ();
val invoke_extend = invoke "extend" #extend;
fun invoke_merge pp = invoke "merge" (fn kind => #merge kind pp);

fun declare_theory_data pos empty extend merge =
  let
    val k = serial ();
    val kind = {pos = pos, empty = empty, extend = extend, merge = merge};
    val _ = Synchronized.change kinds (Datatab.update (k, kind));
  in k end;

val extend_data = Datatab.map invoke_extend;
fun merge_data pp = Datatab.join (invoke_merge pp) o pairself extend_data;

end;



(** datatype theory **)

datatype theory =
  Theory of
   (*identity*)
   {self: theory Unsynchronized.ref option,  (*dynamic self reference -- follows theory changes*)
    draft: bool,                  (*draft mode -- linear destructive changes*)
    id: serial,                   (*identifier*)
    ids: unit Inttab.table} *     (*cumulative identifiers of non-drafts -- symbolic body content*)
   (*data*)
   Object.T Datatab.table *       (*body content*)
   (*ancestry*)
   {parents: theory list,         (*immediate predecessors*)
    ancestors: theory list} *     (*all predecessors -- canonical reverse order*)
   (*history*)
   {name: string,                 (*official theory name*)
    stage: int};                  (*checkpoint counter*)

exception THEORY of string * theory list;

fun rep_theory (Theory args) = args;

val identity_of = #1 o rep_theory;
val data_of = #2 o rep_theory;
val ancestry_of = #3 o rep_theory;
val history_of = #4 o rep_theory;

fun make_identity self draft id ids = {self = self, draft = draft, id = id, ids = ids};
fun make_ancestry parents ancestors = {parents = parents, ancestors = ancestors};
fun make_history name stage = {name = name, stage = stage};

val the_self = the o #self o identity_of;
val parents_of = #parents o ancestry_of;
val ancestors_of = #ancestors o ancestry_of;
val theory_name = #name o history_of;


(* staleness *)

fun eq_id (i: int, j) = i = j;

fun is_stale
    (Theory ({self =
        SOME (Unsynchronized.ref (Theory ({id = id', ...}, _, _, _))), id, ...}, _, _, _)) =
      not (eq_id (id, id'))
  | is_stale (Theory ({self = NONE, ...}, _, _, _)) = true;

fun vitalize (thy as Theory ({self = SOME r, ...}, _, _, _)) = (r := thy; thy)
  | vitalize (thy as Theory ({self = NONE, draft, id, ids}, data, ancestry, history)) =
      let
        val r = Unsynchronized.ref thy;
        val thy' = Theory (make_identity (SOME r) draft id ids, data, ancestry, history);
      in r := thy'; thy' end;


(* draft mode *)

val is_draft = #draft o identity_of;

fun reject_draft thy =
  if is_draft thy then
    raise THEORY ("Illegal draft theory -- stable checkpoint required", [thy])
  else thy;


(* names *)

val PureN = "Pure";
val draftN = "#";
val finished = ~1;

fun display_names thy =
  let
    val draft = if is_draft thy then [draftN] else [];
    val {stage, ...} = history_of thy;
    val name =
      if stage = finished then theory_name thy
      else theory_name thy ^ ":" ^ string_of_int stage;
    val ancestor_names = map theory_name (ancestors_of thy);
    val stale = if is_stale thy then ["!"] else [];
  in rev (stale @ draft @ [name] @ ancestor_names) end;

val pretty_thy = Pretty.str_list "{" "}" o display_names;
val string_of_thy = Pretty.string_of o pretty_thy;

fun pretty_abbrev_thy thy =
  let
    val names = display_names thy;
    val n = length names;
    val abbrev = if n > 5 then "..." :: List.drop (names, n - 5) else names;
  in Pretty.str_list "{" "}" abbrev end;

val str_of_thy = Pretty.str_of o pretty_abbrev_thy;

fun get_theory thy name =
  if theory_name thy <> name then
    (case find_first (fn thy' => theory_name thy' = name) (ancestors_of thy) of
      SOME thy' => thy'
    | NONE => error ("Unknown ancestor theory " ^ quote name))
  else if #stage (history_of thy) = finished then thy
  else error ("Unfinished theory " ^ quote name);

fun this_theory thy name =
  if theory_name thy = name then thy
  else get_theory thy name;


(* theory references *)

(*theory_ref provides a safe way to store dynamic references to a
  theory in external data structures -- a plain theory value would
  become stale as the self reference moves on*)

datatype theory_ref = Theory_Ref of theory Unsynchronized.ref;

fun deref (Theory_Ref (Unsynchronized.ref thy)) = thy;

fun check_thy thy =  (*thread-safe version*)
  let val thy_ref = Theory_Ref (the_self thy) in
    if is_stale thy then error ("Stale theory encountered:\n" ^ string_of_thy thy)
    else thy_ref
  end;


(* build ids *)

fun insert_id draft id ids =
  if draft then ids
  else Inttab.update (id, ()) ids;

fun merge_ids
    (Theory ({draft = draft1, id = id1, ids = ids1, ...}, _, _, _))
    (Theory ({draft = draft2, id = id2, ids = ids2, ...}, _, _, _)) =
  Inttab.merge (K true) (ids1, ids2)
  |> insert_id draft1 id1
  |> insert_id draft2 id2;


(* equality and inclusion *)

val eq_thy = eq_id o pairself (#id o identity_of);

fun proper_subthy (Theory ({id, ...}, _, _, _), Theory ({ids, ...}, _, _, _)) =
  Inttab.defined ids id;

fun subthy thys = eq_thy thys orelse proper_subthy thys;

fun joinable (thy1, thy2) = subthy (thy1, thy2) orelse subthy (thy2, thy1);


(* consistent ancestors *)

fun extend_ancestors thy thys =
  if member eq_thy thys thy then
    raise THEORY ("Duplicate theory node", thy :: thys)
  else thy :: thys;

fun extend_ancestors_of thy = extend_ancestors thy (ancestors_of thy);

val merge_ancestors = merge (fn (thy1, thy2) =>
  eq_thy (thy1, thy2) orelse
    theory_name thy1 = theory_name thy2 andalso
      raise THEORY ("Inconsistent theory versions", [thy1, thy2]));


(* trivial merge *)

fun merge (thy1, thy2) =
  if eq_thy (thy1, thy2) then thy1
  else if proper_subthy (thy2, thy1) then thy1
  else if proper_subthy (thy1, thy2) then thy2
  else error (cat_lines ["Attempt to perform non-trivial merge of theories:",
    str_of_thy thy1, str_of_thy thy2]);

fun merge_refs (ref1, ref2) =
  if ref1 = ref2 then ref1
  else check_thy (merge (deref ref1, deref ref2));



(** build theories **)

(* primitives *)

local
  val lock = Mutex.mutex ();
in
  fun SYNCHRONIZED e = Simple_Thread.synchronized "theory" lock e;
end;

fun create_thy self draft ids data ancestry history =
  let val identity = make_identity self draft (serial ()) ids;
  in vitalize (Theory (identity, data, ancestry, history)) end;

fun change_thy draft' f thy =
  let
    val Theory ({self, draft, id, ids}, data, ancestry, history) = thy;
    val (self', data', ancestry') =
      if draft then (self, data, ancestry)    (*destructive change!*)
      else if #stage history > 0
      then (NONE, data, ancestry)
      else (NONE, extend_data data, make_ancestry [thy] (extend_ancestors_of thy));
    val ids' = insert_id draft id ids;
    val data'' = f data';
    val thy' = SYNCHRONIZED (fn () =>
      (check_thy thy; create_thy self' draft' ids' data'' ancestry' history));
  in thy' end;

val name_thy = change_thy false I;
val extend_thy = change_thy true I;
val modify_thy = change_thy true;

fun copy_thy thy =
  let
    val Theory ({draft, id, ids, ...}, data, ancestry, history) = thy;
    val ids' = insert_id draft id ids;
    val thy' = SYNCHRONIZED (fn () =>
      (check_thy thy; create_thy NONE true ids' data ancestry history));
  in thy' end;

val pre_pure_thy = create_thy NONE true Inttab.empty
  Datatab.empty (make_ancestry [] []) (make_history PureN 0);


(* named theory nodes *)

fun merge_thys pp (thy1, thy2) =
  let
    val ids = merge_ids thy1 thy2;
    val data = merge_data (pp thy1) (data_of thy1, data_of thy2);
    val ancestry = make_ancestry [] [];
    val history = make_history "" 0;
    val thy' = SYNCHRONIZED (fn () =>
     (check_thy thy1; check_thy thy2; create_thy NONE true ids data ancestry history));
  in thy' end;

fun maximal_thys thys =
  thys |> filter_out (fn thy => exists (fn thy' => proper_subthy (thy, thy')) thys);

fun begin_thy pp name imports =
  if name = "" orelse name = draftN then error ("Bad theory name: " ^ quote name)
  else
    let
      val parents = maximal_thys (distinct eq_thy imports);
      val ancestors =
        Library.foldl merge_ancestors ([], map ancestors_of parents)
        |> fold extend_ancestors parents;

      val Theory ({ids, ...}, data, _, _) =
        (case parents of
          [] => error "Missing theory imports"
        | [thy] => extend_thy thy
        | thy :: thys => Library.foldl (merge_thys pp) (thy, thys));

      val ancestry = make_ancestry parents ancestors;
      val history = make_history name 0;
      val thy' = SYNCHRONIZED (fn () =>
        (map check_thy imports; create_thy NONE true ids data ancestry history));
    in thy' end;


(* history stages *)

fun history_stage f thy =
  let
    val {name, stage} = history_of thy;
    val _ = stage = finished andalso raise THEORY ("Theory already finished", [thy]);
    val history' = make_history name (f stage);
    val thy' as Theory (identity', data', ancestry', _) = name_thy thy;
    val thy'' = SYNCHRONIZED (fn () =>
      (check_thy thy'; vitalize (Theory (identity', data', ancestry', history'))));
  in thy'' end;

fun checkpoint_thy thy =
  if is_draft thy then history_stage (fn stage => stage + 1) thy
  else thy;

val finish_thy = history_stage (fn _ => finished);


(* theory data *)

structure Theory_Data =
struct

val declare = declare_theory_data;

fun get k dest thy =
  (case Datatab.lookup (data_of thy) k of
    SOME x => x
  | NONE => invoke_empty k) |> dest;

fun put k mk x = modify_thy (Datatab.update (k, mk x));

end;



(*** proof context ***)

(* datatype Proof.context *)

structure Proof =
struct
  datatype context = Context of Object.T Datatab.table * theory_ref;
end;

fun theory_of_proof (Proof.Context (_, thy_ref)) = deref thy_ref;
fun data_of_proof (Proof.Context (data, _)) = data;
fun map_prf f (Proof.Context (data, thy_ref)) = Proof.Context (f data, thy_ref);


(* proof data kinds *)

local

val kinds = Synchronized.var "Proof_Data" (Datatab.empty: (theory -> Object.T) Datatab.table);

fun invoke_init k =
  (case Datatab.lookup (Synchronized.value kinds) k of
    SOME init => init
  | NONE => raise Fail "Invalid proof data identifier");

fun init_data thy =
  Datatab.map (fn k => fn _ => invoke_init k thy) (Synchronized.value kinds);

fun init_new_data data thy =
  Datatab.merge (K true) (data, init_data thy);

in

fun raw_transfer thy' (Proof.Context (data, thy_ref)) =
  let
    val thy = deref thy_ref;
    val _ = subthy (thy, thy') orelse error "transfer proof context: not a super theory";
    val _ = check_thy thy;
    val data' = init_new_data data thy';
    val thy_ref' = check_thy thy';
  in Proof.Context (data', thy_ref') end;

structure Proof_Context =
struct
  val theory_of = theory_of_proof;
  fun init_global thy = Proof.Context (init_data thy, check_thy thy);
end;

structure Proof_Data =
struct

fun declare init =
  let
    val k = serial ();
    val _ = Synchronized.change kinds (Datatab.update (k, init));
  in k end;

fun get k dest prf =
  dest (case Datatab.lookup (data_of_proof prf) k of
    SOME x => x
  | NONE => invoke_init k (Proof_Context.theory_of prf));   (*adhoc value*)

fun put k mk x = map_prf (Datatab.update (k, mk x));

end;

end;



(*** generic context ***)

datatype generic = Theory of theory | Proof of Proof.context;

fun cases f _ (Theory thy) = f thy
  | cases _ g (Proof prf) = g prf;

fun mapping f g = cases (Theory o f) (Proof o g);
fun mapping_result f g = cases (apsnd Theory o f) (apsnd Proof o g);

val the_theory = cases I (fn _ => error "Ill-typed context: theory expected");
val the_proof = cases (fn _ => error "Ill-typed context: proof expected") I;

fun map_theory f = Theory o f o the_theory;
fun map_proof f = Proof o f o the_proof;

fun map_theory_result f = apsnd Theory o f o the_theory;
fun map_proof_result f = apsnd Proof o f o the_proof;

fun theory_map f = the_theory o f o Theory;
fun proof_map f = the_proof o f o Proof;

val theory_of = cases I Proof_Context.theory_of;
val proof_of = cases Proof_Context.init_global I;


(* pretty printing context *)

exception PRETTY of generic;

val pretty_generic = Pretty o PRETTY;
val pretty = pretty_generic o Proof;
val pretty_global = pretty_generic o Theory;

fun pretty_context init (Pretty (PRETTY context)) = cases init I context;



(** thread data **)

local val tag = Universal.tag () : generic option Universal.tag in

fun thread_data () =
  (case Thread.getLocal tag of
    SOME (SOME context) => SOME context
  | _ => NONE);

fun the_thread_data () =
  (case thread_data () of
    SOME context => context
  | _ => error "Unknown context");

fun set_thread_data context = Thread.setLocal (tag, context);
fun setmp_thread_data context = Library.setmp_thread_data tag (thread_data ()) context;

end;

fun >>> f =
  let
    val (res, context') = f (the_thread_data ());
    val _ = set_thread_data (SOME context');
  in res end;

nonfix >>;
fun >> f = >>> (fn context => ((), f context));

val _ = set_thread_data (SOME (Theory pre_pure_thy));

end;

structure Basic_Context: BASIC_CONTEXT = Context;
open Basic_Context;



(*** type-safe interfaces for data declarations ***)

(** theory data **)

signature THEORY_DATA_PP_ARGS =
sig
  type T
  val empty: T
  val extend: T -> T
  val merge: Context.pretty -> T * T -> T
end;

signature THEORY_DATA_ARGS =
sig
  type T
  val empty: T
  val extend: T -> T
  val merge: T * T -> T
end;

signature THEORY_DATA =
sig
  type T
  val get: theory -> T
  val put: T -> theory -> theory
  val map: (T -> T) -> theory -> theory
end;

functor Theory_Data_PP(Data: THEORY_DATA_PP_ARGS): THEORY_DATA =
struct

type T = Data.T;
exception Data of T;

val kind =
  Context.Theory_Data.declare
    (Position.thread_data ())
    (Data Data.empty)
    (fn Data x => Data (Data.extend x))
    (fn pp => fn (Data x1, Data x2) => Data (Data.merge pp (x1, x2)));

val get = Context.Theory_Data.get kind (fn Data x => x);
val put = Context.Theory_Data.put kind Data;
fun map f thy = put (f (get thy)) thy;

end;

functor Theory_Data(Data: THEORY_DATA_ARGS): THEORY_DATA =
  Theory_Data_PP
  (
    type T = Data.T;
    val empty = Data.empty;
    val extend = Data.extend;
    fun merge _ = Data.merge;
  );



(** proof data **)

signature PROOF_DATA_ARGS =
sig
  type T
  val init: theory -> T
end;

signature PROOF_DATA =
sig
  type T
  val get: Proof.context -> T
  val put: T -> Proof.context -> Proof.context
  val map: (T -> T) -> Proof.context -> Proof.context
end;

functor Proof_Data(Data: PROOF_DATA_ARGS): PROOF_DATA =
struct

type T = Data.T;
exception Data of T;

val kind = Context.Proof_Data.declare (Data o Data.init);

val get = Context.Proof_Data.get kind (fn Data x => x);
val put = Context.Proof_Data.put kind Data;
fun map f prf = put (f (get prf)) prf;

end;



(** generic data **)

signature GENERIC_DATA_ARGS =
sig
  type T
  val empty: T
  val extend: T -> T
  val merge: T * T -> T
end;

signature GENERIC_DATA =
sig
  type T
  val get: Context.generic -> T
  val put: T -> Context.generic -> Context.generic
  val map: (T -> T) -> Context.generic -> Context.generic
end;

functor Generic_Data(Data: GENERIC_DATA_ARGS): GENERIC_DATA =
struct

structure Thy_Data = Theory_Data(Data);
structure Prf_Data = Proof_Data(type T = Data.T val init = Thy_Data.get);

type T = Data.T;

fun get (Context.Theory thy) = Thy_Data.get thy
  | get (Context.Proof prf) = Prf_Data.get prf;

fun put x (Context.Theory thy) = Context.Theory (Thy_Data.put x thy)
  | put x (Context.Proof prf) = Context.Proof (Prf_Data.put x prf);

fun map f ctxt = put (f (get ctxt)) ctxt;

end;

(*hide private interface*)
structure Context: CONTEXT = Context;

