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
  exception THEORY of string * theory list
  structure Proof: sig type context end
  structure Proof_Context:
  sig
    val theory_of: Proof.context -> theory
    val init_global: theory -> Proof.context
    val get_global: {long: bool} -> theory -> string -> Proof.context
  end
end;

signature CONTEXT =
sig
  include BASIC_CONTEXT
  (*theory context*)
  type theory_id
  val theory_id: theory -> theory_id
  val timing: bool Unsynchronized.ref
  val parents_of: theory -> theory list
  val ancestors_of: theory -> theory list
  val theory_id_ord: theory_id ord
  val theory_id_name: {long: bool} -> theory_id -> string
  val theory_long_name: theory -> string
  val theory_base_name: theory -> string
  val theory_name: {long: bool} -> theory -> string
  val theory_identifier: theory -> serial
  val PureN: string
  val pretty_thy: theory -> Pretty.T
  val pretty_abbrev_thy: theory -> Pretty.T
  val get_theory: {long: bool} -> theory -> string -> theory
  val eq_thy_id: theory_id * theory_id -> bool
  val eq_thy: theory * theory -> bool
  val proper_subthy_id: theory_id * theory_id -> bool
  val proper_subthy: theory * theory -> bool
  val subthy_id: theory_id * theory_id -> bool
  val subthy: theory * theory -> bool
  val trace_theories: bool Unsynchronized.ref
  val theories_trace: unit -> {active_positions: Position.T list, active: int, total: int}
  val join_thys: theory list -> theory
  val begin_thy: string -> theory list -> theory
  val finish_thy: theory -> theory
  val theory_data_sizeof1: theory -> (Position.T * int) list
  (*proof context*)
  val raw_transfer: theory -> Proof.context -> Proof.context
  (*certificate*)
  datatype certificate = Certificate of theory | Certificate_Id of theory_id
  val certificate_theory: certificate -> theory
  val certificate_theory_id: certificate -> theory_id
  val eq_certificate: certificate * certificate -> bool
  val join_certificate: certificate * certificate -> certificate
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
  (*thread data*)
  val get_generic_context: unit -> generic option
  val put_generic_context: generic option -> unit
  val setmp_generic_context: generic option -> ('a -> 'b) -> 'a -> 'b
  val the_generic_context: unit -> generic
  val the_global_context: unit -> theory
  val the_local_context: unit -> Proof.context
  val >> : (generic -> generic) -> unit
  val >>> : (generic -> 'a * generic) -> 'a
end;

signature PRIVATE_CONTEXT =
sig
  include CONTEXT
  structure Theory_Data:
  sig
    val declare: Position.T -> Any.T -> ((theory * Any.T) list -> Any.T) -> serial
    val get: serial -> (Any.T -> 'a) -> theory -> 'a
    val put: serial -> ('a -> Any.T) -> 'a -> theory -> theory
  end
  structure Proof_Data:
  sig
    val declare: (theory -> Any.T) -> serial
    val get: serial -> (Any.T -> 'a) -> Proof.context -> 'a
    val put: serial -> ('a -> Any.T) -> 'a -> Proof.context -> Proof.context
  end
end;

structure Context: PRIVATE_CONTEXT =
struct

(*** theory context ***)

(*private copy avoids potential conflict of table exceptions*)
structure Datatab = Table(type key = int val ord = int_ord);


(** datatype theory **)

(* implicit state *)

type state = {stage: int} Synchronized.var;

fun make_state () : state =
  Synchronized.var "Context.state" {stage = 0};

fun next_stage (state: state) =
  Synchronized.change_result state (fn {stage} => (stage + 1, {stage = stage + 1}));


(* theory_id *)

abstype theory_id =
  Theory_Id of
   {id: serial,                   (*identifier*)
    ids: Intset.T,                (*cumulative identifiers -- symbolic body content*)
    name: string,                 (*official theory name*)
    stage: int}                   (*index for anonymous updates*)
with

fun rep_theory_id (Theory_Id args) = args;
val make_theory_id = Theory_Id;

end;


(* theory *)

datatype theory =
  Theory of
   (*allocation state*)
   state *
   (*identity*)
   {theory_id: theory_id,
    token: Position.T Unsynchronized.ref} *
   (*ancestry*)
   {parents: theory list,         (*immediate predecessors*)
    ancestors: theory list} *     (*all predecessors -- canonical reverse order*)
   (*data*)
   Any.T Datatab.table;           (*body content*)

exception THEORY of string * theory list;

fun rep_theory (Theory args) = args;

val state_of = #1 o rep_theory;
val theory_identity = #2 o rep_theory;
val theory_id = #theory_id o theory_identity;
val identity_of = rep_theory_id o theory_id;
val ancestry_of = #3 o rep_theory;
val data_of = #4 o rep_theory;

fun make_ancestry parents ancestors = {parents = parents, ancestors = ancestors};

fun stage_final stage = stage = 0;

val theory_id_stage = #stage o rep_theory_id;
val theory_id_final = stage_final o theory_id_stage;
val theory_id_ord = int_ord o apply2 (#id o rep_theory_id);
fun theory_id_name {long} thy_id =
  let val name = #name (rep_theory_id thy_id)
  in if long then name else Long_Name.base_name name end;

val theory_long_name = #name o identity_of;
val theory_base_name = Long_Name.base_name o theory_long_name;
fun theory_name {long} = if long then theory_long_name else theory_base_name;
val theory_identifier = #id o identity_of;

val parents_of = #parents o ancestry_of;
val ancestors_of = #ancestors o ancestry_of;


(* names *)

val PureN = "Pure";

fun display_name thy_id =
  let
    val name = theory_id_name {long = false} thy_id;
    val final = theory_id_final thy_id;
  in if final then name else name ^ ":" ^ string_of_int (theory_id_stage thy_id) end;

fun display_names thy =
  let
    val name = display_name (theory_id thy);
    val ancestor_names = map theory_long_name (ancestors_of thy);
  in rev (name :: ancestor_names) end;

val pretty_thy = Pretty.str_list "{" "}" o display_names;

val _ = ML_system_pp (fn _ => fn _ => Pretty.to_polyml o pretty_thy);

fun pretty_abbrev_thy thy =
  let
    val names = display_names thy;
    val n = length names;
    val abbrev = if n > 5 then "..." :: List.drop (names, n - 5) else names;
  in Pretty.str_list "{" "}" abbrev end;

fun get_theory long thy name =
  if theory_name long thy <> name then
    (case find_first (fn thy' => theory_name long thy' = name) (ancestors_of thy) of
      SOME thy' => thy'
    | NONE => error ("Unknown ancestor theory " ^ quote name))
  else if theory_id_final (theory_id thy) then thy
  else error ("Unfinished theory " ^ quote name);


(* identity *)

fun merge_ids thys =
  fold (identity_of #> (fn {id, ids, ...} => fn acc => Intset.merge (acc, ids) |> Intset.insert id))
    thys Intset.empty;

val eq_thy_id = op = o apply2 (#id o rep_theory_id);
val eq_thy = op = o apply2 (#id o identity_of);

val proper_subthy_id = apply2 rep_theory_id #> (fn ({id, ...}, {ids, ...}) => Intset.member ids id);
val proper_subthy = proper_subthy_id o apply2 theory_id;

fun subthy_id p = eq_thy_id p orelse proper_subthy_id p;
val subthy = subthy_id o apply2 theory_id;


(* consistent ancestors *)

fun eq_thy_consistent (thy1, thy2) =
  eq_thy (thy1, thy2) orelse
    (theory_base_name thy1 = theory_base_name thy2 andalso
      raise THEORY ("Duplicate theory name", [thy1, thy2]));

fun extend_ancestors thy thys =
  if member eq_thy_consistent thys thy then
    raise THEORY ("Duplicate theory node", thy :: thys)
  else thy :: thys;

val merge_ancestors = merge eq_thy_consistent;

val eq_ancestry =
  apply2 ancestry_of #>
    (fn ({parents, ancestors}, {parents = parents', ancestors = ancestors'}) =>
      eq_list eq_thy (parents, parents') andalso eq_list eq_thy (ancestors, ancestors'));



(** theory data **)

(* data kinds and access methods *)

val timing = Unsynchronized.ref false;

local

type kind =
 {pos: Position.T,
  empty: Any.T,
  merge: (theory * Any.T) list -> Any.T};

val kinds = Synchronized.var "Theory_Data" (Datatab.empty: kind Datatab.table);

fun the_kind k =
  (case Datatab.lookup (Synchronized.value kinds) k of
    SOME kind => kind
  | NONE => raise Fail "Invalid theory data identifier");

in

val invoke_pos = #pos o the_kind;
val invoke_empty = #empty o the_kind;

fun invoke_merge kind args =
  if ! timing then
    Timing.cond_timeit true ("Theory_Data.merge" ^ Position.here (#pos kind))
      (fn () => #merge kind args)
  else #merge kind args;

fun declare_data pos empty merge =
  let
    val k = serial ();
    val kind = {pos = pos, empty = empty, merge = merge};
    val _ = Synchronized.change kinds (Datatab.update (k, kind));
  in k end;

fun lookup_data k thy = Datatab.lookup (data_of thy) k;

fun get_data k thy =
  (case lookup_data k thy of
    SOME x => x
  | NONE => invoke_empty k);

fun merge_data [] = Datatab.empty
  | merge_data [thy] = data_of thy
  | merge_data thys =
      let
        fun merge (k, kind) data =
          (case map_filter (fn thy => lookup_data k thy |> Option.map (pair thy)) thys of
            [] => data
          | [(_, x)] => Datatab.default (k, x) data
          | args => Datatab.update (k, invoke_merge kind args) data);
      in Datatab.fold merge (Synchronized.value kinds) (data_of (hd thys)) end;

end;



(** build theories **)

(* create theory *)

val trace_theories = Unsynchronized.ref false;

local

val theories =
  Synchronized.var "theory_tokens"
    ([]: Position.T Unsynchronized.ref option Unsynchronized.ref list);

val dummy_token = Unsynchronized.ref Position.none;

fun make_token () =
  if ! trace_theories then
    let
      val token = Unsynchronized.ref (Position.thread_data ());
      val _ = Synchronized.change theories (cons (Weak.weak (SOME token)));
    in token end
  else dummy_token;

in

fun theories_trace () =
  let
    val trace = Synchronized.value theories;
    val _ = ML_Heap.full_gc ();
    val active_positions =
      fold (fn Unsynchronized.ref (SOME pos) => cons (! pos) | _ => I) trace [];
  in
    {active_positions = active_positions,
     active = length active_positions,
     total = length trace}
  end;

fun create_thy state ids name stage ancestry data =
  let
    val theory_id = make_theory_id {id = serial (), ids = ids, name = name, stage = stage};
    val identity = {theory_id = theory_id, token = make_token ()};
  in Theory (state, identity, ancestry, data) end;

end;


(* primitives *)

val pre_pure_thy =
  let
    val state = make_state ();
    val stage = next_stage state;
  in create_thy state Intset.empty PureN stage (make_ancestry [] []) Datatab.empty end;

local

fun change_thy finish f thy =
  let
    val {name, stage, ...} = identity_of thy;
    val Theory (state, _, ancestry, data) = thy;
    val ancestry' =
      if stage_final stage
      then make_ancestry [thy] (extend_ancestors thy (ancestors_of thy))
      else ancestry;
    val ids' = merge_ids [thy];
    val stage' = if finish then 0 else next_stage state;
    val data' = f data;
  in create_thy state ids' name stage' ancestry' data' end;

in

val update_thy = change_thy false;
val finish_thy = change_thy true I;

end;


(* join: unfinished theory nodes *)

fun join_thys [] = raise List.Empty
  | join_thys thys =
      let
        val thy0 = hd thys;
        val name0 = theory_long_name thy0;
        val state0 = state_of thy0;

        fun ok thy =
          not (theory_id_final (theory_id thy)) andalso
          theory_long_name thy = name0 andalso
          eq_ancestry (thy0, thy);
        val _ =
          (case filter_out ok thys of
            [] => ()
          | bad => raise THEORY ("Cannot join theories", bad));

        val stage = next_stage state0;
        val ids = merge_ids thys;
        val data = merge_data thys;
      in create_thy state0 ids name0 stage (ancestry_of thy0) data end;


(* merge: finished theory nodes *)

fun make_parents thys =
  let val thys' = distinct eq_thy thys
  in thys' |> filter_out (fn thy => exists (fn thy' => proper_subthy (thy, thy')) thys') end;

fun begin_thy name imports =
  if name = "" then error ("Bad theory name: " ^ quote name)
  else if null imports then error "Missing theory imports"
  else
    let
      val parents = make_parents imports;
      val ancestors =
        Library.foldl1 merge_ancestors (map ancestors_of parents)
        |> fold extend_ancestors parents;
      val ancestry = make_ancestry parents ancestors;

      val state = make_state ();
      val stage = next_stage state;
      val ids = merge_ids parents;
      val data = merge_data parents;
    in create_thy state ids name stage ancestry data |> tap finish_thy end;


(* theory data *)

structure Theory_Data =
struct

val declare = declare_data;

fun get k dest thy = dest (get_data k thy);

fun put k make x = update_thy (Datatab.update (k, make x));

fun sizeof1 k thy =
  Datatab.lookup (data_of thy) k |> Option.map ML_Heap.sizeof1;

end;

fun theory_data_sizeof1 thy =
  build (data_of thy |> Datatab.fold_rev (fn (k, _) =>
    (case Theory_Data.sizeof1 k thy of
      NONE => I
    | SOME n => (cons (invoke_pos k, n)))));



(*** proof context ***)

(* datatype Proof.context *)

structure Proof =
struct
  datatype context = Context of Any.T Datatab.table * theory;
end;


(* proof data kinds *)

local

val kinds = Synchronized.var "Proof_Data" (Datatab.empty: (theory -> Any.T) Datatab.table);

fun init_data thy =
  Synchronized.value kinds |> Datatab.map (fn _ => fn init => init thy);

fun init_new_data thy =
  Synchronized.value kinds |> Datatab.fold (fn (k, init) => fn data =>
    if Datatab.defined data k then data
    else Datatab.update (k, init thy) data);

fun init_fallback k thy =
  (case Datatab.lookup (Synchronized.value kinds) k of
    SOME init => init thy
  | NONE => raise Fail "Invalid proof data identifier");

in

fun raw_transfer thy' (Proof.Context (data, thy)) =
  let
    val _ = subthy (thy, thy') orelse error "Cannot transfer proof context: not a super theory";
    val data' = init_new_data thy' data;
  in Proof.Context (data', thy') end;

structure Proof_Context =
struct
  fun theory_of (Proof.Context (_, thy)) = thy;
  fun init_global thy = Proof.Context (init_data thy, thy);
  fun get_global long thy name = init_global (get_theory long thy name);
end;

structure Proof_Data =
struct

fun declare init =
  let
    val k = serial ();
    val _ = Synchronized.change kinds (Datatab.update (k, init));
  in k end;

fun get k dest (Proof.Context (data, thy)) =
  (case Datatab.lookup data k of
    SOME x => x
  | NONE => init_fallback k thy) |> dest;

fun put k make x (Proof.Context (data, thy)) =
  Proof.Context (Datatab.update (k, make x) data, thy);

end;

end;



(*** theory certificate ***)

datatype certificate = Certificate of theory | Certificate_Id of theory_id;

fun certificate_theory (Certificate thy) = thy
  | certificate_theory (Certificate_Id thy_id) =
      error ("No content for theory certificate " ^ display_name thy_id);

fun certificate_theory_id (Certificate thy) = theory_id thy
  | certificate_theory_id (Certificate_Id thy_id) = thy_id;

fun eq_certificate (Certificate thy1, Certificate thy2) = eq_thy (thy1, thy2)
  | eq_certificate (Certificate_Id thy_id1, Certificate_Id thy_id2) = eq_thy_id (thy_id1, thy_id2)
  | eq_certificate _ = false;

fun join_certificate (cert1, cert2) =
  let val (thy_id1, thy_id2) = apply2 certificate_theory_id (cert1, cert2) in
    if eq_thy_id (thy_id1, thy_id2) then (case cert1 of Certificate _ => cert1 | _ => cert2)
    else if proper_subthy_id (thy_id2, thy_id1) then cert1
    else if proper_subthy_id (thy_id1, thy_id2) then cert2
    else
      error ("Cannot join unrelated theory certificates " ^
        display_name thy_id1 ^ " and " ^ display_name thy_id2)
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



(** thread data **)

local val generic_context_var = Thread_Data.var () : generic Thread_Data.var in

fun get_generic_context () = Thread_Data.get generic_context_var;
val put_generic_context = Thread_Data.put generic_context_var;
fun setmp_generic_context opt_context = Thread_Data.setmp generic_context_var opt_context;

fun the_generic_context () =
  (case get_generic_context () of
    SOME context => context
  | _ => error "Unknown context");

val the_global_context = theory_of o the_generic_context;
val the_local_context = proof_of o the_generic_context;

end;

fun >>> f =
  let
    val (res, context') = f (the_generic_context ());
    val _ = put_generic_context (SOME context');
  in res end;

nonfix >>;
fun >> f = >>> (fn context => ((), f context));

val _ = put_generic_context (SOME (Theory pre_pure_thy));

end;

structure Basic_Context: BASIC_CONTEXT = Context;
open Basic_Context;



(*** type-safe interfaces for data declarations ***)

(** theory data **)

signature THEORY_DATA'_ARGS =
sig
  type T
  val empty: T
  val merge: (theory * T) list -> T
end;

signature THEORY_DATA_ARGS =
sig
  type T
  val empty: T
  val merge: T * T -> T
end;

signature THEORY_DATA =
sig
  type T
  val get: theory -> T
  val put: T -> theory -> theory
  val map: (T -> T) -> theory -> theory
end;

functor Theory_Data'(Data: THEORY_DATA'_ARGS): THEORY_DATA =
struct

type T = Data.T;
exception Data of T;

val kind =
  let val pos = Position.thread_data () in
    Context.Theory_Data.declare
      pos
      (Data Data.empty)
      (Data o Data.merge o map (fn (thy, Data x) => (thy, x)))
  end;

val get = Context.Theory_Data.get kind (fn Data x => x);
val put = Context.Theory_Data.put kind Data;
fun map f thy = put (f (get thy)) thy;

end;

functor Theory_Data(Data: THEORY_DATA_ARGS): THEORY_DATA =
  Theory_Data'
  (
    type T = Data.T;
    val empty = Data.empty;
    fun merge args = Library.foldl (fn (a, (_, b)) => Data.merge (a, b)) (#2 (hd args), tl args)
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
