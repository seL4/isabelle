(*  Title:      Pure/context.ML
    Author:     Makarius

Generic theory contexts with unique identity, arbitrarily typed data, and
monotonic updates.

Generic proof contexts with arbitrarily typed data.

Good names:
   thy, thy', thy1, thy2: theory
   ctxt, ctxt', ctxt1, ctxt2: Proof.context
   context: Context.generic

Bad names:
  ctx: Proof.context
  context: Proof.context
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
  (*theory data*)
  type data_kind = int
  val data_kinds: unit -> (data_kind * Position.T) list
  (*theory context*)
  type id = int
  type theory_id
  val theory_id: theory -> theory_id
  val data_timing: bool Unsynchronized.ref
  val parents_of: theory -> theory list
  val ancestors_of: theory -> theory list
  val theory_id_ord: theory_id ord
  val theory_id_name: {long: bool} -> theory_id -> string
  val theory_long_name: theory -> string
  val theory_base_name: theory -> string
  val theory_name: {long: bool} -> theory -> string
  val theory_identifier: theory -> id
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
  val join_certificate_theory: theory * theory -> theory
  (*generic context*)
  datatype generic = Theory of theory | Proof of Proof.context
  val theory_tracing: bool Unsynchronized.ref
  val proof_tracing: bool Unsynchronized.ref
  val enabled_tracing: unit -> bool
  val finish_tracing: unit ->
   {contexts: (generic * Position.T) list,
    active_contexts: int,
    active_theories: int,
    active_proofs: int,
    total_contexts: int,
    total_theories: int,
    total_proofs: int}
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
    val declare: Position.T -> Any.T -> ((theory * Any.T) list -> Any.T) -> data_kind
    val get: data_kind -> (Any.T -> 'a) -> theory -> 'a
    val put: data_kind -> ('a -> Any.T) -> 'a -> theory -> theory
  end
  structure Proof_Data:
  sig
    val declare: (theory -> Any.T) -> data_kind
    val get: data_kind -> (Any.T -> 'a) -> Proof.context -> 'a
    val put: data_kind -> ('a -> Any.T) -> 'a -> Proof.context -> Proof.context
  end
end;

structure Context: PRIVATE_CONTEXT =
struct

(*** type definitions ***)

(* context data *)

(*private copy avoids potential conflict of table exceptions*)
structure Datatab = Table(type key = int val ord = int_ord);

type data_kind = int;
val data_kind = Counter.make ();


(* theory identity *)

type id = int;

local
  val new_block = Counter.make ();
  fun new_elem () = Bitset.make_elem (new_block (), 0);
  val var = Thread_Data.var () : id Thread_Data.var;
in

fun new_id () =
  let
    val id =
      (case Option.map Bitset.dest_elem (Thread_Data.get var) of
        NONE => new_elem ()
      | SOME (m, n) =>
          (case try Bitset.make_elem (m, n + 1) of
            NONE => new_elem ()
          | SOME elem => elem));
    val _ = Thread_Data.put var (SOME id);
  in id end;

end;

abstype theory_id =
  Thy_Id of
   {id: id,         (*identifier*)
    ids: Bitset.T,  (*cumulative identifiers -- symbolic body content*)
    name: string,   (*official theory name*)
    stage: int}     (*index for anonymous updates*)
with
  fun rep_theory_id (Thy_Id args) = args;
  val make_theory_id = Thy_Id;
end;


(* theory allocation state *)

type state = {stage: int} Synchronized.var;

fun make_state () : state =
  Synchronized.var "Context.state" {stage = 0};

fun next_stage (state: state) =
  Synchronized.change_result state (fn {stage} => (stage + 1, {stage = stage + 1}));


(* theory and proof context *)

datatype theory =
  Thy_Undef
| Thy of
    (*allocation state*)
    state *
    (*identity*)
    {theory_id: theory_id,
     theory_token: theory Unsynchronized.ref,
     theory_token_pos: Position.T} *
    (*ancestry*)
    {parents: theory list,         (*immediate predecessors*)
     ancestors: theory list} *     (*all predecessors -- canonical reverse order*)
    (*data*)
    Any.T Datatab.table;           (*body content*)

datatype proof =
  Prf_Undef
| Prf of
    (*identity*)
    proof Unsynchronized.ref *  (*token*)
    Position.T *                (*token_pos*)
    theory *
    (*data*)
    Any.T Datatab.table;

structure Proof = struct type context = proof end;

datatype generic = Theory of theory | Proof of Proof.context;


(* heap allocations *)

val theory_tracing = Unsynchronized.ref false;
val proof_tracing = Unsynchronized.ref false;

fun enabled_tracing () = ! theory_tracing orelse ! proof_tracing;

local

val m = Integer.pow 18 2;

fun cons_tokens var token =
  Synchronized.change var (fn (n, tokens) =>
    let val tokens' = if n mod m = 0 then filter Unsynchronized.weak_active tokens else tokens
    in (n + 1, Weak.weak (SOME token) :: tokens') end);

fun finish_tokens var =
  Synchronized.change_result var (fn (n, tokens) =>
    let
      val tokens' = filter Unsynchronized.weak_active tokens;
      val results = map_filter Unsynchronized.weak_peek tokens';
    in ((n, results), (n, tokens')) end);

fun make_token guard var token0 =
  if ! guard then
    let
      val token = Unsynchronized.ref (! token0);
      val pos = Position.thread_data ();
      fun assign res = (token := res; cons_tokens var token; res);
    in (token, pos, assign) end
  else (token0, Position.none, I);

val theory_tokens = Synchronized.var "theory_tokens" (0, []: theory Unsynchronized.weak_ref list);
val proof_tokens = Synchronized.var "proof_tokens" (0, []: proof Unsynchronized.weak_ref list);

val theory_token0 = Unsynchronized.ref Thy_Undef;
val proof_token0 = Unsynchronized.ref Prf_Undef;

in

fun theory_token () = make_token theory_tracing theory_tokens theory_token0;
fun proof_token () = make_token proof_tracing proof_tokens proof_token0;

fun finish_tracing () =
  let
    val _ = ML_Heap.full_gc ();
    val (total_theories, token_theories) = finish_tokens theory_tokens;
    val (total_proofs, token_proofs) = finish_tokens proof_tokens;

    fun cons1 (thy as Thy (_, {theory_token_pos, ...}, _, _)) = cons (Theory thy, theory_token_pos)
      | cons1 _ = I;
    fun cons2 (ctxt as Prf (_, proof_token_pos, _, _)) = cons (Proof ctxt, proof_token_pos)
      | cons2 _ = I;

    val contexts = build (fold cons1 token_theories #> fold cons2 token_proofs);
    val active_theories = fold (fn (Theory _, _) => Integer.add 1 | _ => I) contexts 0;
    val active_proofs = fold (fn (Proof _, _) => Integer.add 1 | _ => I) contexts 0;
  in
    {contexts = contexts,
     active_contexts = active_theories + active_proofs,
     active_theories = active_theories,
     active_proofs = active_proofs,
     total_contexts = total_theories + total_proofs,
     total_theories = total_theories,
     total_proofs = total_proofs}
  end;

end;



(*** theory operations ***)

fun rep_theory (Thy args) = args;

exception THEORY of string * theory list;

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

val _ = ML_system_pp (fn _ => fn _ => Pretty.to_ML o pretty_thy);

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
  fold (identity_of #> (fn {id, ids, ...} => fn acc => Bitset.merge (acc, ids) |> Bitset.insert id))
    thys Bitset.empty;

val eq_thy_id = op = o apply2 (#id o rep_theory_id);
val eq_thy = op = o apply2 (#id o identity_of);

val proper_subthy_id = apply2 rep_theory_id #> (fn ({id, ...}, {ids, ...}) => Bitset.member ids id);
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

val data_timing = Unsynchronized.ref false;

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

fun data_kinds () =
  Datatab.fold_rev (fn (k, {pos, ...}) => cons (k, pos)) (Synchronized.value kinds) [];

val invoke_pos = #pos o the_kind;
val invoke_empty = #empty o the_kind;

fun invoke_merge kind args =
  if ! data_timing then
    Timing.cond_timeit true ("Theory_Data.merge" ^ Position.here (#pos kind))
      (fn () => #merge kind args)
  else #merge kind args;

fun declare_data pos empty merge =
  let
    val k = data_kind ();
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

fun create_thy state ids name stage ancestry data =
  let
    val theory_id = make_theory_id {id = new_id (), ids = ids, name = name, stage = stage};
    val (token, pos, assign) = theory_token ();
    val identity = {theory_id = theory_id, theory_token = token, theory_token_pos = pos};
  in assign (Thy (state, identity, ancestry, data)) end;


(* primitives *)

val pre_pure_thy =
  let
    val state = make_state ();
    val stage = next_stage state;
  in create_thy state Bitset.empty PureN stage (make_ancestry [] []) Datatab.empty end;

local

fun change_thy finish f thy =
  let
    val {name, stage, ...} = identity_of thy;
    val Thy (state, _, ancestry, data) = thy;
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

fun raw_transfer thy' (ctxt as Prf (_, _, thy, data)) =
  if eq_thy (thy, thy') then ctxt
  else if proper_subthy (thy, thy') then
    let
      val (token', pos', assign) = proof_token ();
      val data' = init_new_data thy' data;
    in assign (Prf (token', pos', thy', data')) end
  else error "Cannot transfer proof context: not a super theory";

structure Proof_Context =
struct
  fun theory_of (Prf (_, _, thy, _)) = thy;
  fun init_global thy =
    let val (token, pos, assign) = proof_token ()
    in assign (Prf (token, pos, thy, init_data thy)) end;
  fun get_global long thy name = init_global (get_theory long thy name);
end;

structure Proof_Data =
struct

fun declare init =
  let
    val k = data_kind ();
    val _ = Synchronized.change kinds (Datatab.update (k, init));
  in k end;

fun get k dest (Prf (_, _, thy, data)) =
  (case Datatab.lookup data k of
    SOME x => x
  | NONE => init_fallback k thy) |> dest;

fun put k make x (Prf (_, _, thy, data)) =
  let
    val (token', pos', assign) = proof_token ();
    val data' = Datatab.update (k, make x) data;
  in assign (Prf (token', pos', thy, data')) end;

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

fun err_join (thy_id1, thy_id2) =
  error ("Cannot join unrelated theory certificates " ^
    display_name thy_id1 ^ " and " ^ display_name thy_id2);

fun join_certificate (cert1, cert2) =
  let val (thy_id1, thy_id2) = apply2 certificate_theory_id (cert1, cert2) in
    if eq_thy_id (thy_id1, thy_id2) then (case cert1 of Certificate _ => cert1 | _ => cert2)
    else if proper_subthy_id (thy_id2, thy_id1) then cert1
    else if proper_subthy_id (thy_id1, thy_id2) then cert2
    else err_join (thy_id1, thy_id2)
  end;

fun join_certificate_theory (thy1, thy2) =
  let val (thy_id1, thy_id2) = apply2 theory_id (thy1, thy2) in
    if subthy_id (thy_id2, thy_id1) then thy1
    else if proper_subthy_id (thy_id1, thy_id2) then thy2
    else err_join (thy_id1, thy_id2)
  end;


(*** generic context ***)

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
