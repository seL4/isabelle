(*  Title:      Pure/context.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Generic theory contexts with unique identity, arbitrarily typed data,
monotonic development graph and history support.  Generic proof
contexts with arbitrarily typed data.
*)

signature BASIC_CONTEXT =
sig
  type theory
  type theory_ref
  exception THEORY of string * theory list
end;

signature CONTEXT =
sig
  include BASIC_CONTEXT
  (*theory context*)
  val theory_name: theory -> string
  val parents_of: theory -> theory list
  val ancestors_of: theory -> theory list
  val is_stale: theory -> bool
  val PureN: string
  val CPureN: string
  val is_draft: theory -> bool
  val exists_name: string -> theory -> bool
  val names_of: theory -> string list
  val pretty_thy: theory -> Pretty.T
  val string_of_thy: theory -> string
  val pprint_thy: theory -> pprint_args -> unit
  val pretty_abbrev_thy: theory -> Pretty.T
  val str_of_thy: theory -> string
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
  val begin_thy: (theory -> Pretty.pp) -> string -> theory list -> theory
  (*proof context*)
  type proof
  val theory_of_proof: proof -> theory
  val transfer_proof: theory -> proof -> proof
  val init_proof: theory -> proof
  (*generic context*)
  datatype generic = Theory of theory | Proof of proof
  val cases: (theory -> 'a) -> (proof -> 'a) -> generic -> 'a
  val mapping: (theory -> theory) -> (proof -> proof) -> generic -> generic
  val mapping_result: (theory -> 'a * theory) -> (proof -> 'a * proof) -> generic -> 'a * generic
  val the_theory: generic -> theory
  val the_proof: generic -> proof
  val map_theory: (theory -> theory) -> generic -> generic
  val map_proof: (proof -> proof) -> generic -> generic
  val map_theory_result: (theory -> 'a * theory) -> generic -> 'a * generic
  val map_proof_result: (proof -> 'a * proof) -> generic -> 'a * generic
  val theory_map: (generic -> generic) -> theory -> theory
  val proof_map: (generic -> generic) -> proof -> proof
  val theory_of: generic -> theory   (*total*)
  val proof_of: generic -> proof     (*total*)
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
  structure TheoryData:
  sig
    val declare: Object.T -> (Object.T -> Object.T) -> (Object.T -> Object.T) ->
      (Pretty.pp -> Object.T * Object.T -> Object.T) -> serial
    val get: serial -> (Object.T -> 'a) -> theory -> 'a
    val put: serial -> ('a -> Object.T) -> 'a -> theory -> theory
  end
  structure ProofData:
  sig
    val declare: (theory -> Object.T) -> serial
    val get: serial -> (Object.T -> 'a) -> proof -> 'a
    val put: serial -> ('a -> Object.T) -> 'a -> proof -> proof
  end
end;

structure Context: PRIVATE_CONTEXT =
struct

(*** theory context ***)

(** theory data **)

(* data kinds and access methods *)

(*private copy avoids potential conflict of table exceptions*)
structure Datatab = TableFun(type key = int val ord = int_ord);

local

type kind =
 {empty: Object.T,
  copy: Object.T -> Object.T,
  extend: Object.T -> Object.T,
  merge: Pretty.pp -> Object.T * Object.T -> Object.T};

val kinds = ref (Datatab.empty: kind Datatab.table);

fun invoke f k =
  (case Datatab.lookup (! kinds) k of
    SOME kind => f kind
  | NONE => sys_error "Invalid theory data identifier");

in

fun invoke_empty k   = invoke (K o #empty) k ();
val invoke_copy      = invoke #copy;
val invoke_extend    = invoke #extend;
fun invoke_merge pp  = invoke (fn kind => #merge kind pp);

fun declare_theory_data empty copy extend merge =
  let
    val k = serial ();
    val kind = {empty = empty, copy = copy, extend = extend, merge = merge};
    val _ = CRITICAL (fn () => change kinds (Datatab.update (k, kind)));
  in k end;

val copy_data = Datatab.map' invoke_copy;
val extend_data = Datatab.map' invoke_extend;
fun merge_data pp = Datatab.join (invoke_merge pp) o pairself extend_data;

end;



(** datatype theory **)

datatype theory =
  Theory of
   (*identity*)
   {self: theory ref option,            (*dynamic self reference -- follows theory changes*)
    id: serial * string,                (*identifier of this theory*)
    ids: string Inttab.table,           (*identifiers of ancestors*)
    iids: string Inttab.table} *        (*identifiers of intermediate checkpoints*)
   (*data*)
   Object.T Datatab.table *
   (*ancestry*)
   {parents: theory list,               (*immediate predecessors*)
    ancestors: theory list} *           (*all predecessors*)
   (*history*)
   {name: string,                       (*prospective name of finished theory*)
    version: int,                       (*checkpoint counter*)
    intermediates: theory list};        (*intermediate checkpoints*)

exception THEORY of string * theory list;

fun rep_theory (Theory args) = args;

val identity_of = #1 o rep_theory;
val data_of     = #2 o rep_theory;
val ancestry_of = #3 o rep_theory;
val history_of  = #4 o rep_theory;

fun make_identity self id ids iids = {self = self, id = id, ids = ids, iids = iids};
fun make_ancestry parents ancestors = {parents = parents, ancestors = ancestors};
fun make_history name vers ints = {name = name, version = vers, intermediates = ints};

val the_self = the o #self o identity_of;
val parents_of = #parents o ancestry_of;
val ancestors_of = #ancestors o ancestry_of;
val theory_name = #name o history_of;


(* staleness *)

fun eq_id ((i: int, _), (j, _)) = (i = j);

fun is_stale
    (Theory ({self = SOME (ref (Theory ({id = id', ...}, _, _, _))), id, ...}, _, _, _)) =
      not (eq_id (id, id'))
  | is_stale (Theory ({self = NONE, ...}, _, _, _)) = true;

fun vitalize (thy as Theory ({self = SOME r, ...}, _, _, _)) = (r := thy; thy)
  | vitalize (thy as Theory ({self = NONE, id, ids, iids}, data, ancestry, history)) =
      let
        val r = ref thy;
        val thy' = Theory (make_identity (SOME r) id ids iids, data, ancestry, history);
      in r := thy'; thy' end;


(* names *)

val PureN = "Pure";
val CPureN = "CPure";

val draftN = "#";
fun draft_id (_, name) = (name = draftN);
val is_draft = draft_id o #id o identity_of;

fun exists_name name (thy as Theory ({id, ids, iids, ...}, _, _, _)) =
  name = theory_name thy orelse
  name = #2 id orelse
  Inttab.exists (equal name o #2) ids orelse
  Inttab.exists (equal name o #2) iids;

fun names_of (Theory ({id, ids, iids, ...}, _, _, _)) =
  rev (#2 id :: Inttab.fold (cons o #2) iids (Inttab.fold (cons o #2) ids []));

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


(* theory references *)

(*theory_ref provides a safe way to store dynamic references to a
  theory in external data structures -- a plain theory value would
  become stale as the self reference moves on*)

datatype theory_ref = TheoryRef of theory ref;

fun deref (TheoryRef (ref thy)) = thy;

fun check_thy thy =  (*thread-safe version*)
  let val thy_ref = TheoryRef (the_self thy) in
    if is_stale thy then error ("Stale theory encountered:\n" ^ string_of_thy thy)
    else thy_ref
  end;


(* consistency *)

fun check_ins id ids =
  if draft_id id orelse Inttab.defined ids (#1 id) then ids
  else if Inttab.exists (equal (#2 id) o #2) ids then
    error ("Different versions of theory component " ^ quote (#2 id))
  else Inttab.update id ids;

fun check_insert intermediate id (ids, iids) =
  let val ids' = check_ins id ids and iids' = check_ins id iids
  in if intermediate then (ids, iids') else (ids', iids) end;

fun check_merge
    (Theory ({id = id1, ids = ids1, iids = iids1, ...}, _, _, history1))
    (Theory ({id = id2, ids = ids2, iids = iids2, ...}, _, _, history2)) =
  (Inttab.fold check_ins ids2 ids1, Inttab.fold check_ins iids2 iids1)
  |> check_insert (#version history1 > 0) id1
  |> check_insert (#version history2 > 0) id2;


(* equality and inclusion *)

val eq_thy = eq_id o pairself (#id o identity_of);

fun proper_subthy
    (Theory ({id = (i, _), ...}, _, _, _), Theory ({ids, iids, ...}, _, _, _)) =
  Inttab.defined ids i orelse Inttab.defined iids i;

fun subthy thys = eq_thy thys orelse proper_subthy thys;

fun joinable (thy1, thy2) = subthy (thy1, thy2) orelse subthy (thy2, thy1);


(* trivial merge *)

fun merge (thy1, thy2) =
  if eq_thy (thy1, thy2) then thy1
  else if proper_subthy (thy2, thy1) then thy1
  else if proper_subthy (thy1, thy2) then thy2
  else (check_merge thy1 thy2;
    error (cat_lines ["Attempt to perform non-trivial merge of theories:",
      str_of_thy thy1, str_of_thy thy2]));

fun merge_refs (ref1, ref2) =
  if ref1 = ref2 then ref1
  else check_thy (merge (deref ref1, deref ref2));



(** build theories **)

(* primitives *)

fun create_thy name self id ids iids data ancestry history =
  let
    val {version, name = _, intermediates = _} = history;
    val intermediate = version > 0;
    val (ids', iids') = check_insert intermediate id (ids, iids);
    val id' = (serial (), name);
    val _ = check_insert intermediate id' (ids', iids');
    val identity' = make_identity self id' ids' iids';
  in vitalize (Theory (identity', data, ancestry, history)) end;

fun change_thy name f thy =
  let
    val Theory ({self, id, ids, iids}, data, ancestry, history) = thy;
    val (self', data', ancestry') =
      if is_draft thy then (self, data, ancestry)    (*destructive change!*)
      else if #version history > 0
      then (NONE, copy_data data, ancestry)
      else (NONE, extend_data data, make_ancestry [thy] (thy :: #ancestors ancestry));
    val data'' = f data';
    val thy' = NAMED_CRITICAL "theory" (fn () =>
      (check_thy thy; create_thy name self' id ids iids data'' ancestry' history));
  in thy' end;

fun name_thy name = change_thy name I;
val modify_thy = change_thy draftN;
val extend_thy = modify_thy I;

fun copy_thy thy =
  let
    val Theory ({id, ids, iids, ...}, data, ancestry, history) = thy;
    val data' = copy_data data;
    val thy' = NAMED_CRITICAL "theory" (fn () =>
      (check_thy thy; create_thy draftN NONE id ids iids data' ancestry history));
  in thy' end;

val pre_pure_thy = create_thy draftN NONE (serial (), draftN) Inttab.empty Inttab.empty
  Datatab.empty (make_ancestry [] []) (make_history PureN 0 []);


(* named theory nodes *)

fun merge_thys pp (thy1, thy2) =
  if exists_name CPureN thy1 <> exists_name CPureN thy2 then
    error "Cannot merge Pure and CPure developments"
  else
    let
      val (ids, iids) = check_merge thy1 thy2;
      val data = merge_data (pp thy1) (data_of thy1, data_of thy2);
      val ancestry = make_ancestry [] [];
      val history = make_history "" 0 [];
      val thy' = NAMED_CRITICAL "theory" (fn () =>
       (check_thy thy1; check_thy thy2;
        create_thy draftN NONE (serial (), draftN) ids iids data ancestry history))
    in thy' end;

fun maximal_thys thys =
  thys |> filter (fn thy => not (exists (fn thy' => proper_subthy (thy, thy')) thys));

fun begin_thy pp name imports =
  if name = draftN then error ("Illegal theory name: " ^ quote draftN)
  else
    let
      val parents = maximal_thys (distinct eq_thy imports);
      val ancestors = distinct eq_thy (parents @ maps ancestors_of parents);
      val Theory ({id, ids, iids, ...}, data, _, _) =
        (case parents of
          [] => error "No parent theories"
        | [thy] => extend_thy thy
        | thy :: thys => Library.foldl (merge_thys pp) (thy, thys));
      val ancestry = make_ancestry parents ancestors;
      val history = make_history name 0 [];
      val thy' = NAMED_CRITICAL "theory" (fn () =>
        (map check_thy imports; create_thy draftN NONE id ids iids data ancestry history));
    in thy' end;


(* undoable checkpoints *)

fun checkpoint_thy thy =
  if not (is_draft thy) then thy
  else
    let
      val {name, version, intermediates} = history_of thy;
      val thy' as Theory (identity', data', ancestry', _) =
        name_thy (name ^ ":" ^ string_of_int version) thy;
      val history' = make_history name (version + 1) (thy' :: intermediates);
      val thy'' = NAMED_CRITICAL "theory" (fn () =>
        (check_thy thy'; vitalize (Theory (identity', data', ancestry', history'))));
    in thy'' end;

fun finish_thy thy = NAMED_CRITICAL "theory" (fn () =>
  let
    val {name, version, intermediates} = history_of thy;
    val rs = map ((fn TheoryRef r => r) o check_thy) intermediates;
    val thy' as Theory ({self, id, ids, ...}, data', ancestry', _) = name_thy name thy;
    val identity' = make_identity self id ids Inttab.empty;
    val history' = make_history name 0 [];
    val thy'' = vitalize (Theory (identity', data', ancestry', history'));
    val _ = List.app (fn r => r := thy'') rs;
  in thy'' end);


(* theory data *)

structure TheoryData =
struct

val declare = declare_theory_data;

fun get k dest thy =
  dest ((case Datatab.lookup (data_of thy) k of
    SOME x => x
  | NONE => invoke_copy k (invoke_empty k)));   (*adhoc value*)

fun put k mk x = modify_thy (Datatab.update (k, mk x));

end;



(*** proof context ***)

(* datatype proof *)

datatype proof = Prf of Object.T Datatab.table * theory_ref;

fun theory_of_proof (Prf (_, thy_ref)) = deref thy_ref;
fun data_of_proof (Prf (data, _)) = data;
fun map_prf f (Prf (data, thy_ref)) = Prf (f data, thy_ref);


(* proof data kinds *)

local

val kinds = ref (Datatab.empty: (theory -> Object.T) Datatab.table);

fun invoke_init k =
  (case Datatab.lookup (! kinds) k of
    SOME init => init
  | NONE => sys_error "Invalid proof data identifier");

fun init_data thy =
  Datatab.map' (fn k => fn _ => invoke_init k thy) (! kinds);

fun init_new_data data thy =
  Datatab.merge (K true) (data, init_data thy);

in

fun init_proof thy = Prf (init_data thy, check_thy thy);

fun transfer_proof thy' (prf as Prf (data, thy_ref)) =
  let
    val thy = deref thy_ref;
    val _ = subthy (thy, thy') orelse error "transfer proof context: not a super theory";
    val _ = check_thy thy;
    val data' = init_new_data data thy';
    val thy_ref' = check_thy thy';
  in Prf (data', thy_ref') end;


structure ProofData =
struct

fun declare init =
  let
    val k = serial ();
    val _ = CRITICAL (fn () => change kinds (Datatab.update (k, init)));
  in k end;

fun get k dest prf =
  dest (case Datatab.lookup (data_of_proof prf) k of
    SOME x => x
  | NONE => invoke_init k (theory_of_proof prf));   (*adhoc value*)

fun put k mk x = map_prf (Datatab.update (k, mk x));

end;

end;



(*** generic context ***)

datatype generic = Theory of theory | Proof of proof;

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

val theory_of = cases I theory_of_proof;
val proof_of = cases init_proof I;



(** thread data **)

local val tag = Universal.tag () : generic option Universal.tag in

fun thread_data () =
  (case Multithreading.get_data tag of
    SOME (SOME context) => SOME context
  | _ => NONE);

fun the_thread_data () =
  (case thread_data () of
    SOME context => context
  | _ => error "Unknown context");

fun set_thread_data context = Multithreading.put_data (tag, context);
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

structure BasicContext: BASIC_CONTEXT = Context;
open BasicContext;



(*** type-safe interfaces for data declarations ***)

(** theory data **)

signature THEORY_DATA_ARGS =
sig
  type T
  val empty: T
  val copy: T -> T
  val extend: T -> T
  val merge: Pretty.pp -> T * T -> T
end;

signature THEORY_DATA =
sig
  type T
  val get: theory -> T
  val put: T -> theory -> theory
  val map: (T -> T) -> theory -> theory
  val init: theory -> theory
end;

functor TheoryDataFun(Data: THEORY_DATA_ARGS): THEORY_DATA =
struct

structure TheoryData = Context.TheoryData;

type T = Data.T;
exception Data of T;

val kind = TheoryData.declare
  (Data Data.empty)
  (fn Data x => Data (Data.copy x))
  (fn Data x => Data (Data.extend x))
  (fn pp => fn (Data x1, Data x2) => Data (Data.merge pp (x1, x2)));

val get = TheoryData.get kind (fn Data x => x);
val put = TheoryData.put kind Data;
fun map f thy = put (f (get thy)) thy;

fun init thy = map I thy;

end;



(** proof data **)

signature PROOF_DATA_ARGS =
sig
  type T
  val init: theory -> T
end;

signature PROOF_DATA =
sig
  type T
  val get: Context.proof -> T
  val put: T -> Context.proof -> Context.proof
  val map: (T -> T) -> Context.proof -> Context.proof
end;

functor ProofDataFun(Data: PROOF_DATA_ARGS): PROOF_DATA =
struct

structure ProofData = Context.ProofData;

type T = Data.T;
exception Data of T;

val kind = ProofData.declare (Data o Data.init);

val get = ProofData.get kind (fn Data x => x);
val put = ProofData.put kind Data;
fun map f prf = put (f (get prf)) prf;

end;



(** generic data **)

signature GENERIC_DATA_ARGS =
sig
  type T
  val empty: T
  val extend: T -> T
  val merge: Pretty.pp -> T * T -> T
end;

signature GENERIC_DATA =
sig
  type T
  val get: Context.generic -> T
  val put: T -> Context.generic -> Context.generic
  val map: (T -> T) -> Context.generic -> Context.generic
end;

functor GenericDataFun(Data: GENERIC_DATA_ARGS): GENERIC_DATA =
struct

structure ThyData = TheoryDataFun(open Data val copy = I);
structure PrfData = ProofDataFun(type T = Data.T val init = ThyData.get);

type T = Data.T;

fun get (Context.Theory thy) = ThyData.get thy
  | get (Context.Proof prf) = PrfData.get prf;

fun put x (Context.Theory thy) = Context.Theory (ThyData.put x thy)
  | put x (Context.Proof prf) = Context.Proof (PrfData.put x prf);

fun map f ctxt = put (f (get ctxt)) ctxt;

end;

(*hide private interface*)
structure Context: CONTEXT = Context;

(*fake predeclarations*)
structure Proof = struct type context = Context.proof end;
structure ProofContext =
struct val theory_of = Context.theory_of_proof val init = Context.init_proof end;
