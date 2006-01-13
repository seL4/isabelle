(*  Title:      Pure/context.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Generic theory contexts with unique identity, arbitrarily typed data,
development graph and history support.  Implicit theory contexts in ML.
Generic proof contexts with arbitrarily typed data.
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
  val theory_name: theory -> string
  val parents_of: theory -> theory list
  val ancestors_of: theory -> theory list
  val is_stale: theory -> bool
  val ProtoPureN: string
  val PureN: string
  val CPureN: string
  val draftN: string
  val exists_name: string -> theory -> bool
  val names_of: theory -> string list
  val pretty_thy: theory -> Pretty.T
  val string_of_thy: theory -> string
  val pprint_thy: theory -> pprint_args -> unit
  val pretty_abbrev_thy: theory -> Pretty.T
  val str_of_thy: theory -> string
  val check_thy: theory -> theory
  val eq_thy: theory * theory -> bool
  val subthy: theory * theory -> bool
  val joinable: theory * theory -> bool
  val merge: theory * theory -> theory                     (*exception TERM*)
  val merge_refs: theory_ref * theory_ref -> theory_ref    (*exception TERM*)
  val self_ref: theory -> theory_ref
  val deref: theory_ref -> theory
  val copy_thy: theory -> theory
  val checkpoint_thy: theory -> theory
  val finish_thy: theory -> theory
  val theory_data_of: theory -> string list
  val pre_pure_thy: theory
  val begin_thy: (theory -> Pretty.pp) -> string -> theory list -> theory
  (*ML theory context*)
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
  (*proof context*)
  type proof
  exception PROOF of string * proof
  val theory_of_proof: proof -> theory
  val transfer_proof: theory -> proof -> proof
  val init_proof: theory -> proof
  val proof_data_of: theory -> string list
  (*generic context*)
  datatype generic = Theory of theory | Proof of proof
  val cases: (theory -> 'a) -> (proof -> 'a) -> generic -> 'a
  val the_theory: generic -> theory
  val the_proof: generic -> proof
  val map_theory: (generic -> generic) -> theory -> theory
  val map_proof: (generic -> generic) -> proof -> proof
  val theory_of: generic -> theory   (*total*)
  val proof_of: generic -> proof     (*total*)
end;

signature PRIVATE_CONTEXT =
sig
  include CONTEXT
  structure TheoryData:
  sig
    val declare: string -> Object.T -> (Object.T -> Object.T) -> (Object.T -> Object.T) ->
      (Pretty.pp -> Object.T * Object.T -> Object.T) -> serial
    val init: serial -> theory -> theory
    val get: serial -> (Object.T -> 'a) -> theory -> 'a
    val put: serial -> ('a -> Object.T) -> 'a -> theory -> theory
  end
  structure ProofData:
  sig
    val declare: string -> (theory -> Object.T) -> serial
    val init: serial -> theory -> theory
    val get: serial -> (Object.T -> 'a) -> proof -> 'a
    val put: serial -> ('a -> Object.T) -> 'a -> proof -> proof
  end
end;

structure Context: PRIVATE_CONTEXT =
struct

(*** theory context ***)

(** theory data **)

(* data kinds and access methods *)

local

type kind =
 {name: string,
  empty: Object.T,
  copy: Object.T -> Object.T,
  extend: Object.T -> Object.T,
  merge: Pretty.pp -> Object.T * Object.T -> Object.T};

val kinds = ref (Inttab.empty: kind Inttab.table);

fun invoke meth_name meth_fn k =
  (case Inttab.lookup (! kinds) k of
    SOME kind => meth_fn kind |> transform_failure (fn exn =>
      EXCEPTION (exn, "Theory data method " ^ #name kind ^ "." ^ meth_name ^ " failed"))
  | NONE => sys_error ("Invalid theory data identifier " ^ string_of_int k));

in

fun invoke_name k    = invoke "name" (K o #name) k ();
fun invoke_empty k   = invoke "empty" (K o #empty) k ();
val invoke_copy      = invoke "copy" #copy;
val invoke_extend    = invoke "extend" #extend;
fun invoke_merge pp  = invoke "merge" (fn kind => #merge kind pp);

fun declare_theory_data name empty copy extend merge =
  let
    val k = serial ();
    val kind = {name = name, empty = empty, copy = copy, extend = extend, merge = merge};
    val _ = conditional (Inttab.exists (equal name o #name o #2) (! kinds)) (fn () =>
      warning ("Duplicate declaration of theory data " ^ quote name));
    val _ = change kinds (Inttab.update (k, kind));
  in k end;

val copy_data = Inttab.map' invoke_copy;
val extend_data = Inttab.map' invoke_extend;
fun merge_data pp = Inttab.join (SOME oo invoke_merge pp) o pairself extend_data;

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
   {theory: Object.T Inttab.table,      (*theory data record*)
    proof: unit Inttab.table} *         (*proof data kinds*)
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
fun make_data theory proof = {theory = theory, proof = proof};
fun make_ancestry parents ancestors = {parents = parents, ancestors = ancestors};
fun make_history name vers ints = {name = name, version = vers, intermediates = ints};

fun map_theory f {theory, proof} = make_data (f theory) proof;
fun map_proof f {theory, proof} = make_data theory (f proof);

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

val ProtoPureN = "ProtoPure";
val PureN = "Pure";
val CPureN = "CPure";

val draftN = "#";
fun draft_id (_, name) = (name = draftN);
val is_draft = draft_id o #id o identity_of;

fun exists_name name (Theory ({id, ids, iids, ...}, _, _, _)) =
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


(* consistency *)    (*exception TERM*)

fun check_thy thy =
  if is_stale thy then
    raise TERM ("Stale theory encountered:\n" ^ string_of_thy thy, [])
  else thy;

fun check_ins id ids =
  if draft_id id orelse Inttab.defined ids (#1 id) then ids
  else if Inttab.exists (equal (#2 id) o #2) ids then
    raise TERM ("Different versions of theory component " ^ quote (#2 id), [])
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

val eq_thy = eq_id o pairself (#id o identity_of o check_thy);

fun proper_subthy
    (Theory ({id = (i, _), ...}, _, _, _), Theory ({ids, iids, ...}, _, _, _)) =
  Inttab.defined ids i orelse Inttab.defined iids i;

fun subthy thys = eq_thy thys orelse proper_subthy thys;

fun joinable (thy1, thy2) = subthy (thy1, thy2) orelse subthy (thy2, thy1);


(* theory references *)

(*theory_ref provides a safe way to store dynamic references to a
  theory in external data structures -- a plain theory value would
  become stale as the self reference moves on*)

datatype theory_ref = TheoryRef of theory ref;

val self_ref = TheoryRef o the_self o check_thy;
fun deref (TheoryRef (ref thy)) = thy;


(* trivial merge *)    (*exception TERM*)

fun merge (thy1, thy2) =
  if eq_thy (thy1, thy2) then thy1
  else if proper_subthy (thy2, thy1) then thy1
  else if proper_subthy (thy1, thy2) then thy2
  else (check_merge thy1 thy2;
    raise TERM (cat_lines ["Attempt to perform non-trivial merge of theories:",
      str_of_thy thy1, str_of_thy thy2], []));

fun merge_refs (ref1, ref2) =
  if ref1 = ref2 then ref1
  else self_ref (merge (deref ref1, deref ref2));



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

fun change_thy name f (thy as Theory ({self, id, ids, iids}, data, ancestry, history)) =
  let
    val _ = check_thy thy;
    val (self', data', ancestry') =
      if is_draft thy then (self, data, ancestry)    (*destructive change!*)
      else if #version history > 0
      then (NONE, map_theory copy_data data, ancestry)
      else (NONE, map_theory extend_data data, make_ancestry [thy] (thy :: #ancestors ancestry));
    val data'' = f data';
  in create_thy name self' id ids iids data'' ancestry' history end;

fun name_thy name = change_thy name I;
val modify_thy = change_thy draftN;
val extend_thy = modify_thy I;

fun copy_thy (thy as Theory ({id, ids, iids, ...}, data, ancestry, history)) =
  (check_thy thy;
    create_thy draftN NONE id ids iids (map_theory copy_data data) ancestry history);

val pre_pure_thy = create_thy draftN NONE (serial (), draftN) Inttab.empty Inttab.empty
  (make_data Inttab.empty Inttab.empty) (make_ancestry [] []) (make_history ProtoPureN 0 []);


(* named theory nodes *)

fun merge_thys pp (thy1, thy2) =
  if exists_name CPureN thy1 <> exists_name CPureN thy2 then
    error "Cannot merge Pure and CPure developments"
  else
    let
      val (ids, iids) = check_merge thy1 thy2;
      val data1 = data_of thy1 and data2 = data_of thy2;
      val data = make_data
        (merge_data (pp thy1) (#theory data1, #theory data2))
        (Inttab.merge (K true) (#proof data1, #proof data2));
      val ancestry = make_ancestry [] [];
      val history = make_history "" 0 [];
    in create_thy draftN NONE (serial (), draftN) ids iids data ancestry history end;

fun maximal_thys thys =
  thys |> filter (fn thy => not (exists (fn thy' => proper_subthy (thy, thy')) thys));

fun begin_thy pp name imports =
  if name = draftN then error ("Illegal theory name: " ^ quote draftN)
  else
    let
      val parents =
        maximal_thys (gen_distinct eq_thy (map check_thy imports));
      val ancestors = gen_distinct eq_thy (parents @ List.concat (map ancestors_of parents));
      val Theory ({id, ids, iids, ...}, data, _, _) =
        (case parents of
          [] => error "No parent theories"
        | [thy] => extend_thy thy
        | thy :: thys => Library.foldl (merge_thys pp) (thy, thys));
      val ancestry = make_ancestry parents ancestors;
      val history = make_history name 0 [];
    in create_thy draftN NONE id ids iids data ancestry history end;


(* undoable checkpoints *)

fun checkpoint_thy thy =
  if not (is_draft thy) then thy
  else
    let
      val {name, version, intermediates} = history_of thy;
      val thy' as Theory (identity', data', ancestry', _) =
        name_thy (name ^ ":" ^ string_of_int version) thy;
      val history' = make_history name (version + 1) (thy' :: intermediates);
    in vitalize (Theory (identity', data', ancestry', history')) end;

fun finish_thy thy =
  let
    val {name, version, intermediates} = history_of thy;
    val rs = map (the_self o check_thy) intermediates;
    val thy' as Theory ({self, id, ids, ...}, data', ancestry', _) = name_thy name thy;
    val identity' = make_identity self id ids Inttab.empty;
    val history' = make_history name 0 [];
    val thy'' = vitalize (Theory (identity', data', ancestry', history'));
    val _ = List.app (fn r => r := thy'') rs;
  in thy'' end;


(* theory data *)

fun dest_data name_of tab =
  map name_of (Inttab.keys tab)
  |> map (rpair ()) |> Symtab.make_multi |> Symtab.dest
  |> map (apsnd length)
  |> map (fn (name, 1) => name | (name, n) => name ^ enclose "[" "]" (string_of_int n));

val theory_data_of = dest_data invoke_name o #theory o data_of;

structure TheoryData =
struct

val declare = declare_theory_data;

fun get k dest thy =
  (case Inttab.lookup (#theory (data_of thy)) k of
    SOME x => (dest x handle Match =>
      error ("Failed to access theory data " ^ quote (invoke_name k)))
  | NONE => error ("Uninitialized theory data " ^ quote (invoke_name k)));

fun put k mk x = modify_thy (map_theory (Inttab.update (k, mk x)));
fun init k = put k I (invoke_empty k);

end;



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

fun use_output verbose txt = use_text ml_output verbose (Symbol.escape txt);

fun use_mltext txt verbose opt_thy = setmp opt_thy (fn () => use_output verbose txt) ();
fun use_mltext_theory txt verbose thy = #2 (pass_theory thy (use_output verbose) txt);

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



(*** proof context ***)

(* datatype proof *)

datatype proof = Proof of theory_ref * Object.T Inttab.table;

exception PROOF of string * proof;

fun theory_of_proof (Proof (thy_ref, _)) = deref thy_ref;
fun data_of_proof (Proof (_, data)) = data;
fun map_prf f (Proof (thy_ref, data)) = Proof (thy_ref, f data);

fun transfer_proof thy' (prf as Proof (thy_ref, data)) =
  if not (subthy (deref thy_ref, thy')) then
    raise PROOF ("transfer proof context: no a super theory", prf)
  else Proof (self_ref thy', data);


(* proof data kinds *)

local

type kind =
 {name: string,
  init: theory -> Object.T};

val kinds = ref (Inttab.empty: kind Inttab.table);

fun invoke meth_name meth_fn k =
  (case Inttab.lookup (! kinds) k of
    SOME kind => meth_fn kind |> transform_failure (fn exn =>
      EXCEPTION (exn, "Proof data method " ^ #name kind ^ "." ^ meth_name ^ " failed"))
  | NONE => sys_error ("Invalid proof data identifier " ^ string_of_int k));

fun invoke_name k = invoke "name" (K o #name) k ();
val invoke_init   = invoke "init" #init;

in

val proof_data_of = dest_data invoke_name o #proof o data_of;

fun init_proof thy =
  Proof (self_ref thy, Inttab.map' (fn k => fn _ => invoke_init k thy) (#proof (data_of thy)));

structure ProofData =
struct

fun declare name init =
  let
    val k = serial ();
    val kind = {name = name, init = init};
    val _ = conditional (Inttab.exists (equal name o #name o #2) (! kinds)) (fn () =>
      warning ("Duplicate declaration of proof data " ^ quote name));
    val _ = change kinds (Inttab.update (k, kind));
  in k end;

fun init k = modify_thy (map_proof (Inttab.update (k, ())));

fun get k dest prf =
  (case Inttab.lookup (data_of_proof prf) k of
    SOME x => (dest x handle Match =>
      error ("Failed to access proof data " ^ quote (invoke_name k)))
  | NONE => error ("Uninitialized proof data " ^ quote (invoke_name k)));

fun put k mk x = map_prf (Inttab.update (k, mk x));

end;

end;



(*** generic context ***)

datatype generic = Theory of theory | Proof of proof;

fun cases f _ (Theory thy) = f thy
  | cases _ g (Proof prf) = g prf;

val the_theory = cases I (fn _ => raise Fail "Bad generic context: theory expected");
val the_proof = cases (fn _ => raise Fail "Bad generic context: proof context expected") I;

fun map_theory f = the_theory o f o Theory;
fun map_proof f = the_proof o f o Proof;

val theory_of = cases I theory_of_proof;
val proof_of = cases init_proof I;

end;

structure BasicContext: BASIC_CONTEXT = Context;
open BasicContext;



(*** type-safe interfaces for data declarations ***)

(** theory data **)

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
  val get_sg: theory -> T    (*obsolete*)
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
  (fn pp => fn (Data x1, Data x2) => Data (Data.merge pp (x1, x2)));

val init = TheoryData.init kind;
val get = TheoryData.get kind (fn Data x => x);
val get_sg = get;
fun print thy = Data.print thy (get thy);
val put = TheoryData.put kind Data;
fun map f thy = put (f (get thy)) thy;

end;



(** proof data **)

signature PROOF_DATA_ARGS =
sig
  val name: string
  type T
  val init: theory -> T
  val print: Context.proof -> T -> unit
end;

signature PROOF_DATA =
sig
  type T
  val init: theory -> theory
  val print: Context.proof -> unit
  val get: Context.proof -> T
  val put: T -> Context.proof -> Context.proof
  val map: (T -> T) -> Context.proof -> Context.proof
end;

functor ProofDataFun(Data: PROOF_DATA_ARGS): PROOF_DATA =
struct

structure ProofData = Context.ProofData;

type T = Data.T;
exception Data of T;

val kind = ProofData.declare Data.name (Data o Data.init);

val init = ProofData.init kind;
val get = ProofData.get kind (fn Data x => x);
fun print prf = Data.print prf (get prf);
val put = ProofData.put kind Data;
fun map f prf = put (f (get prf)) prf;

end;



(** generic data **)

signature GENERIC_DATA_ARGS =
sig
  val name: string
  type T
  val empty: T
  val extend: T -> T
  val merge: Pretty.pp -> T * T -> T
  val print: Context.generic -> T -> unit
end;

signature GENERIC_DATA =
sig
  type T
  val init: theory -> theory
  val get: Context.generic -> T
  val put: T -> Context.generic -> Context.generic
  val map: (T -> T) -> Context.generic -> Context.generic
  val print: Context.generic -> unit
end;

functor GenericDataFun(Data: GENERIC_DATA_ARGS): GENERIC_DATA =
struct

structure ThyData = TheoryDataFun(open Data val copy = I fun print _ _ = ());
structure PrfData =
  ProofDataFun(val name = Data.name type T = Data.T val init = ThyData.get fun print _ _ = ());

type T = Data.T;
val init = ThyData.init #> PrfData.init;

fun get (Context.Theory thy) = ThyData.get thy
  | get (Context.Proof prf) = PrfData.get prf;

fun put x (Context.Theory thy) = Context.Theory (ThyData.put x thy)
  | put x (Context.Proof prf) = Context.Proof (PrfData.put x prf);

fun map f ctxt = put (f (get ctxt)) ctxt;

fun print ctxt = Data.print ctxt (get ctxt);

end;


(*hide private interface*)
structure Context: CONTEXT = Context;
