(*  Title:      Pure/global_theory.ML
    Author:     Makarius

Global theory content: stored facts.
*)

signature GLOBAL_THEORY =
sig
  val facts_of: theory -> Facts.T
  val intern_fact: theory -> xstring -> string
  val defined_fact: theory -> string -> bool
  val hide_fact: bool -> string -> theory -> theory
  val begin_recent_proofs: theory -> theory
  val join_recent_proofs: theory -> unit
  val join_proofs: theory -> unit
  val get_fact: Context.generic -> theory -> Facts.ref -> thm list
  val get_thms: theory -> xstring -> thm list
  val get_thm: theory -> xstring -> thm
  val all_thms_of: theory -> (string * thm) list
  val map_facts: ('a -> 'b) -> ('c * ('a list * 'd) list) list -> ('c * ('b list * 'd) list) list
  val burrow_fact: ('a list -> 'b list) -> ('a list * 'c) list -> ('b list * 'c) list
  val burrow_facts: ('a list -> 'b list) ->
    ('c * ('a list * 'd) list) list -> ('c * ('b list * 'd) list) list
  val name_multi: string -> 'a list -> (string * 'a) list
  val name_thm: bool -> bool -> string -> thm -> thm
  val name_thms: bool -> bool -> string -> thm list -> thm list
  val name_thmss: bool -> string -> (thm list * 'a) list -> (thm list * 'a) list
  val store_thms: binding * thm list -> theory -> thm list * theory
  val store_thm: binding * thm -> theory -> thm * theory
  val store_thm_open: binding * thm -> theory -> thm * theory
  val add_thms: ((binding * thm) * attribute list) list -> theory -> thm list * theory
  val add_thm: (binding * thm) * attribute list -> theory -> thm * theory
  val add_thmss: ((binding * thm list) * attribute list) list -> theory -> thm list list * theory
  val add_thms_dynamic: binding * (Context.generic -> thm list) -> theory -> theory
  val note_thmss: string -> (Thm.binding * (thm list * attribute list) list) list
    -> theory -> (string * thm list) list * theory
  val add_defs: bool -> ((binding * term) * attribute list) list ->
    theory -> thm list * theory
  val add_defs_unchecked: bool -> ((binding * term) * attribute list) list ->
    theory -> thm list * theory
  val add_defs_cmd: bool -> ((binding * string) * attribute list) list ->
    theory -> thm list * theory
  val add_defs_unchecked_cmd: bool -> ((binding * string) * attribute list) list ->
    theory -> thm list * theory
end;

structure Global_Theory: GLOBAL_THEORY =
struct

(** theory data **)

type proofs = thm list * unit lazy;

val empty_proofs: proofs = ([], Lazy.value ());

fun add_proofs more_thms ((thms, _): proofs) =
  let val thms' = fold cons more_thms thms
  in (thms', Lazy.lazy (fn () => Thm.join_proofs (rev thms'))) end;

fun force_proofs ((_, prfs): proofs) = Lazy.force prfs;

structure Data = Theory_Data
(
  type T = Facts.T * (proofs * proofs);
  val empty = (Facts.empty, (empty_proofs, empty_proofs));
  fun extend (facts, _) = (facts, snd empty);
  fun merge ((facts1, _), (facts2, _)) = (Facts.merge (facts1, facts2), snd empty);
);


(* facts *)

val facts_of = #1 o Data.get;

val intern_fact = Facts.intern o facts_of;
val defined_fact = Facts.defined o facts_of;

fun hide_fact fully name = Data.map (apfst (Facts.hide fully name));


(* forked proofs *)

fun register_proofs (thy, thms) = (Data.map (apsnd (pairself (add_proofs thms))) thy, thms);

val begin_recent_proofs = Data.map (apsnd (apfst (K empty_proofs)));
val join_recent_proofs = force_proofs o #1 o #2 o Data.get;
val join_proofs = force_proofs o #2 o #2 o Data.get;


(** retrieve theorems **)

fun get_fact context thy xthmref =
  let
    val ctxt = Context.proof_of context;

    val facts = facts_of thy;
    val xname = Facts.name_of_ref xthmref;
    val pos = Facts.pos_of_ref xthmref;

    val name =
      (case intern_fact thy xname of
        "_" => "Pure.asm_rl"
      | name => name);
    val res = Facts.lookup context facts name;
    val _ = Theory.check_thy thy;
  in
    (case res of
      NONE => error ("Unknown fact " ^ quote name ^ Position.str_of pos)
    | SOME (static, ths) =>
        (Context_Position.report ctxt pos (Name_Space.markup (Facts.space_of facts) name);
         if static then ()
         else Context_Position.report ctxt pos (Isabelle_Markup.dynamic_fact name);
         Facts.select xthmref (map (Thm.transfer thy) ths)))
  end;

fun get_thms thy = get_fact (Context.Theory thy) thy o Facts.named;
fun get_thm thy name = Facts.the_single name (get_thms thy name);

fun all_thms_of thy =
  Facts.fold_static (fn (_, ths) => append (map (`(Thm.get_name_hint)) ths)) (facts_of thy) [];



(** store theorems **)

(* fact specifications *)

fun map_facts f = map (apsnd (map (apfst (map f))));
fun burrow_fact f = split_list #>> burrow f #> op ~~;
fun burrow_facts f = split_list ##> burrow (burrow_fact f) #> op ~~;


(* naming *)

fun name_multi name [x] = [(name, x)]
  | name_multi "" xs = map (pair "") xs
  | name_multi name xs = map_index (fn (i, x) => (name ^ "_" ^ string_of_int (i + 1), x)) xs;

fun name_thm pre official name thm = thm
  |> (if not official orelse pre andalso Thm.derivation_name thm <> "" then I
      else Thm.name_derivation name)
  |> (if name = "" orelse pre andalso Thm.has_name_hint thm then I
      else Thm.put_name_hint name);

fun name_thms pre official name xs =
  map (uncurry (name_thm pre official)) (name_multi name xs);

fun name_thmss official name fact =
  burrow_fact (name_thms true official name) fact;


(* enter_thms *)

fun enter_thms pre_name post_name app_att (b, thms) thy =
  if Binding.is_empty b
  then swap (register_proofs (app_att (thy, thms)))
  else
    let
      val naming = Sign.naming_of thy;
      val name = Name_Space.full_name naming b;
      val (thy', thms') =
        register_proofs (apsnd (post_name name) (app_att (thy, pre_name name thms)));
      val thms'' = map (Thm.transfer thy') thms';
      val thy'' = thy'
        |> (Data.map o apfst)
            (Facts.add_global (Proof_Context.init_global thy') naming (b, thms'') #> snd);
    in (thms'', thy'') end;


(* store_thm(s) *)

fun store_thms (b, thms) =
  enter_thms (name_thms true true) (name_thms false true) I (b, thms);

fun store_thm (b, th) = store_thms (b, [th]) #>> the_single;

fun store_thm_open (b, th) =
  enter_thms (name_thms true false) (name_thms false false) I (b, [th]) #>> the_single;


(* add_thms(s) *)

fun add_thms_atts pre_name ((b, thms), atts) =
  enter_thms pre_name (name_thms false true)
    (Library.foldl_map (Thm.theory_attributes atts)) (b, thms);

fun gen_add_thmss pre_name =
  fold_map (add_thms_atts pre_name);

fun gen_add_thms pre_name args =
  apfst (map hd) o gen_add_thmss pre_name (map (apfst (apsnd single)) args);

val add_thmss = gen_add_thmss (name_thms true true);
val add_thms = gen_add_thms (name_thms true true);
val add_thm = yield_singleton add_thms;


(* add_thms_dynamic *)

fun add_thms_dynamic (b, f) thy = thy
  |> (Data.map o apfst)
      (Facts.add_dynamic (Proof_Context.init_global thy) (Sign.naming_of thy) (b, f) #> snd);


(* note_thmss *)

fun note_thmss kind = fold_map (fn ((b, more_atts), ths_atts) => fn thy =>
  let
    val name = Sign.full_name thy b;
    fun app (x, (ths, atts)) = Library.foldl_map (Thm.theory_attributes atts) (x, ths);
    val (thms, thy') = thy |> enter_thms
      (name_thmss true) (name_thms false true) (apsnd flat o Library.foldl_map app)
      (b, map (fn (ths, atts) => (ths, surround (Thm.kind kind) (atts @ more_atts))) ths_atts);
  in ((name, thms), thy') end);


(* store axioms as theorems *)

local

fun no_read _ (_, t) = t;

fun read ctxt (b, str) =
  Syntax.read_prop ctxt str handle ERROR msg =>
    cat_error msg ("The error(s) above occurred in definition " ^ Binding.print b);

fun add prep unchecked overloaded = fold_map (fn ((b, raw_prop), atts) => fn thy =>
  let
    val ctxt = Syntax.init_pretty_global thy;
    val prop = prep ctxt (b, raw_prop);
    val ((_, def), thy') = Thm.add_def ctxt unchecked overloaded (b, prop) thy;
    val thm = def
      |> Thm.forall_intr_frees
      |> Thm.forall_elim_vars 0
      |> Thm.varifyT_global;
  in yield_singleton (gen_add_thms (K I)) ((b, thm), atts) thy' end);

in

val add_defs = add no_read false;
val add_defs_unchecked = add no_read true;
val add_defs_cmd = add read false;
val add_defs_unchecked_cmd = add read true;

end;

end;
