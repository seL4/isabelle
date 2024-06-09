(*  Title:      Pure/global_theory.ML
    Author:     Makarius

Global theory content: stored facts.
*)

signature GLOBAL_THEORY =
sig
  val facts_of: theory -> Facts.T
  val fact_space: theory -> Name_Space.T
  val check_fact: theory -> xstring * Position.T -> string
  val intern_fact: theory -> xstring -> string
  val defined_fact: theory -> string -> bool
  val alias_fact: binding -> string -> theory -> theory
  val hide_fact: bool -> string -> theory -> theory
  val dest_thms: bool -> theory list -> theory -> (Thm_Name.T * thm) list
  val pretty_thm_name: theory -> Thm_Name.T -> Pretty.T
  val print_thm_name: theory -> Thm_Name.T -> string
  val get_thm_names: theory -> Thm_Name.T Inttab.table
  val dest_thm_names: theory -> (Proofterm.thm_id * Thm_Name.T) list
  val lookup_thm_id: theory -> Proofterm.thm_id -> Thm_Name.T option
  val lookup_thm: theory -> thm -> (Proofterm.thm_id * Thm_Name.T) option
  val get_thms: theory -> xstring -> thm list
  val get_thm: theory -> xstring -> thm
  val transfer_theories: theory -> thm -> thm
  val all_thms_of: theory -> bool -> (Thm_Name.T * thm) list
  val get_thm_name: theory -> Thm_Name.T * Position.T -> thm
  type name_flags
  val unnamed: name_flags
  val official1: name_flags
  val official2: name_flags
  val unofficial1: name_flags
  val unofficial2: name_flags
  val name_thm: name_flags -> Thm_Name.P -> thm -> thm
  val name_thms: name_flags -> string * Position.T -> thm list -> thm list
  val name_facts: name_flags -> string * Position.T -> (thm list * 'a) list -> (thm list * 'a) list
  val check_thms_lazy: thm list lazy -> thm list lazy
  val add_thms_lazy: string -> (binding * thm list lazy) -> theory -> theory
  val store_thm: binding * thm -> theory -> thm * theory
  val store_thm_open: binding * thm -> theory -> thm * theory
  val add_thms: ((binding * thm) * attribute list) list -> theory -> thm list * theory
  val add_thm: (binding * thm) * attribute list -> theory -> thm * theory
  val add_thmss: ((binding * thm list) * attribute list) list -> theory -> thm list list * theory
  val add_thms_dynamic': Context.generic -> binding * (Context.generic -> thm list) ->
    theory -> string * theory
  val add_thms_dynamic: binding * (Context.generic -> thm list) -> theory -> theory
  val note_thms: string -> Thm.binding * (thm list * attribute list) list ->
    theory -> (string * thm list) * theory
  val note_thmss: string -> (Thm.binding * (thm list * attribute list) list) list ->
    theory -> (string * thm list) list * theory
  val note_thmss_foundation: string -> (Thm.binding * (thm list * attribute list) list) list ->
    theory -> (string * thm list) list * theory
  val add_def: binding * term -> theory -> thm * theory
  val add_def_overloaded: binding * term -> theory -> thm * theory
  val add_def_unchecked: binding * term -> theory -> thm * theory
  val add_def_unchecked_overloaded: binding * term -> theory -> thm * theory
end;

structure Global_Theory: GLOBAL_THEORY =
struct

(** theory data **)

structure Data = Theory_Data
(
  type T = Facts.T * Thm_Name.T Inttab.table lazy option;
  val empty: T = (Facts.empty, NONE);
  fun merge ((facts1, _), (facts2, _)) = (Facts.merge (facts1, facts2), NONE);
);


(* global facts *)

val facts_of = #1 o Data.get;
val map_facts = Data.map o apfst;

val fact_space = Facts.space_of o facts_of;
fun check_fact thy = Facts.check (Context.Theory thy) (facts_of thy);
val intern_fact = Facts.intern o facts_of;
val defined_fact = Facts.defined o facts_of;

fun alias_fact binding name thy =
  map_facts (Facts.alias (Sign.naming_of thy) binding name) thy;

fun hide_fact fully name = map_facts (Facts.hide fully name);

fun dest_thms verbose prev_thys thy =
  Facts.dest_static verbose (map facts_of prev_thys) (facts_of thy)
  |> maps (fn (name, thms) => Thm_Name.list (name, Position.none) thms |> map (apfst fst));

fun pretty_thm_name thy = Facts.pretty_thm_name (Context.Theory thy) (facts_of thy);
val print_thm_name = Pretty.string_of oo pretty_thm_name;


(* thm_name vs. derivation_id *)

val thm_names_of = #2 o Data.get;
val map_thm_names = Data.map o apsnd;

fun make_thm_names thy =
  (dest_thms true (Theory.parents_of thy) thy, Inttab.empty)
  |-> fold (fn (thm_name, thm) => fn thm_names =>
    (case Thm.derivation_id (Thm.transfer thy thm) of
      NONE => thm_names
    | SOME {serial, theory_name} =>
        if Context.theory_long_name thy <> theory_name then
          raise THM ("Bad theory name for derivation", 0, [thm])
        else
          (case Inttab.lookup thm_names serial of
            SOME thm_name' =>
              raise THM ("Duplicate use of derivation identity for " ^
                print_thm_name thy thm_name ^ " vs. " ^
                print_thm_name thy thm_name', 0, [thm])
          | NONE => Inttab.update (serial, thm_name) thm_names)));

fun lazy_thm_names thy =
  (case thm_names_of thy of
    NONE => Lazy.lazy (fn () => make_thm_names thy)
  | SOME lazy_tab => lazy_tab);

val get_thm_names = Lazy.force o lazy_thm_names;

fun dest_thm_names thy =
  let
    val theory_name = Context.theory_long_name thy;
    fun thm_id i = Proofterm.make_thm_id (i, theory_name);
  in Inttab.fold_rev (fn (i, thm_name) => cons (thm_id i, thm_name)) (get_thm_names thy) [] end;

fun lookup_thm_id thy =
  let
    val theories =
      Symtab.build (Theory.nodes_of thy |> fold (fn thy' =>
        Symtab.update (Context.theory_long_name thy', lazy_thm_names thy')));
    fun lookup (thm_id: Proofterm.thm_id) =
      (case Symtab.lookup theories (#theory_name thm_id) of
        NONE => NONE
      | SOME lazy_tab => Inttab.lookup (Lazy.force lazy_tab) (#serial thm_id));
  in lookup end;

fun lookup_thm thy =
  let val lookup = lookup_thm_id thy in
    fn thm =>
      (case Thm.derivation_id thm of
        NONE => NONE
      | SOME thm_id =>
          (case lookup thm_id of
            NONE => NONE
          | SOME thm_name => SOME (thm_id, thm_name)))
  end;

val _ =
  Theory.setup
   (Theory.at_begin (fn thy =>
      if is_none (thm_names_of thy) then NONE
      else SOME (map_thm_names (K NONE) thy)) #>
    Theory.at_end (fn thy =>
      if is_some (thm_names_of thy) then NONE
      else
        let
          val lazy_tab =
            if Future.proofs_enabled 1
            then Lazy.lazy (fn () => make_thm_names thy)
            else Lazy.value (make_thm_names thy);
        in SOME (map_thm_names (K (SOME lazy_tab)) thy) end));


(* retrieve theorems *)

fun get_thms thy xname =
  #thms (Facts.retrieve (Context.Theory thy) (facts_of thy) (xname, Position.none));

fun get_thm thy xname =
  Facts.the_single (xname, Position.none) (get_thms thy xname);

fun transfer_theories thy =
  let
    val theories =
      Symtab.build (Theory.nodes_of thy |> fold (fn thy' =>
        Symtab.update (Context.theory_long_name thy', thy')));
    fun transfer th =
      Thm.transfer (the_default thy (Symtab.lookup theories (Thm.theory_long_name th))) th;
  in transfer end;

fun all_thms_of thy verbose =
  let
    val transfer = transfer_theories thy;
    val facts = facts_of thy;
    fun add (name, ths) =
      if not verbose andalso Facts.is_concealed facts name then I
      else append (map (`(Thm.get_name_hint) o transfer) ths);
  in Facts.fold_static add facts [] end;

fun get_thm_name thy ((name, i), pos) =
  let
    val facts = facts_of thy;
    fun print_name () =
      Facts.markup_extern (Proof_Context.init_global thy) facts name |-> Markup.markup;
  in
    (case (Facts.lookup (Context.Theory thy) facts name, i) of
      (NONE, _) => error ("Undefined fact " ^ quote (print_name ()) ^ Position.here pos)
    | (SOME {thms = [thm], ...}, 0) => thm
    | (SOME {thms, ...}, 0) => Facts.err_single (print_name (), pos) thms
    | (SOME {thms, ...}, _) =>
        if i > 0 andalso i <= length thms then nth thms (i - 1)
        else Facts.err_selection (print_name (), pos) i thms)
    |> Thm.transfer thy
  end;



(** store theorems **)

(* register proofs *)

fun check_thms_lazy (thms: thm list lazy) =
  if Proofterm.any_proofs_enabled () orelse Options.default_bool "strict_facts"
  then Lazy.force_value thms else thms;

fun zproof_enabled {zproof} name =
  name <> "" andalso zproof andalso Proofterm.zproof_enabled (Proofterm.get_proofs_level ());

fun store_proof zproof (name, thm) thy =
  if zproof_enabled zproof (#1 (#1 name)) then
    let val (thm', thy') = Thm.store_zproof name thm thy
    in ((name, thm'), thy') end
  else ((name, thm), thy);

fun store_proofs_lazy zproof name thms thy =
  if zproof_enabled zproof (#1 name) then
    fold_map (uncurry Thm.store_zproof) (Thm_Name.list name (Lazy.force thms)) thy
    |>> Lazy.value
  else (check_thms_lazy thms, thy);

fun register_proofs_lazy zproof name thms thy =
  let val (thms', thy') = store_proofs_lazy zproof name thms thy;
  in (thms', Thm.register_proofs thms' thy') end;

fun register_proofs zproof name thms =
  Lazy.value thms |> register_proofs_lazy zproof name #>> Lazy.force;


(* name theorems *)

abstype name_flags = No_Name_Flags | Name_Flags of {post: bool, official: bool}
with

val unnamed = No_Name_Flags;
val official1 = Name_Flags {post = false, official = true};
val official2 = Name_Flags {post = true, official = true};
val unofficial1 = Name_Flags {post = false, official = false};
val unofficial2 = Name_Flags {post = true, official = false};

fun name_thm name_flags (name, pos) =
  Thm.solve_constraints #> (fn thm =>
    (case name_flags of
      No_Name_Flags => thm
    | Name_Flags {post, official} =>
        thm
        |> (official andalso (post orelse Thm_Name.is_empty (Thm.raw_derivation_name thm))) ?
            Thm.name_derivation (name, pos)
        |> (not (Thm_Name.is_empty name) andalso (post orelse not (Thm.has_name_hint thm))) ?
            Thm.put_name_hint name));

end;

fun name_thms name_flags name_pos thms =
  Thm_Name.list name_pos thms |> map (uncurry (name_thm name_flags));

fun name_facts name_flags name_pos facts =
  Thm_Name.expr name_pos facts |> (map o apfst o map) (uncurry (name_thm name_flags));


(* store theorems and proofs *)

fun add_facts (b, fact) thy =
  let
    val check =
      Thm_Name.list (Sign.full_name_pos thy b) #> map (fn ((name, pos), thm) =>
        let
          fun err msg =
            error ("Malformed global fact " ^
              Thm_Name.print name ^ Position.here pos ^ "\n" ^ msg);
          val prop = Thm.plain_prop_of thm
            handle THM _ =>
              thm
              |> Thm.check_hyps (Context.Theory thy)
              |> Thm.full_prop_of;
          val _ =
            ignore (Logic.unvarify_global (Term_Subst.zero_var_indexes prop))
              handle TYPE (msg, _, _) => err msg
                | TERM (msg, _) => err msg
                | ERROR msg => err msg;
        in thm end);
    val arg = (b, Lazy.map_finished check fact);
  in
    thy |> map_facts (Facts.add_static (Context.Theory thy) {strict = true, index = false} arg #> #2)
  end;

fun add_thms_lazy kind (b, thms) thy =
  let
    val name = Sign.full_name_pos thy b;
    val register = register_proofs_lazy {zproof = true} name;
  in
    if #1 name = "" then register thms thy |> #2
    else
      thy
      |> register (Lazy.map_finished (name_thms official1 name #> map (Thm.kind_rule kind)) thms)
      |-> curry add_facts b
  end;


(* apply theorems and attributes *)

fun apply_facts zproof name_flags1 name_flags2 (b, facts) thy =
  let
    val name = Sign.full_name_pos thy b;
    val named_facts = Thm_Name.expr name facts;
    val (named_facts', thy') =
      (named_facts, thy) |-> fold_map (fn (thms, atts) => fn thy1 =>
        let val (thms', thy2) = fold_map (store_proof zproof) thms thy1
        in ((thms', atts), thy2) end);

    val unnamed = #1 name = "";
    val name_thm1 = if unnamed then #2 else uncurry (name_thm name_flags1);

    val app_facts =
      fold_maps (fn (named_thms, atts) => fn thy =>
        let val thms = map name_thm1 named_thms
        in fold_map (Thm.theory_attributes atts o Thm.transfer thy) thms thy end);
    val register = register_proofs {zproof = false} name;
  in
    if unnamed then app_facts named_facts' thy' |-> register
    else
      let
        val (thms', thy') = app_facts named_facts' thy' |>> name_thms name_flags2 name |-> register;
        val thy'' = thy' |> add_facts (b, Lazy.value thms');
      in (map (Thm.transfer thy'') thms', thy'') end
  end;


(* store_thm *)

fun store_thm (b, th) =
  apply_facts {zproof = true} official1 official2 (b, [([th], [])]) #>> the_single;

fun store_thm_open (b, th) =
  apply_facts {zproof = true} unofficial1 unofficial2 (b, [([th], [])]) #>> the_single;


(* add_thms(s) *)

val add_thmss =
  fold_map (fn ((b, thms), atts) =>
    apply_facts  {zproof = true} official1 official2 (b, [(thms, atts)]));

fun add_thms args =
  add_thmss (map (apfst (apsnd single)) args) #>> map the_single;

val add_thm = yield_singleton add_thms;


(* dynamic theorems *)

fun add_thms_dynamic' context arg thy =
  let val (name, facts') = Facts.add_dynamic context arg (facts_of thy)
  in (name, map_facts (K facts') thy) end;

fun add_thms_dynamic arg thy =
  add_thms_dynamic' (Context.Theory thy) arg thy |> snd;


(* note_thmss *)

local

fun note_thms' zproof kind ((b, more_atts), facts) thy =
  let
    val name = Sign.full_name thy b;
    val facts' = facts |> map (apsnd (fn atts => surround (Thm.kind kind) (atts @ more_atts)));
    val (thms', thy') = thy |> apply_facts zproof official1 official2 (b, facts');
  in ((name, thms'), thy') end;

in

val note_thms = note_thms' {zproof = true};
val note_thmss = fold_map o note_thms;
val note_thmss_foundation = fold_map o note_thms' {zproof = false};

end;


(* old-style defs *)

local

fun add unchecked overloaded (b, prop) thy =
  let
    val context = Defs.global_context thy;
    val ((_, def), thy') = Thm.add_def context unchecked overloaded (b, prop) thy;
    val thm = def
      |> Thm.forall_intr_frees
      |> Thm.forall_elim_vars 0
      |> Thm.varifyT_global;
  in thy' |> apply_facts {zproof = true} unnamed official2 (b, [([thm], [])]) |>> the_single end;

in

val add_def = add false false;
val add_def_overloaded = add false true;
val add_def_unchecked = add true false;
val add_def_unchecked_overloaded = add true true;

end;

end;
