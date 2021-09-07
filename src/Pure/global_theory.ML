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
  val get_thm_names: theory -> Thm_Name.T Inttab.table
  val dest_thm_names: theory -> (Proofterm.thm_id * Thm_Name.T) list
  val lookup_thm_id: theory -> Proofterm.thm_id -> Thm_Name.T option
  val lookup_thm: theory -> thm -> (Proofterm.thm_id * Thm_Name.T) option
  val get_thms: theory -> xstring -> thm list
  val get_thm: theory -> xstring -> thm
  val transfer_theories: theory -> thm -> thm
  val all_thms_of: theory -> bool -> (string * thm) list
  val get_thm_name: theory -> Thm_Name.T * Position.T -> thm
  val burrow_fact: ('a list -> 'b list) -> ('a list * 'c) list -> ('b list * 'c) list
  val burrow_facts: ('a list -> 'b list) ->
    ('c * ('a list * 'd) list) list -> ('c * ('b list * 'd) list) list
  val name_multi: string * Position.T -> thm list -> ((string * Position.T) * thm) list
  type name_flags
  val unnamed: name_flags
  val official1: name_flags
  val official2: name_flags
  val unofficial1: name_flags
  val unofficial2: name_flags
  val name_thm: name_flags -> string * Position.T -> thm -> thm
  val name_thms: name_flags -> string * Position.T -> thm list -> thm list
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
  val note_thms: string -> Thm.binding * (thm list * attribute list) list -> theory ->
    (string * thm list) * theory
  val note_thmss: string -> (Thm.binding * (thm list * attribute list) list) list -> theory ->
    (string * thm list) list * theory
  val add_defs: bool -> ((binding * term) * attribute list) list ->
    theory -> thm list * theory
  val add_defs_unchecked: bool -> ((binding * term) * attribute list) list ->
    theory -> thm list * theory
end;

structure Global_Theory: GLOBAL_THEORY =
struct

(** theory data **)

structure Data = Theory_Data
(
  type T = Facts.T * Thm_Name.T Inttab.table lazy option;
  val empty: T = (Facts.empty, NONE);
  val extend = I;
  fun merge ((facts1, _), (facts2, _)) = (Facts.merge (facts1, facts2), NONE);
);


(* facts *)

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
  |> maps (uncurry Thm_Name.make_list);


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
                Thm_Name.print thm_name ^ " vs. " ^
                Thm_Name.print thm_name', 0, [thm])
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
        Symtab.update (Context.theory_name thy', thy')));
    fun transfer th =
      Thm.transfer (the_default thy (Symtab.lookup theories (Thm.theory_name th))) th;
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

(* fact specifications *)

fun burrow_fact f = split_list #>> burrow f #> op ~~;
fun burrow_facts f = split_list ##> burrow (burrow_fact f) #> op ~~;


(* name theorems *)

abstype name_flags = No_Name_Flags | Name_Flags of {pre: bool, official: bool}
with

val unnamed = No_Name_Flags;
val official1 = Name_Flags {pre = true, official = true};
val official2 = Name_Flags {pre = false, official = true};
val unofficial1 = Name_Flags {pre = true, official = false};
val unofficial2 = Name_Flags {pre = false, official = false};

fun name_thm name_flags (name, pos) =
  Thm.solve_constraints #> (fn thm =>
    (case name_flags of
      No_Name_Flags => thm
    | Name_Flags {pre, official} =>
        thm
        |> (official andalso (not pre orelse Thm.raw_derivation_name thm = "")) ?
            Thm.name_derivation (name, pos)
        |> (name <> "" andalso (not pre orelse not (Thm.has_name_hint thm))) ?
            Thm.put_name_hint name));

end;

fun name_multi (name, pos) =
  Thm_Name.make_list name #> (map o apfst) (fn thm_name => (Thm_Name.flatten thm_name, pos));

fun name_thms name_flags name_pos =
  name_multi name_pos #> map (uncurry (name_thm name_flags));


(* apply theorems and attributes *)

fun register_proofs thms thy = (thms, Thm.register_proofs (Lazy.value thms) thy);

fun bind_name thy b = (Sign.full_name thy b, Binding.default_pos_of b);

fun add_facts (b, fact) thy =
  let
    val (full_name, pos) = bind_name thy b;
    fun check fact =
      fact |> map_index (fn (i, thm) =>
        let
          fun err msg =
            error ("Malformed global fact " ^
              quote (full_name ^
                (if length fact = 1 then "" else "(" ^ string_of_int (i + 1) ^ ")")) ^
              Position.here pos ^ "\n" ^ msg);
          val prop = Thm.plain_prop_of thm
            handle THM _ =>
              thm
              |> Thm.check_hyps (Context.Theory thy)
              |> Thm.full_prop_of;
        in
          ignore (Logic.unvarify_global (Term_Subst.zero_var_indexes prop))
            handle TYPE (msg, _, _) => err msg
              | TERM (msg, _) => err msg
              | ERROR msg => err msg
        end);
    val arg = (b, Lazy.map_finished (tap check) fact);
  in
    thy |> map_facts (Facts.add_static (Context.Theory thy) {strict = true, index = false} arg #> #2)
  end;

fun check_thms_lazy (thms: thm list lazy) =
  if Proofterm.proofs_enabled () orelse Options.default_bool "strict_facts"
  then Lazy.force_value thms else thms;

fun add_thms_lazy kind (b, thms) thy =
  if Binding.is_empty b then Thm.register_proofs (check_thms_lazy thms) thy
  else
    let
      val name_pos = bind_name thy b;
      val thms' =
        check_thms_lazy thms
        |> Lazy.map_finished (name_thms official1 name_pos #> map (Thm.kind_rule kind));
    in thy |> Thm.register_proofs thms' |> add_facts (b, thms') end;

val app_facts =
  apfst flat oo fold_map (fn (thms, atts) => fn thy =>
    fold_map (Thm.theory_attributes atts) (map (Thm.transfer thy) thms) thy);

fun apply_facts name_flags1 name_flags2 (b, facts) thy =
  if Binding.is_empty b then app_facts facts thy |-> register_proofs
  else
    let
      val name_pos = bind_name thy b;
      val (thms', thy') = thy
        |> app_facts (map (apfst (name_thms name_flags1 name_pos)) facts)
        |>> name_thms name_flags2 name_pos |-> register_proofs;
      val thy'' = thy' |> add_facts (b, Lazy.value thms');
    in (map (Thm.transfer thy'') thms', thy'') end;


(* store_thm *)

fun store_thm (b, th) =
  apply_facts official1 official2 (b, [([th], [])]) #>> the_single;

fun store_thm_open (b, th) =
  apply_facts unofficial1 unofficial2 (b, [([th], [])]) #>> the_single;


(* add_thms(s) *)

val add_thmss =
  fold_map (fn ((b, thms), atts) => apply_facts official1 official2 (b, [(thms, atts)]));

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

fun note_thms kind ((b, more_atts), facts) thy =
  let
    val name = Sign.full_name thy b;
    val facts' = facts |> map (apsnd (fn atts => surround (Thm.kind kind) (atts @ more_atts)));
    val (thms', thy') = thy |> apply_facts official1 official2 (b, facts');
  in ((name, thms'), thy') end;

val note_thmss = fold_map o note_thms;


(* old-style defs *)

local

fun add unchecked overloaded = fold_map (fn ((b, prop), atts) => fn thy =>
  let
    val context = Defs.global_context thy;
    val ((_, def), thy') = Thm.add_def context unchecked overloaded (b, prop) thy;
    val thm = def
      |> Thm.forall_intr_frees
      |> Thm.forall_elim_vars 0
      |> Thm.varifyT_global;
  in thy' |> apply_facts unnamed official2 (b, [([thm], atts)]) |>> the_single end);

in

val add_defs = add false;
val add_defs_unchecked = add true;

end;

end;
