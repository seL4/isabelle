(*  Title:      Pure/pure_thy.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Theorem storage.  The ProtoPure theory.
*)

signature BASIC_PURE_THY =
sig
  structure ProtoPure:
    sig
      val thy: theory
      val prop_def: thm
      val term_def: thm
      val conjunction_def: thm
    end
end;

signature PURE_THY =
sig
  include BASIC_PURE_THY
  val tag_rule: Markup.property -> thm -> thm
  val untag_rule: string -> thm -> thm
  val tag: Markup.property -> attribute
  val untag: string -> attribute
  val has_name_hint: thm -> bool
  val get_name_hint: thm -> string
  val put_name_hint: string -> thm -> thm
  val get_group: thm -> string option
  val put_group: string -> thm -> thm
  val group: string -> attribute
  val has_kind: thm -> bool
  val get_kind: thm -> string
  val kind_rule: string -> thm -> thm
  val kind: string -> attribute
  val kind_internal: attribute
  val has_internal: Markup.property list -> bool
  val is_internal: thm -> bool
  val get_fact: theory -> Facts.ref -> thm list
  val get_fact_silent: theory -> Facts.ref -> thm list
  val get_thms: theory -> xstring -> thm list
  val get_thm: theory -> xstring -> thm
  val theorems_of: theory -> thm list NameSpace.table
  val all_facts_of: theory -> Facts.T
  val thms_of: theory -> (string * thm) list
  val all_thms_of: theory -> (string * thm) list
  val hide_thms: bool -> string list -> theory -> theory
  val map_facts: ('a -> 'b) -> ('c * ('a list * 'd) list) list -> ('c * ('b list * 'd) list) list
  val burrow_fact: ('a list -> 'b list) -> ('a list * 'c) list -> ('b list * 'c) list
  val burrow_facts: ('a list -> 'b list) ->
    ('c * ('a list * 'd) list) list -> ('c * ('b list * 'd) list) list
  val name_multi: string -> 'a list -> (string * 'a) list
  val name_thm: bool -> bool -> string -> thm -> thm
  val name_thms: bool -> bool -> string -> thm list -> thm list
  val name_thmss: bool -> string -> (thm list * 'a) list -> (thm list * 'a) list
  val store_thm: (bstring * thm) * attribute list -> theory -> thm * theory
  val smart_store_thms: (bstring * thm list) -> thm list
  val smart_store_thms_open: (bstring * thm list) -> thm list
  val forall_elim_var: int -> thm -> thm
  val forall_elim_vars: int -> thm -> thm
  val add_thms_dynamic: bstring * (Context.generic -> thm list) -> theory -> theory
  val add_thms: ((bstring * thm) * attribute list) list -> theory -> thm list * theory
  val add_thmss: ((bstring * thm list) * attribute list) list -> theory -> thm list list * theory
  val note: string -> string * thm -> theory -> thm * theory
  val note_thmss: string -> ((bstring * attribute list) *
    (Facts.ref * attribute list) list) list -> theory -> (bstring * thm list) list * theory
  val note_thmss_i: string -> ((bstring * attribute list) *
    (thm list * attribute list) list) list -> theory -> (bstring * thm list) list * theory
  val note_thmss_grouped: string -> string -> ((bstring * attribute list) *
    (thm list * attribute list) list) list -> theory -> (bstring * thm list) list * theory
  val note_thmss_qualified: string -> string -> ((bstring * attribute list) *
    (thm list * attribute list) list) list -> theory -> (bstring * thm list) list * theory
  val add_axioms: ((bstring * string) * attribute list) list -> theory -> thm list * theory
  val add_axioms_i: ((bstring * term) * attribute list) list -> theory -> thm list * theory
  val add_axiomss: ((bstring * string list) * attribute list) list ->
    theory -> thm list list * theory
  val add_axiomss_i: ((bstring * term list) * attribute list) list ->
    theory -> thm list list * theory
  val add_defs: bool -> ((bstring * string) * attribute list) list ->
    theory -> thm list * theory
  val add_defs_i: bool -> ((bstring * term) * attribute list) list ->
    theory -> thm list * theory
  val add_defs_unchecked: bool -> ((bstring * string) * attribute list) list ->
    theory -> thm list * theory
  val add_defs_unchecked_i: bool -> ((bstring * term) * attribute list) list ->
    theory -> thm list * theory
  val appl_syntax: (string * typ * mixfix) list
  val applC_syntax: (string * typ * mixfix) list
end;

structure PureThy: PURE_THY =
struct


(*** theorem tags ***)

(* add / delete tags *)

fun tag_rule tg = Thm.map_tags (insert (op =) tg);
fun untag_rule s = Thm.map_tags (filter_out (fn (s', _) => s = s'));

fun tag tg x = Thm.rule_attribute (K (tag_rule tg)) x;
fun untag s x = Thm.rule_attribute (K (untag_rule s)) x;


(* unofficial theorem names *)

fun the_name_hint thm = the (AList.lookup (op =) (Thm.get_tags thm) Markup.nameN);

val has_name_hint = can the_name_hint;
val get_name_hint = the_default "??.unknown" o try the_name_hint;

fun put_name_hint name = untag_rule Markup.nameN #> tag_rule (Markup.nameN, name);


(* theorem groups *)

fun get_group thm = AList.lookup (op =) (Thm.get_tags thm) Markup.groupN;

fun put_group name =
  if name = "" then I else Thm.map_tags (AList.update (op =) (Markup.groupN, name));

fun group name = Thm.rule_attribute (K (put_group name));


(* theorem kinds *)

fun the_kind thm = the (AList.lookup (op =) (Thm.get_tags thm) Markup.kindN);

val has_kind = can the_kind;
val get_kind = the_default "" o try the_kind;

fun kind_rule k = tag_rule (Markup.kindN, k) o untag_rule Markup.kindN;
fun kind k x = if k = "" then x else Thm.rule_attribute (K (kind_rule k)) x;
fun kind_internal x = kind Thm.internalK x;
fun has_internal tags = exists (fn tg => tg = (Markup.kindN, Thm.internalK)) tags;
val is_internal = has_internal o Thm.get_tags;



(*** theorem database ***)

(** dataype theorems **)

datatype thms = Thms of
 {theorems: thm list NameSpace.table,   (* FIXME legacy *)
  all_facts: Facts.T};

fun make_thms theorems all_facts = Thms {theorems = theorems, all_facts = all_facts};

structure TheoremsData = TheoryDataFun
(
  type T = thms ref;   (* FIXME legacy *)
  val empty = ref (make_thms NameSpace.empty_table Facts.empty);
  fun copy (ref x) = ref x;
  fun extend (ref (Thms {theorems = _, all_facts})) = ref (make_thms NameSpace.empty_table all_facts);
  fun merge _
     (ref (Thms {theorems = _, all_facts = all_facts1}),
      ref (Thms {theorems = _, all_facts = all_facts2})) =
    ref (make_thms NameSpace.empty_table (Facts.merge (all_facts1, all_facts2)));
);

val get_theorems_ref = TheoremsData.get;
val get_theorems = (fn Thms args => args) o ! o get_theorems_ref;
val theorems_of = #theorems o get_theorems;
val all_facts_of = #all_facts o get_theorems;



(** retrieve theorems **)

local

fun lookup_thms thy xname =
  let
    val (space, thms) = #theorems (get_theorems thy);
    val name = NameSpace.intern space xname;
  in Option.map (pair name) (Symtab.lookup thms name) end;

fun lookup_fact thy xname =
  let
    val facts = all_facts_of thy;
    val name = NameSpace.intern (Facts.space_of facts) xname;
  in Option.map (pair name) (Facts.lookup (Context.Theory thy) facts name) end;

fun show_result NONE = "none"
  | show_result (SOME (name, _)) = quote name;

fun get silent theory thmref =
  let
    val name = Facts.name_of_ref thmref;
    val pos = Facts.pos_of_ref thmref;
    val new_res = lookup_fact theory name;
    val old_res = get_first (fn thy => lookup_thms thy name) (theory :: Theory.ancestors_of theory);
    val is_same =
      (case (new_res, old_res) of
        (NONE, NONE) => true
      | (SOME (_, ths1), SOME (_, ths2)) => Thm.eq_thms (ths1, ths2)
      | _ => false);
    val _ =
      if is_same orelse silent then ()
      else legacy_feature ("Fact lookup differs from old-style thm database:\n" ^
        show_result new_res ^ " vs " ^ show_result old_res ^ Position.str_of pos);
  in
    (case old_res of
      NONE => error ("Unknown theorem(s) " ^ quote name ^ Position.str_of pos)
    | SOME (_, ths) => Facts.select thmref (map (Thm.transfer theory) ths))
  end;

in

val get_fact_silent = get true;
val get_fact = get false;

fun get_thms thy = get_fact thy o Facts.named;
fun get_thm thy name = Facts.the_single name (get_thms thy name);

end;


(* thms_of etc. *)

fun thms_of thy =
  let val thms = #2 (theorems_of thy)
  in map (`(get_name_hint)) (maps snd (Symtab.dest thms)) end;

fun all_thms_of thy = maps thms_of (thy :: Theory.ancestors_of thy);



(** store theorems **)                    (*DESTRUCTIVE*)

(* hiding -- affects current theory node only *)

fun hide_thms fully names thy = CRITICAL (fn () =>
  let
    val r as ref (Thms {theorems = (space, thms), all_facts}) = get_theorems_ref thy;
    val space' = fold (NameSpace.hide fully) names space;
  in r := make_thms (space', thms) all_facts; thy end);


(* fact specifications *)

fun map_facts f = map (apsnd (map (apfst (map f))));
fun burrow_fact f = split_list #>> burrow f #> op ~~;
fun burrow_facts f = split_list ##> burrow (burrow_fact f) #> op ~~;


(* naming *)

fun gen_names _ len "" = replicate len ""
  | gen_names j len name = map (fn i => name ^ "_" ^ string_of_int i) (j + 1 upto j + len);

fun name_multi name [x] = [(name, x)]
  | name_multi name xs = gen_names 0 (length xs) name ~~ xs;

fun name_thm pre official name thm = thm
  |> (if Thm.get_name thm <> "" andalso pre orelse not official then I else Thm.put_name name)
  |> (if has_name_hint thm andalso pre orelse name = "" then I else put_name_hint name)
  |> Thm.map_tags (Position.default_properties (Position.thread_data ()));

fun name_thms pre official name xs =
  map (uncurry (name_thm pre official)) (name_multi name xs);

fun name_thmss official name fact =
  burrow_fact (name_thms true official name) fact;


(* add_thms_dynamic *)

fun add_thms_dynamic (bname, f) thy = CRITICAL (fn () =>
  let
    val name = Sign.full_name thy bname;
    val r as ref (Thms {theorems, all_facts}) = get_theorems_ref thy;
    val all_facts' = Facts.add_dynamic (Sign.naming_of thy) (name, f) all_facts;
    val _ = r := make_thms theorems all_facts';
  in thy end);


(* enter_thms *)

fun warn_overwrite name = warning ("Replaced old copy of theorems " ^ quote name);
fun warn_same name = warning ("Theorem database already contains a copy of " ^ quote name);

fun enter_thms _ _ app_att ("", thms) thy = app_att (thy, thms) |> swap
  | enter_thms pre_name post_name app_att (bname, thms) thy = CRITICAL (fn () =>
      let
        val name = Sign.full_name thy bname;
        val (thy', thms') = apsnd (post_name name) (app_att (thy, pre_name name thms));
        val r as ref (Thms {theorems = (space, theorems), all_facts}) = get_theorems_ref thy';
        val space' = Sign.declare_name thy' name space;
        val theorems' = Symtab.update (name, thms') theorems;
        val all_facts' = Facts.add_global (Sign.naming_of thy') (name, thms') all_facts;
      in
        (case Symtab.lookup theorems name of
          NONE => ()
        | SOME thms'' =>
            if Thm.eq_thms (thms', thms'') then warn_same name
            else warn_overwrite name);
        r := make_thms (space', theorems') all_facts';
        (thms', thy')
      end);


(* add_thms(s) *)

fun add_thms_atts pre_name ((bname, thms), atts) =
  enter_thms pre_name (name_thms false true)
    (foldl_map (Thm.theory_attributes atts)) (bname, thms);

fun gen_add_thmss pre_name =
  fold_map (add_thms_atts pre_name);

fun gen_add_thms pre_name args =
  apfst (map hd) o gen_add_thmss pre_name (map (apfst (apsnd single)) args);

val add_thmss = gen_add_thmss (name_thms true true);
val add_thms = gen_add_thms (name_thms true true);


(* note_thmss(_i) *)

local

fun gen_note_thmss get tag = fold_map (fn ((bname, more_atts), ths_atts) => fn thy =>
  let
    fun app (x, (ths, atts)) = foldl_map (Thm.theory_attributes atts) (x, ths);
    val (thms, thy') = thy |> enter_thms
      (name_thmss true) (name_thms false true) (apsnd flat o foldl_map app)
      (bname, map (fn (ths, atts) => (get thy ths, surround tag (atts @ more_atts))) ths_atts);
  in ((bname, thms), thy') end);

in

fun note_thmss k = gen_note_thmss get_fact (kind k);
fun note_thmss_i k = gen_note_thmss (K I) (kind k);
fun note_thmss_grouped k g = gen_note_thmss (K I) (kind k #> group g);

end;

fun note kind (name, thm) =
  note_thmss_i kind [((name, []), [([thm], [])])]
  #>> (fn [(_, [thm])] => thm);

fun note_thmss_qualified k path facts thy =
  thy
  |> Sign.add_path path
  |> Sign.no_base_names
  |> note_thmss_i k facts
  ||> Sign.restore_naming thy;


(* store_thm *)

fun store_thm ((bname, thm), atts) thy =
  let val ([th'], thy') = add_thms_atts (name_thms true true) ((bname, [thm]), atts) thy
  in (th', thy') end;


(* smart_store_thms(_open) *)

local

fun smart_store _ (name, []) =
      error ("Cannot store empty list of theorems: " ^ quote name)
  | smart_store official (name, [thm]) =
      fst (enter_thms (name_thms true official) (name_thms false official) I (name, [thm])
        (Thm.theory_of_thm thm))
  | smart_store official (name, thms) =
      let val thy = Theory.merge_list (map Thm.theory_of_thm thms) in
        fst (enter_thms (name_thms true official) (name_thms false official) I (name, thms) thy)
      end;

in

val smart_store_thms = smart_store true;
val smart_store_thms_open = smart_store false;

end;


(* forall_elim_var(s) -- belongs to drule.ML *)

fun forall_elim_vars_aux strip_vars i th =
  let
    val {thy, tpairs, prop, ...} = Thm.rep_thm th;
    val add_used = Term.fold_aterms
      (fn Var ((x, j), _) => if i = j then insert (op =) x else I | _ => I);
    val used = fold (fn (t, u) => add_used t o add_used u) tpairs (add_used prop []);
    val vars = strip_vars prop;
    val cvars = (Name.variant_list used (map #1 vars), vars)
      |> ListPair.map (fn (x, (_, T)) => Thm.cterm_of thy (Var ((x, i), T)));
  in fold Thm.forall_elim cvars th end;

val forall_elim_vars = forall_elim_vars_aux Term.strip_all_vars;

fun forall_elim_var i th = forall_elim_vars_aux
  (fn Const ("all", _) $ Abs (a, T, _) => [(a, T)]
  | _ => raise THM ("forall_elim_vars", i, [th])) i th;


(* store axioms as theorems *)

local
  fun get_ax thy (name, _) = Thm.get_axiom_i thy (Sign.full_name thy name);
  fun get_axs thy named_axs = map (forall_elim_vars 0 o get_ax thy) named_axs;
  fun add_single add ((name, ax), atts) thy =
    let
      val named_ax = [(name, ax)];
      val thy' = add named_ax thy;
      val thm = hd (get_axs thy' named_ax);
    in apfst hd (gen_add_thms (K I) [((name, thm), atts)] thy') end;
  fun add_multi add ((name, axs), atts) thy =
    let
      val named_axs = name_multi name axs;
      val thy' = add named_axs thy;
      val thms = get_axs thy' named_axs;
    in apfst hd (gen_add_thmss (K I) [((name, thms), atts)] thy') end;
  fun add_singles add = fold_map (add_single add);
  fun add_multis add = fold_map (add_multi add);
in
  val add_axioms           = add_singles Theory.add_axioms;
  val add_axioms_i         = add_singles Theory.add_axioms_i;
  val add_axiomss          = add_multis Theory.add_axioms;
  val add_axiomss_i        = add_multis Theory.add_axioms_i;
  val add_defs             = add_singles o Theory.add_defs false;
  val add_defs_i           = add_singles o Theory.add_defs_i false;
  val add_defs_unchecked   = add_singles o Theory.add_defs true;
  val add_defs_unchecked_i = add_singles o Theory.add_defs_i true;
end;



(*** the ProtoPure theory ***)

val typ = SimpleSyntax.read_typ;
val term = SimpleSyntax.read_term;
val prop = SimpleSyntax.read_prop;

val appl_syntax =
 [("_appl", typ "('b => 'a) => args => logic", Mixfix ("(1_/(1'(_')))", [1000, 0], 1000)),
  ("_appl", typ "('b => 'a) => args => aprop", Mixfix ("(1_/(1'(_')))", [1000, 0], 1000))];

val applC_syntax =
 [("",       typ "'a => cargs",                  Delimfix "_"),
  ("_cargs", typ "'a => cargs => cargs",         Mixfix ("_/ _", [1000, 1000], 1000)),
  ("_applC", typ "('b => 'a) => cargs => logic", Mixfix ("(1_/ _)", [1000, 1000], 999)),
  ("_applC", typ "('b => 'a) => cargs => aprop", Mixfix ("(1_/ _)", [1000, 1000], 999))];

val proto_pure =
  Context.pre_pure_thy
  |> Compress.init_data
  |> TheoremsData.init
  |> Sign.add_types
   [("fun", 2, NoSyn),
    ("prop", 0, NoSyn),
    ("itself", 1, NoSyn),
    ("dummy", 0, NoSyn)]
  |> Sign.add_nonterminals Syntax.basic_nonterms
  |> Sign.add_syntax_i
   [("_lambda",     typ "pttrns => 'a => logic",     Mixfix ("(3%_./ _)", [0, 3], 3)),
    ("_abs",        typ "'a",                        NoSyn),
    ("",            typ "'a => args",                Delimfix "_"),
    ("_args",       typ "'a => args => args",        Delimfix "_,/ _"),
    ("",            typ "id => idt",                 Delimfix "_"),
    ("_idtdummy",   typ "idt",                       Delimfix "'_"),
    ("_idtyp",      typ "id => type => idt",         Mixfix ("_::_", [], 0)),
    ("_idtypdummy", typ "type => idt",               Mixfix ("'_()::_", [], 0)),
    ("",            typ "idt => idt",                Delimfix "'(_')"),
    ("",            typ "idt => idts",               Delimfix "_"),
    ("_idts",       typ "idt => idts => idts",       Mixfix ("_/ _", [1, 0], 0)),
    ("",            typ "idt => pttrn",              Delimfix "_"),
    ("",            typ "pttrn => pttrns",           Delimfix "_"),
    ("_pttrns",     typ "pttrn => pttrns => pttrns", Mixfix ("_/ _", [1, 0], 0)),
    ("",            typ "id => aprop",               Delimfix "_"),
    ("",            typ "longid => aprop",           Delimfix "_"),
    ("",            typ "var => aprop",              Delimfix "_"),
    ("_DDDOT",      typ "aprop",                     Delimfix "..."),
    ("_aprop",      typ "aprop => prop",             Delimfix "PROP _"),
    ("_asm",        typ "prop => asms",              Delimfix "_"),
    ("_asms",       typ "prop => asms => asms",      Delimfix "_;/ _"),
    ("_bigimpl",    typ "asms => prop => prop",      Mixfix ("((3[| _ |])/ ==> _)", [0, 1], 1)),
    ("_ofclass",    typ "type => logic => prop",     Delimfix "(1OFCLASS/(1'(_,/ _')))"),
    ("_mk_ofclass", typ "dummy",                     NoSyn),
    ("_TYPE",       typ "type => logic",             Delimfix "(1TYPE/(1'(_')))"),
    ("",            typ "id => logic",               Delimfix "_"),
    ("",            typ "longid => logic",           Delimfix "_"),
    ("",            typ "var => logic",              Delimfix "_"),
    ("_DDDOT",      typ "logic",                     Delimfix "..."),
    ("_constify",   typ "num => num_const",          Delimfix "_"),
    ("_indexnum",   typ "num_const => index",        Delimfix "\\<^sub>_"),
    ("_index",      typ "logic => index",            Delimfix "(00\\<^bsub>_\\<^esub>)"),
    ("_indexdefault", typ "index",                   Delimfix ""),
    ("_indexvar",   typ "index",                     Delimfix "'\\<index>"),
    ("_struct",     typ "index => logic",            Mixfix ("\\<struct>_", [1000], 1000)),
    ("==>",         typ "prop => prop => prop",      Delimfix "op ==>"),
    (Term.dummy_patternN, typ "aprop",               Delimfix "'_")]
  |> Sign.add_syntax_i appl_syntax
  |> Sign.add_modesyntax_i (Symbol.xsymbolsN, true)
   [("fun",      typ "type => type => type",   Mixfix ("(_/ \\<Rightarrow> _)", [1, 0], 0)),
    ("_bracket", typ "types => type => type",  Mixfix ("([_]/ \\<Rightarrow> _)", [0, 0], 0)),
    ("_ofsort",  typ "tid => sort => type",    Mixfix ("_\\<Colon>_", [1000, 0], 1000)),
    ("_constrain", typ "'a => type => 'a",     Mixfix ("_\\<Colon>_", [4, 0], 3)),
    ("_idtyp",    typ "id => type => idt",     Mixfix ("_\\<Colon>_", [], 0)),
    ("_idtypdummy", typ "type => idt",         Mixfix ("'_()\\<Colon>_", [], 0)),
    ("_type_constraint_", typ "'a",            NoSyn),
    ("_lambda",  typ "pttrns => 'a => logic",  Mixfix ("(3\\<lambda>_./ _)", [0, 3], 3)),
    ("==",       typ "'a => 'a => prop",       InfixrName ("\\<equiv>", 2)),
    ("all_binder", typ "idts => prop => prop", Mixfix ("(3\\<And>_./ _)", [0, 0], 0)),
    ("==>",      typ "prop => prop => prop",   InfixrName ("\\<Longrightarrow>", 1)),
    ("_DDDOT",   typ "aprop",                  Delimfix "\\<dots>"),
    ("_bigimpl", typ "asms => prop => prop",   Mixfix ("((1\\<lbrakk>_\\<rbrakk>)/ \\<Longrightarrow> _)", [0, 1], 1)),
    ("_DDDOT",   typ "logic",                  Delimfix "\\<dots>")]
  |> Sign.add_modesyntax_i ("", false)
   [("prop", typ "prop => prop", Mixfix ("_", [0], 0)),
    ("ProtoPure.term", typ "'a => prop", Delimfix "TERM _"),
    ("ProtoPure.conjunction", typ "prop => prop => prop", InfixrName ("&&", 2))]
  |> Sign.add_modesyntax_i ("HTML", false)
   [("_lambda", typ "pttrns => 'a => logic", Mixfix ("(3\\<lambda>_./ _)", [0, 3], 3))]
  |> Sign.add_consts_i
   [("==", typ "'a => 'a => prop", InfixrName ("==", 2)),
    ("==>", typ "prop => prop => prop", Mixfix ("(_/ ==> _)", [2, 1], 1)),
    ("all", typ "('a => prop) => prop", Binder ("!!", 0, 0)),
    ("prop", typ "prop => prop", NoSyn),
    ("TYPE", typ "'a itself", NoSyn),
    (Term.dummy_patternN, typ "'a", Delimfix "'_")]
  |> Theory.add_deps "==" ("==", typ "'a => 'a => prop") []
  |> Theory.add_deps "==>" ("==>", typ "prop => prop => prop") []
  |> Theory.add_deps "all" ("all", typ "('a => prop) => prop") []
  |> Theory.add_deps "TYPE" ("TYPE", typ "'a itself") []
  |> Theory.add_deps Term.dummy_patternN (Term.dummy_patternN, typ "'a") []
  |> Sign.add_trfuns Syntax.pure_trfuns
  |> Sign.add_trfunsT Syntax.pure_trfunsT
  |> Sign.local_path
  |> Sign.add_consts_i
   [("term", typ "'a => prop", NoSyn),
    ("conjunction", typ "prop => prop => prop", NoSyn)]
  |> (add_defs_i false o map Thm.no_attributes)
   [("prop_def", prop "(CONST prop :: prop => prop) (A::prop) == A::prop"),
    ("term_def", prop "(CONST ProtoPure.term :: 'a => prop) (x::'a) == (!!A::prop. A ==> A)"),
    ("conjunction_def", prop "(A && B) == (!!C::prop. (A ==> B ==> C) ==> C)")] |> snd
  |> Sign.hide_consts false ["conjunction", "term"]
  |> add_thmss [(("nothing", []), [])] |> snd
  |> Theory.add_axioms_i Proofterm.equality_axms
  |> Theory.end_theory;

structure ProtoPure =
struct
  val thy = proto_pure;
  val prop_def = get_axiom thy "prop_def";
  val term_def = get_axiom thy "term_def";
  val conjunction_def = get_axiom thy "conjunction_def";
end;

end;

structure BasicPureThy: BASIC_PURE_THY = PureThy;
open BasicPureThy;

