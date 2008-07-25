(*  Title:      Pure/pure_thy.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Theorem storage.  Pure theory syntax and logical content.
*)

signature PURE_THY =
sig
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
  val facts_of: theory -> Facts.T
  val intern_fact: theory -> xstring -> string
  val defined_fact: theory -> string -> bool
  val hide_fact: bool -> string -> theory -> theory
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
  val store_thms: bstring * thm list -> theory -> thm list * theory
  val store_thm: bstring * thm -> theory -> thm * theory
  val store_thm_open: bstring * thm -> theory -> thm * theory
  val add_thm: (bstring * thm) * attribute list -> theory -> thm * theory
  val add_thms: ((bstring * thm) * attribute list) list -> theory -> thm list * theory
  val add_thmss: ((bstring * thm list) * attribute list) list -> theory -> thm list list * theory
  val add_thms_dynamic: bstring * (Context.generic -> thm list) -> theory -> theory
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
  val add_defs: bool -> ((bstring * string) * attribute list) list ->
    theory -> thm list * theory
  val add_defs_i: bool -> ((bstring * term) * attribute list) list ->
    theory -> thm list * theory
  val add_defs_unchecked: bool -> ((bstring * string) * attribute list) list ->
    theory -> thm list * theory
  val add_defs_unchecked_i: bool -> ((bstring * term) * attribute list) list ->
    theory -> thm list * theory
  val old_appl_syntax: theory -> bool
  val old_appl_syntax_setup: theory -> theory
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



(*** stored facts ***)

(** theory data **)

structure FactsData = TheoryDataFun
(
  type T = Facts.T;
  val empty = Facts.empty;
  val copy = I;
  val extend = I;
  fun merge _ = Facts.merge;
);

val facts_of = FactsData.get;

val intern_fact = Facts.intern o facts_of;
val defined_fact = Facts.defined o facts_of;

fun hide_fact fully name = FactsData.map (Facts.hide fully name);



(** retrieve theorems **)

fun get_fact context thy xthmref =
  let
    val xname = Facts.name_of_ref xthmref;
    val pos = Facts.pos_of_ref xthmref;

    val name = intern_fact thy xname;
    val res = Facts.lookup context (facts_of thy) name;
    val _ = Theory.check_thy thy;
  in
    (case res of
      NONE => error ("Unknown fact " ^ quote name ^ Position.str_of pos)
    | SOME ths => Facts.select xthmref (map (Thm.transfer thy) ths))
  end;

fun get_thms thy = get_fact (Context.Theory thy) thy o Facts.named;
fun get_thm thy name = Facts.the_single name (get_thms thy name);

fun all_thms_of thy =
  Facts.fold_static (fn (_, ths) => append (map (`(get_name_hint)) ths)) (facts_of thy) [];



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
  |> (if Thm.get_name thm <> "" andalso pre orelse not official then I else Thm.put_name name)
  |> (if has_name_hint thm andalso pre orelse name = "" then I else put_name_hint name)
  |> Thm.map_tags (Position.default_properties (Position.thread_data ()));

fun name_thms pre official name xs =
  map (uncurry (name_thm pre official)) (name_multi name xs);

fun name_thmss official name fact =
  burrow_fact (name_thms true official name) fact;


(* enter_thms *)

fun enter_thms _ _ app_att ("", thms) thy = app_att (thy, thms) |> swap
  | enter_thms pre_name post_name app_att (bname, thms) thy =
      let
        val naming = Sign.naming_of thy;
        val name = NameSpace.full naming bname;
        val (thy', thms') = apsnd (post_name name) (app_att (thy, pre_name name thms));
        val thms'' = map (Thm.transfer thy') thms';
        val thy'' = thy' |> FactsData.map (Facts.add_global naming (name, thms''));
      in (thms'', thy'') end;


(* store_thm(s) *)

val store_thms = enter_thms (name_thms true true) (name_thms false true) I;
fun store_thm (name, th) = store_thms (name, [th]) #>> the_single;

fun store_thm_open (name, th) =
  enter_thms (name_thms true false) (name_thms false false) I (name, [th]) #>> the_single;


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
val add_thm = yield_singleton add_thms;


(* add_thms_dynamic *)

fun add_thms_dynamic (bname, f) thy =
  let val name = Sign.full_name thy bname
  in thy |> FactsData.map (Facts.add_dynamic (Sign.naming_of thy) (name, f)) end;


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

fun note_thmss k = gen_note_thmss (fn thy => get_fact (Context.Theory thy) thy) (kind k);
fun note_thmss_i k = gen_note_thmss (K I) (kind k);
fun note_thmss_grouped k g = gen_note_thmss (K I) (kind k #> group g);

end;

fun note_thmss_qualified k path facts thy =
  thy
  |> Sign.add_path path
  |> Sign.no_base_names
  |> note_thmss_i k facts
  ||> Sign.restore_naming thy;


(* store axioms as theorems *)

local
  fun get_ax thy (name, _) = Thm.get_axiom_i thy (Sign.full_name thy name);
  fun get_axs thy named_axs = map (Thm.forall_elim_vars 0 o get_ax thy) named_axs;
  fun add_axm add = fold_map (fn ((name, ax), atts) => fn thy =>
    let
      val named_ax = [(name, ax)];
      val thy' = add named_ax thy;
      val thm = hd (get_axs thy' named_ax);
    in apfst hd (gen_add_thms (K I) [((name, thm), atts)] thy') end);
in
  val add_axioms           = add_axm Theory.add_axioms;
  val add_axioms_i         = add_axm Theory.add_axioms_i;
  val add_defs             = add_axm o Theory.add_defs false;
  val add_defs_i           = add_axm o Theory.add_defs_i false;
  val add_defs_unchecked   = add_axm o Theory.add_defs true;
  val add_defs_unchecked_i = add_axm o Theory.add_defs_i true;
end;



(*** Pure theory syntax and logical content ***)

val typ = SimpleSyntax.read_typ;
val term = SimpleSyntax.read_term;
val prop = SimpleSyntax.read_prop;


(* application syntax variants *)

val appl_syntax =
 [("_appl", typ "('b => 'a) => args => logic", Mixfix ("(1_/(1'(_')))", [1000, 0], 1000)),
  ("_appl", typ "('b => 'a) => args => aprop", Mixfix ("(1_/(1'(_')))", [1000, 0], 1000))];

val applC_syntax =
 [("",       typ "'a => cargs",                  Delimfix "_"),
  ("_cargs", typ "'a => cargs => cargs",         Mixfix ("_/ _", [1000, 1000], 1000)),
  ("_applC", typ "('b => 'a) => cargs => logic", Mixfix ("(1_/ _)", [1000, 1000], 999)),
  ("_applC", typ "('b => 'a) => cargs => aprop", Mixfix ("(1_/ _)", [1000, 1000], 999))];

structure OldApplSyntax = TheoryDataFun
(
  type T = bool;
  val empty = false;
  val copy = I;
  val extend = I;
  fun merge _ (b1, b2) : T =
    if b1 = b2 then b1
    else error "Cannot merge theories with different application syntax";
);

val old_appl_syntax = OldApplSyntax.get;

val old_appl_syntax_setup =
  OldApplSyntax.put true #>
  Sign.del_modesyntax_i Syntax.mode_default applC_syntax #>
  Sign.add_syntax_i appl_syntax;


(* main content *)

val _ = Context.>> (Context.map_theory
  (OldApplSyntax.init #>
   Sign.add_types
   [("fun", 2, NoSyn),
    ("prop", 0, NoSyn),
    ("itself", 1, NoSyn),
    ("dummy", 0, NoSyn)]
  #> Sign.add_nonterminals Syntax.basic_nonterms
  #> Sign.add_syntax_i
   [("_lambda",     typ "pttrns => 'a => logic",       Mixfix ("(3%_./ _)", [0, 3], 3)),
    ("_abs",        typ "'a",                          NoSyn),
    ("",            typ "'a => args",                  Delimfix "_"),
    ("_args",       typ "'a => args => args",          Delimfix "_,/ _"),
    ("",            typ "id => idt",                   Delimfix "_"),
    ("_idtdummy",   typ "idt",                         Delimfix "'_"),
    ("_idtyp",      typ "id => type => idt",           Mixfix ("_::_", [], 0)),
    ("_idtypdummy", typ "type => idt",                 Mixfix ("'_()::_", [], 0)),
    ("",            typ "idt => idt",                  Delimfix "'(_')"),
    ("",            typ "idt => idts",                 Delimfix "_"),
    ("_idts",       typ "idt => idts => idts",         Mixfix ("_/ _", [1, 0], 0)),
    ("",            typ "idt => pttrn",                Delimfix "_"),
    ("",            typ "pttrn => pttrns",             Delimfix "_"),
    ("_pttrns",     typ "pttrn => pttrns => pttrns",   Mixfix ("_/ _", [1, 0], 0)),
    ("",            typ "id => aprop",                 Delimfix "_"),
    ("",            typ "longid => aprop",             Delimfix "_"),
    ("",            typ "var => aprop",                Delimfix "_"),
    ("_DDDOT",      typ "aprop",                       Delimfix "..."),
    ("_aprop",      typ "aprop => prop",               Delimfix "PROP _"),
    ("_asm",        typ "prop => asms",                Delimfix "_"),
    ("_asms",       typ "prop => asms => asms",        Delimfix "_;/ _"),
    ("_bigimpl",    typ "asms => prop => prop",        Mixfix ("((3[| _ |])/ ==> _)", [0, 1], 1)),
    ("_ofclass",    typ "type => logic => prop",       Delimfix "(1OFCLASS/(1'(_,/ _')))"),
    ("_mk_ofclass", typ "dummy",                       NoSyn),
    ("_TYPE",       typ "type => logic",               Delimfix "(1TYPE/(1'(_')))"),
    ("",            typ "id => logic",                 Delimfix "_"),
    ("",            typ "longid => logic",             Delimfix "_"),
    ("",            typ "var => logic",                Delimfix "_"),
    ("_DDDOT",      typ "logic",                       Delimfix "..."),
    ("_constify",   typ "num => num_const",            Delimfix "_"),
    ("_indexnum",   typ "num_const => index",          Delimfix "\\<^sub>_"),
    ("_index",      typ "logic => index",              Delimfix "(00\\<^bsub>_\\<^esub>)"),
    ("_indexdefault", typ "index",                     Delimfix ""),
    ("_indexvar",   typ "index",                       Delimfix "'\\<index>"),
    ("_struct",     typ "index => logic",              Mixfix ("\\<struct>_", [1000], 1000)),
    ("==>",         typ "prop => prop => prop",        Delimfix "op ==>"),
    (Term.dummy_patternN, typ "aprop",                 Delimfix "'_")]
  #> Sign.add_syntax_i applC_syntax
  #> Sign.add_modesyntax_i (Symbol.xsymbolsN, true)
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
  #> Sign.add_modesyntax_i ("", false)
   [("prop", typ "prop => prop", Mixfix ("_", [0], 0)),
    ("Pure.term", typ "'a => prop", Delimfix "TERM _"),
    ("Pure.conjunction", typ "prop => prop => prop", InfixrName ("&&", 2))]
  #> Sign.add_modesyntax_i ("HTML", false)
   [("_lambda", typ "pttrns => 'a => logic", Mixfix ("(3\\<lambda>_./ _)", [0, 3], 3))]
  #> Sign.add_consts_i
   [("==", typ "'a => 'a => prop", InfixrName ("==", 2)),
    ("==>", typ "prop => prop => prop", Mixfix ("(_/ ==> _)", [2, 1], 1)),
    ("all", typ "('a => prop) => prop", Binder ("!!", 0, 0)),
    ("prop", typ "prop => prop", NoSyn),
    ("TYPE", typ "'a itself", NoSyn),
    (Term.dummy_patternN, typ "'a", Delimfix "'_")]
  #> Theory.add_deps "==" ("==", typ "'a => 'a => prop") []
  #> Theory.add_deps "==>" ("==>", typ "prop => prop => prop") []
  #> Theory.add_deps "all" ("all", typ "('a => prop) => prop") []
  #> Theory.add_deps "TYPE" ("TYPE", typ "'a itself") []
  #> Theory.add_deps Term.dummy_patternN (Term.dummy_patternN, typ "'a") []
  #> Sign.add_trfuns Syntax.pure_trfuns
  #> Sign.add_trfunsT Syntax.pure_trfunsT
  #> Sign.local_path
  #> Sign.add_consts_i
   [("term", typ "'a => prop", NoSyn),
    ("conjunction", typ "prop => prop => prop", NoSyn)]
  #> (add_defs_i false o map Thm.no_attributes)
   [("prop_def", prop "(CONST prop :: prop => prop) (A::prop) == A::prop"),
    ("term_def", prop "(CONST Pure.term :: 'a => prop) (x::'a) == (!!A::prop. A ==> A)"),
    ("conjunction_def", prop "(A && B) == (!!C::prop. (A ==> B ==> C) ==> C)")] #> snd
  #> Sign.hide_const false "Pure.conjunction"
  #> Sign.hide_const false "Pure.term"
  #> add_thmss [(("nothing", []), [])] #> snd
  #> Theory.add_axioms_i Proofterm.equality_axms));

end;

