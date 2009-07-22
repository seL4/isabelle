(*  Title:      Pure/pure_thy.ML
    Author:     Markus Wenzel, TU Muenchen

Theorem storage.  Pure theory syntax and logical content.
*)

signature PURE_THY =
sig
  val facts_of: theory -> Facts.T
  val intern_fact: theory -> xstring -> string
  val defined_fact: theory -> string -> bool
  val hide_fact: bool -> string -> theory -> theory
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
  val name_thm: bool -> bool -> Position.T -> string -> thm -> thm
  val name_thms: bool -> bool -> Position.T -> string -> thm list -> thm list
  val name_thmss: bool -> Position.T -> string -> (thm list * 'a) list -> (thm list * 'a) list
  val store_thms: binding * thm list -> theory -> thm list * theory
  val store_thm: binding * thm -> theory -> thm * theory
  val store_thm_open: binding * thm -> theory -> thm * theory
  val add_thms: ((binding * thm) * attribute list) list -> theory -> thm list * theory
  val add_thm: (binding * thm) * attribute list -> theory -> thm * theory
  val add_thmss: ((binding * thm list) * attribute list) list -> theory -> thm list list * theory
  val add_thms_dynamic: binding * (Context.generic -> thm list) -> theory -> theory
  val note_thmss: string -> (Thm.binding * (thm list * attribute list) list) list
    -> theory -> (string * thm list) list * theory
  val note_thmss_grouped: string -> string -> (Thm.binding * (thm list * attribute list) list) list
    -> theory -> (string * thm list) list * theory
  val add_axioms: ((binding * term) * attribute list) list -> theory -> thm list * theory
  val add_axioms_cmd: ((binding * string) * attribute list) list -> theory -> thm list * theory
  val add_defs: bool -> ((binding * term) * attribute list) list ->
    theory -> thm list * theory
  val add_defs_unchecked: bool -> ((binding * term) * attribute list) list ->
    theory -> thm list * theory
  val add_defs_cmd: bool -> ((binding * string) * attribute list) list ->
    theory -> thm list * theory
  val add_defs_unchecked_cmd: bool -> ((binding * string) * attribute list) list ->
    theory -> thm list * theory
  val old_appl_syntax: theory -> bool
  val old_appl_syntax_setup: theory -> theory
end;

structure PureThy: PURE_THY =
struct


(*** stored facts ***)

(** theory data **)

structure FactsData = TheoryDataFun
(
  type T = Facts.T * thm list;
  val empty = (Facts.empty, []);
  val copy = I;
  fun extend (facts, _) = (facts, []);
  fun merge _ ((facts1, _), (facts2, _)) = (Facts.merge (facts1, facts2), []);
);


(* facts *)

val facts_of = #1 o FactsData.get;

val intern_fact = Facts.intern o facts_of;
val defined_fact = Facts.defined o facts_of;

fun hide_fact fully name = FactsData.map (apfst (Facts.hide fully name));


(* proofs *)

fun register_proofs (thy, thms) = (FactsData.map (apsnd (append thms)) thy, thms);

fun join_proofs thy = Thm.join_proofs (rev (#2 (FactsData.get thy)));



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
    | SOME (static, ths) =>
        (Position.report ((if static then Markup.fact else Markup.dynamic_fact) name) pos;
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

fun name_thm pre official pos name thm = thm
  |> (if Thm.get_name thm <> "" andalso pre orelse not official then I else Thm.put_name name)
  |> (if Thm.has_name_hint thm andalso pre orelse name = "" then I else Thm.put_name_hint name)
  |> Thm.default_position pos
  |> Thm.default_position (Position.thread_data ());

fun name_thms pre official pos name xs =
  map (uncurry (name_thm pre official pos)) (name_multi name xs);

fun name_thmss official pos name fact =
  burrow_fact (name_thms true official pos name) fact;


(* enter_thms *)

fun enter_thms pre_name post_name app_att (b, thms) thy =
  if Binding.is_empty b
  then swap (register_proofs (app_att (thy, thms)))
  else
    let
      val naming = Sign.naming_of thy;
      val name = NameSpace.full_name naming b;
      val (thy', thms') =
        register_proofs (apsnd (post_name name) (app_att (thy, pre_name name thms)));
      val thms'' = map (Thm.transfer thy') thms';
      val thy'' = thy' |> (FactsData.map o apfst) (Facts.add_global naming (b, thms'') #> snd);
    in (thms'', thy'') end;


(* store_thm(s) *)

fun store_thms (b, thms) = enter_thms (name_thms true true Position.none)
  (name_thms false true Position.none) I (b, thms);

fun store_thm (b, th) = store_thms (b, [th]) #>> the_single;

fun store_thm_open (b, th) =
  enter_thms (name_thms true false Position.none) (name_thms false false Position.none) I
    (b, [th]) #>> the_single;


(* add_thms(s) *)

fun add_thms_atts pre_name ((b, thms), atts) =
  enter_thms pre_name (name_thms false true Position.none)
    (Library.foldl_map (Thm.theory_attributes atts)) (b, thms);

fun gen_add_thmss pre_name =
  fold_map (add_thms_atts pre_name);

fun gen_add_thms pre_name args =
  apfst (map hd) o gen_add_thmss pre_name (map (apfst (apsnd single)) args);

val add_thmss = gen_add_thmss (name_thms true true Position.none);
val add_thms = gen_add_thms (name_thms true true Position.none);
val add_thm = yield_singleton add_thms;


(* add_thms_dynamic *)

fun add_thms_dynamic (b, f) thy = thy
  |> (FactsData.map o apfst)
      (Facts.add_dynamic (Sign.naming_of thy) (b, f) #> snd);


(* note_thmss *)

local

fun gen_note_thmss tag = fold_map (fn ((b, more_atts), ths_atts) => fn thy =>
  let
    val pos = Binding.pos_of b;
    val name = Sign.full_name thy b;
    val _ = Position.report (Markup.fact_decl name) pos;

    fun app (x, (ths, atts)) = Library.foldl_map (Thm.theory_attributes atts) (x, ths);
    val (thms, thy') = thy |> enter_thms
      (name_thmss true pos) (name_thms false true pos) (apsnd flat o Library.foldl_map app)
      (b, map (fn (ths, atts) => (ths, surround tag (atts @ more_atts))) ths_atts);
  in ((name, thms), thy') end);

in

fun note_thmss k = gen_note_thmss (Thm.kind k);
fun note_thmss_grouped k g = gen_note_thmss (Thm.kind k #> Thm.group g);

end;


(* store axioms as theorems *)

local
  fun get_ax thy (b, _) = Thm.axiom thy (Sign.full_name thy b);
  fun get_axs thy named_axs = map (Thm.forall_elim_vars 0 o get_ax thy) named_axs;
  fun add_axm add = fold_map (fn ((b, ax), atts) => fn thy =>
    let
      val named_ax = [(b, ax)];
      val thy' = add named_ax thy;
      val thm = hd (get_axs thy' named_ax);
    in apfst hd (gen_add_thms (K I) [((b, thm), atts)] thy') end);
in
  val add_defs               = add_axm o Theory.add_defs_i false;
  val add_defs_unchecked     = add_axm o Theory.add_defs_i true;
  val add_axioms             = add_axm Theory.add_axioms_i;
  val add_defs_cmd           = add_axm o Theory.add_defs false;
  val add_defs_unchecked_cmd = add_axm o Theory.add_defs true;
  val add_axioms_cmd         = add_axm Theory.add_axioms;
end;



(*** Pure theory syntax and logical content ***)

val typ = SimpleSyntax.read_typ;
val term = SimpleSyntax.read_term;
val prop = SimpleSyntax.read_prop;

val typeT = Syntax.typeT;
val spropT = Syntax.spropT;


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
   [(Binding.name "fun", 2, NoSyn),
    (Binding.name "prop", 0, NoSyn),
    (Binding.name "itself", 1, NoSyn),
    (Binding.name "dummy", 0, NoSyn)]
  #> Sign.add_nonterminals (map Binding.name Syntax.basic_nonterms)
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
    ("",            typ "aprop => aprop",              Delimfix "'(_')"),
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
    ("_constify",   typ "float_token => float_const",  Delimfix "_"),
    ("_indexnum",   typ "num_const => index",          Delimfix "\\<^sub>_"),
    ("_index",      typ "logic => index",              Delimfix "(00\\<^bsub>_\\<^esub>)"),
    ("_indexdefault", typ "index",                     Delimfix ""),
    ("_indexvar",   typ "index",                       Delimfix "'\\<index>"),
    ("_struct",     typ "index => logic",              Mixfix ("\\<struct>_", [1000], 1000)),
    ("==>",         typ "prop => prop => prop",        Delimfix "op ==>"),
    (Term.dummy_patternN, typ "aprop",                 Delimfix "'_"),
    ("_sort_constraint", typ "type => prop",           Delimfix "(1SORT'_CONSTRAINT/(1'(_')))"),
    ("Pure.term",   typ "logic => prop",               Delimfix "TERM _"),
    ("Pure.conjunction", typ "prop => prop => prop",   InfixrName ("&&&", 2))]
  #> Sign.add_syntax_i applC_syntax
  #> Sign.add_modesyntax_i (Symbol.xsymbolsN, true)
   [("fun",      typ "type => type => type",   Mixfix ("(_/ \\<Rightarrow> _)", [1, 0], 0)),
    ("_bracket", typ "types => type => type",  Mixfix ("([_]/ \\<Rightarrow> _)", [0, 0], 0)),
    ("_ofsort",  typ "tid => sort => type",    Mixfix ("_\\<Colon>_", [1000, 0], 1000)),
    ("_constrain", typ "logic => type => logic", Mixfix ("_\\<Colon>_", [4, 0], 3)),
    ("_constrain", [spropT, typeT] ---> spropT, Mixfix ("_\\<Colon>_", [4, 0], 3)),
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
   [("prop", typ "prop => prop", Mixfix ("_", [0], 0))]
  #> Sign.add_modesyntax_i ("HTML", false)
   [("_lambda", typ "pttrns => 'a => logic", Mixfix ("(3\\<lambda>_./ _)", [0, 3], 3))]
  #> Sign.add_consts_i
   [(Binding.name "==", typ "'a => 'a => prop", InfixrName ("==", 2)),
    (Binding.name "==>", typ "prop => prop => prop", Mixfix ("(_/ ==> _)", [2, 1], 1)),
    (Binding.name "all", typ "('a => prop) => prop", Binder ("!!", 0, 0)),
    (Binding.name "prop", typ "prop => prop", NoSyn),
    (Binding.name "TYPE", typ "'a itself", NoSyn),
    (Binding.name Term.dummy_patternN, typ "'a", Delimfix "'_")]
  #> Theory.add_deps "==" ("==", typ "'a => 'a => prop") []
  #> Theory.add_deps "==>" ("==>", typ "prop => prop => prop") []
  #> Theory.add_deps "all" ("all", typ "('a => prop) => prop") []
  #> Theory.add_deps "TYPE" ("TYPE", typ "'a itself") []
  #> Theory.add_deps Term.dummy_patternN (Term.dummy_patternN, typ "'a") []
  #> Sign.add_trfuns Syntax.pure_trfuns
  #> Sign.add_trfunsT Syntax.pure_trfunsT
  #> Sign.local_path
  #> Sign.add_consts_i
   [(Binding.name "term", typ "'a => prop", NoSyn),
    (Binding.name "sort_constraint", typ "'a itself => prop", NoSyn),
    (Binding.name "conjunction", typ "prop => prop => prop", NoSyn)]
  #> (add_defs false o map Thm.no_attributes)
   [(Binding.name "prop_def", prop "(CONST prop :: prop => prop) (A::prop) == A::prop"),
    (Binding.name "term_def", prop "(CONST Pure.term :: 'a => prop) (x::'a) == (!!A::prop. A ==> A)"),
    (Binding.name "sort_constraint_def",
      prop "(CONST Pure.sort_constraint :: 'a itself => prop) (CONST TYPE :: 'a itself) ==\
      \ (CONST Pure.term :: 'a itself => prop) (CONST TYPE :: 'a itself)"),
    (Binding.name "conjunction_def", prop "(A &&& B) == (!!C::prop. (A ==> B ==> C) ==> C)")] #> snd
  #> Sign.hide_const false "Pure.term"
  #> Sign.hide_const false "Pure.sort_constraint"
  #> Sign.hide_const false "Pure.conjunction"
  #> add_thmss [((Binding.name "nothing", []), [])] #> snd
  #> Theory.add_axioms_i (map (apfst Binding.name) Proofterm.equality_axms)));

end;
