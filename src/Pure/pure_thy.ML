(*  Title:      Pure/pure_thy.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Theorem storage.  The ProtoPure theory.
*)

signature BASIC_PURE_THY =
sig
  datatype interval = FromTo of int * int | From of int | Single of int
  datatype thmref =
    Name of string |
    NameSelection of string * interval list |
    Fact of string
  val print_theorems: theory -> unit
  val print_theory: theory -> unit
  val get_thm: theory -> thmref -> thm
  val get_thms: theory -> thmref -> thm list
  val get_thmss: theory -> thmref list -> thm list
  val thm: xstring -> thm
  val thms: xstring -> thm list
  structure ProtoPure:
    sig
      val thy: theory
      val prop_def: thm
    end
end;

signature PURE_THY =
sig
  include BASIC_PURE_THY
  val map_tags: (tag list -> tag list) -> thm -> thm
  val tag_rule: tag -> thm -> thm
  val untag_rule: string -> thm -> thm
  val tag: tag -> attribute
  val untag: string -> attribute
  val get_kind: thm -> string
  val kind_rule: string -> thm -> thm
  val kind: string -> attribute
  val theoremK: string
  val lemmaK: string
  val corollaryK: string
  val internalK: string
  val kind_internal: attribute
  val has_internal: tag list -> bool
  val is_internal: thm -> bool
  val string_of_thmref: thmref -> string
  val print_theorems_diff: theory -> theory -> unit
  val get_thm_closure: theory -> thmref -> thm
  val get_thms_closure: theory -> thmref -> thm list
  val single_thm: string -> thm list -> thm
  val name_of_thmref: thmref -> string
  val map_name_of_thmref: (string -> string) -> thmref -> thmref
  val select_thm: thmref -> thm list -> thm list
  val selections: string * thm list -> (thmref * thm) list
  val theorems_of: theory -> thm list NameSpace.table
  val theorem_space: theory -> NameSpace.T
  val fact_index_of: theory -> FactIndex.T
  val valid_thms: theory -> thmref * thm list -> bool
  val thms_containing: theory -> FactIndex.spec -> (string * thm list) list
  val thms_containing_consts: theory -> string list -> (string * thm) list
  val thms_of: theory -> (string * thm) list
  val all_thms_of: theory -> (string * thm) list
  val hide_thms: bool -> string list -> theory -> theory
  val store_thm: (bstring * thm) * attribute list -> theory -> thm * theory
  val smart_store_thms: (bstring * thm list) -> thm list
  val smart_store_thms_open: (bstring * thm list) -> thm list
  val forall_elim_var: int -> thm -> thm
  val forall_elim_vars: int -> thm -> thm
  val name_multi: string -> 'a list -> (string * 'a) list
  val add_thms: ((bstring * thm) * attribute list) list -> theory -> thm list * theory
  val add_thmss: ((bstring * thm list) * attribute list) list -> theory -> thm list list * theory 
  val note_thmss: string -> ((bstring * attribute list) *
    (thmref * attribute list) list) list -> theory -> (bstring * thm list) list * theory
  val note_thmss_i: string -> ((bstring * attribute list) *
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
  val add_defss: bool -> ((bstring * string list) * attribute list) list ->
    theory -> thm list list * theory
  val add_defss_i: bool -> ((bstring * term list) * attribute list) list ->
    theory -> thm list list * theory
  val generic_setup: string option -> theory -> theory
  val add_oracle: bstring * string * string -> theory -> theory
end;

structure PureThy: PURE_THY =
struct


(*** theorem tags ***)

(* add / delete tags *)

fun map_tags f thm =
  Thm.put_name_tags (Thm.name_of_thm thm, f (#2 (Thm.get_name_tags thm))) thm;

fun tag_rule tg = map_tags (fn tgs => if tg mem tgs then tgs else tgs @ [tg]);
fun untag_rule s = map_tags (filter_out (equal s o #1));

fun tag tg x = Thm.rule_attribute (K (tag_rule tg)) x;
fun untag s x = Thm.rule_attribute (K (untag_rule s)) x;

fun simple_tag name x = tag (name, []) x;


(* theorem kinds *)

val theoremK = "theorem";
val lemmaK = "lemma";
val corollaryK = "corollary";
val internalK = "internal";

fun get_kind thm =
  (case AList.lookup (op =) ((#2 o Thm.get_name_tags) thm) "kind" of
    SOME (k :: _) => k
  | _ => "unknown");

fun kind_rule k = tag_rule ("kind", [k]) o untag_rule "kind";
fun kind k x = if k = "" then x else Thm.rule_attribute (K (kind_rule k)) x;
fun kind_internal x = kind internalK x;
fun has_internal tags = exists (fn ("kind", [k]) => k = internalK | _ => false) tags;
val is_internal = has_internal o Thm.tags_of_thm;



(*** theorem database ***)

(** dataype theorems **)

fun pretty_theorems_diff thy prev_thms (space, thms) =
  let
    val prt_thm = Display.pretty_thm_sg thy;
    fun prt_thms (name, [th]) =
          Pretty.block [Pretty.str (name ^ ":"), Pretty.brk 1, prt_thm th]
      | prt_thms (name, ths) = Pretty.big_list (name ^ ":") (map prt_thm ths);

    val diff_thmss = Symtab.fold (fn fact =>
      if not (Symtab.member eq_thms prev_thms fact) then cons fact else I) thms [];
    val thmss = diff_thmss |> map (apfst (NameSpace.extern space)) |> Library.sort_wrt #1;
  in Pretty.big_list "theorems:" (map prt_thms thmss) end;

fun pretty_theorems thy = pretty_theorems_diff thy Symtab.empty;

structure TheoremsData = TheoryDataFun
(struct
  val name = "Pure/theorems";
  type T =
   {theorems: thm list NameSpace.table,
    index: FactIndex.T} ref;

  fun mk_empty _ =
    ref {theorems = NameSpace.empty_table, index = FactIndex.empty}: T;

  val empty = mk_empty ();
  fun copy (ref x) = ref x;
  val extend = mk_empty;
  fun merge _ = mk_empty;
  fun print thy (ref {theorems, index}) = Pretty.writeln (pretty_theorems thy theorems);
end);

val get_theorems_ref = TheoremsData.get;
val get_theorems = ! o get_theorems_ref;
val theorems_of = #theorems o get_theorems;
val theorem_space = #1 o theorems_of;
val fact_index_of = #index o get_theorems;


(* print theory *)

val print_theorems = TheoremsData.print;

fun print_theorems_diff prev_thy thy =
  Pretty.writeln (pretty_theorems_diff thy
    (#2 (theorems_of prev_thy)) (#theorems (get_theorems thy)));

fun print_theory thy =
  Display.pretty_full_theory thy @
    [pretty_theorems thy (#theorems (get_theorems thy))]
  |> Pretty.chunks |> Pretty.writeln;



(** retrieve theorems **)

fun the_thms _ (SOME thms) = thms
  | the_thms name NONE = error ("Unknown theorem(s) " ^ quote name);

fun single_thm _ [thm] = thm
  | single_thm name _ = error ("Single theorem expected " ^ quote name);


(* datatype interval *)

datatype interval =
  FromTo of int * int |
  From of int |
  Single of int;

fun interval _ (FromTo (i, j)) = i upto j
  | interval n (From i) = i upto n
  | interval _ (Single i) = [i];

fun string_of_interval (FromTo (i, j)) = string_of_int i ^ "-" ^ string_of_int j
  | string_of_interval (From i) = string_of_int i ^ "-"
  | string_of_interval (Single i) = string_of_int i;


(* datatype thmref *)

datatype thmref =
  Name of string |
  NameSelection of string * interval list |
  Fact of string;

fun name_of_thmref (Name name) = name
  | name_of_thmref (NameSelection (name, _)) = name
  | name_of_thmref (Fact _) = error "Illegal literal fact";

fun map_name_of_thmref f (Name name) = Name (f name)
  | map_name_of_thmref f (NameSelection (name, is)) = NameSelection (f name, is)
  | map_name_of_thmref _ thmref = thmref;

fun string_of_thmref (Name name) = name
  | string_of_thmref (NameSelection (name, is)) =
      name ^ enclose "(" ")" (commas (map string_of_interval is))
  | string_of_thmref (Fact _) = error "Illegal literal fact";


(* select_thm *)

fun select_thm (Name _) thms = thms
  | select_thm (Fact _) thms = thms
  | select_thm (NameSelection (name, is)) thms =
      let
        val n = length thms;
        fun select i =
          if i < 1 orelse i > n then
            error ("Bad subscript " ^ string_of_int i ^ " for " ^
              quote name ^ " (length " ^ string_of_int n ^ ")")
          else List.nth (thms, i - 1);
      in map select (List.concat (map (interval n) is)) end;


(* selections *)

fun selections (name, [thm]) = [(Name name, thm)]
  | selections (name, thms) = (1 upto length thms, thms) |> ListPair.map (fn (i, thm) =>
      (NameSelection (name, [Single i]), thm));


(* get_thm(s)_closure -- statically scoped versions *)

(*beware of proper order of evaluation!*)

fun lookup_thms thy =
  let
    val thy_ref = Theory.self_ref thy;
    val (space, thms) = #theorems (get_theorems thy);
  in
    fn name =>
      Option.map (map (Thm.transfer (Theory.deref thy_ref)))     (*dynamic identity*)
      (Symtab.lookup thms (NameSpace.intern space name)) (*static content*)
  end;

fun get_thms_closure thy =
  let val closures = map lookup_thms (thy :: Theory.ancestors_of thy) in
    fn thmref =>
      let val name = name_of_thmref thmref;
      in select_thm thmref (the_thms name (get_first (fn f => f name) closures)) end
  end;

fun get_thm_closure thy =
  let val get = get_thms_closure thy
  in fn thmref => single_thm (name_of_thmref thmref) (get thmref) end;


(* get_thms etc. *)

fun get_thms theory thmref =
  let val name = name_of_thmref thmref in
    get_first (fn thy => lookup_thms thy name) (theory :: Theory.ancestors_of theory)
    |> the_thms name |> select_thm thmref |> map (Thm.transfer theory)
  end;

fun get_thmss thy thmrefs = List.concat (map (get_thms thy) thmrefs);
fun get_thm thy thmref = single_thm (name_of_thmref thmref) (get_thms thy thmref);

fun thm name = get_thm (the_context ()) (Name name);
fun thms name = get_thms (the_context ()) (Name name);


(* thms_containing etc. *)

fun valid_thms thy (thmref, ths) =
  (case try (get_thms thy) thmref of
    NONE => false
  | SOME ths' => Thm.eq_thms (ths, ths'));

fun thms_containing theory spec =
  (theory :: Theory.ancestors_of theory)
  |> map (fn thy =>
      FactIndex.find (fact_index_of thy) spec
      |> List.filter (fn (name, ths) => valid_thms theory (Name name, ths))
      |> gen_distinct (eq_fst (op =)))
  |> List.concat;

fun thms_containing_consts thy consts =
  thms_containing thy (consts, []) |> map #2 |> List.concat
  |> map (fn th => (Thm.name_of_thm th, th));


(* thms_of etc. *)

fun thms_of thy =
  let val thms = #2 (theorems_of thy)
  in map (fn th => (Thm.name_of_thm th, th)) (List.concat (map snd (Symtab.dest thms))) end;

fun all_thms_of thy = List.concat (map thms_of (thy :: Theory.ancestors_of thy));



(** store theorems **)                    (*DESTRUCTIVE*)

(* hiding -- affects current theory node only *)

fun hide_thms fully names thy =
  let
    val r as ref {theorems = (space, thms), index} = get_theorems_ref thy;
    val space' = fold (NameSpace.hide fully) names space;
  in r := {theorems = (space', thms), index = index}; thy end;


(* naming *)

fun gen_names _ len "" = replicate len ""
  | gen_names j len name = map (fn i => name ^ "_" ^ string_of_int i) (j + 1 upto j + len);

fun name_multi name [x] = [(name, x)]
  | name_multi name xs = gen_names 0 (length xs) name ~~ xs;

fun name_thm pre (name, thm) =
  if Thm.name_of_thm thm <> "" andalso pre then thm else Thm.name_thm (name, thm);

fun name_thms pre name xs = map (name_thm pre) (name_multi name xs);

fun name_thmss name xs =
  (case filter_out (null o fst) xs of
    [([x], z)] => [([name_thm true (name, x)], z)]
  | _ => fst (fold_map (fn (ys, z) => fn i =>
    ((map (name_thm true) (gen_names i (length ys) name ~~ ys), z), i + length ys)) xs 0));


(* enter_thms *)

fun warn_overwrite name = warning ("Replaced old copy of theorems " ^ quote name);
fun warn_same name = warning ("Theorem database already contains a copy of " ^ quote name);

fun enter_thms _ _ app_att ("", thms) thy = app_att (thy, thms) |> swap
  | enter_thms pre_name post_name app_att (bname, thms) thy =
      let
        val name = Sign.full_name thy bname;
        val (thy', thms') = apsnd (post_name name) (app_att (thy, pre_name name thms));
        val r as ref {theorems = (space, theorems), index} = get_theorems_ref thy';
        val space' = Sign.declare_name thy' name space;
        val theorems' = Symtab.update (name, thms') theorems;
        val index' = FactIndex.add_global (name, thms') index;
      in
        (case Symtab.lookup theorems name of
          NONE => ()
        | SOME thms'' =>
            if Thm.eq_thms (thms', thms'') then warn_same name
            else warn_overwrite name);
        r := {theorems = (space', theorems'), index = index'};
        (thms', thy')
      end;


(* add_thms(s) *)

fun add_thms_atts pre_name ((bname, thms), atts) =
  enter_thms pre_name (name_thms false) (foldl_map (Thm.theory_attributes atts)) (bname, thms);

fun gen_add_thmss pre_name =
  fold_map (add_thms_atts pre_name);

fun gen_add_thms pre_name args =
  apfst (map hd) o gen_add_thmss pre_name (map (apfst (apsnd single)) args);

val add_thmss = gen_add_thmss (name_thms true);
val add_thms = gen_add_thms (name_thms true);


(* note_thmss(_i) *)

local

fun gen_note_thmss get k = fold_map (fn ((bname, more_atts), ths_atts) => fn thy =>
  let
    fun app (x, (ths, atts)) = foldl_map (Thm.theory_attributes atts) (x, ths);
    val (thms, thy') = thy |> enter_thms
      name_thmss (name_thms false) (apsnd List.concat o foldl_map app)
      (bname, map (fn (ths, atts) => (get thy ths, atts @ more_atts @ [kind k])) ths_atts);
  in ((bname, thms), thy') end);

in

val note_thmss = gen_note_thmss get_thms;
val note_thmss_i = gen_note_thmss (K I);

fun note_thmss_qualified k path facts thy =
  thy
  |> Theory.add_path path
  |> Theory.no_base_names
  |> note_thmss_i k facts
  ||> Theory.restore_naming thy;

end;


(* store_thm *)

fun store_thm ((bname, thm), atts) thy =
  let val ([th'], thy') = add_thms_atts (name_thms true) ((bname, [thm]), atts) thy
  in (th', thy') end;


(* smart_store_thms(_open) *)

local

fun smart_store _ (name, []) =
      error ("Cannot store empty list of theorems: " ^ quote name)
  | smart_store name_thm (name, [thm]) =
      fst (enter_thms (name_thm true) (name_thm false) I (name, [thm]) (Thm.theory_of_thm thm))
  | smart_store name_thm (name, thms) =
      let
        fun merge (thy, th) = Theory.merge (thy, Thm.theory_of_thm th);
        val thy = Library.foldl merge (Thm.theory_of_thm (hd thms), tl thms);
      in fst (enter_thms (name_thm true) (name_thm false) I (name, thms) thy) end;

in

val smart_store_thms = smart_store name_thms;
val smart_store_thms_open = smart_store (K (K I));

end;


(* forall_elim_var(s) -- belongs to drule.ML *)

fun forall_elim_vars_aux strip_vars i th =
  let
    val {thy, tpairs, prop, ...} = Thm.rep_thm th;
    val add_used = Term.fold_aterms
      (fn Var ((x, j), _) => if i = j then curry (op ins_string) x else I | _ => I);
    val used = fold (fn (t, u) => add_used t o add_used u) tpairs (add_used prop []);
    val vars = strip_vars prop;
    val cvars = (Term.variantlist (map #1 vars, used), vars)
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
  val add_axioms    = add_singles Theory.add_axioms;
  val add_axioms_i  = add_singles Theory.add_axioms_i;
  val add_axiomss   = add_multis Theory.add_axioms;
  val add_axiomss_i = add_multis Theory.add_axioms_i;
  val add_defs      = add_singles o Theory.add_defs;
  val add_defs_i    = add_singles o Theory.add_defs_i;
  val add_defss     = add_multis o Theory.add_defs;
  val add_defss_i   = add_multis o Theory.add_defs_i;
end;



(*** ML setup ***)

(* generic_setup *)

fun generic_setup NONE = (fn thy => thy |> Context.setup ())
  | generic_setup (SOME txt) = Context.use_let "val setup: theory -> theory" "setup" txt;


(* add_oracle *)

fun add_oracle (name, T, oracle) =
  let val txt =
    "local\n\
    \  type T = " ^ T ^ ";\n\
    \  val oracle: theory -> T -> term = " ^ oracle ^ ";\n\
    \  val name = " ^ quote name ^ ";\n\
    \  exception Arg of T;\n\
    \  val _ = Context.>> (Theory.add_oracle (name, fn (thy, Arg x) => oracle thy x));\n\
    \  val thy = Context.the_context ();\n\
    \  val invoke_" ^ name ^ " = Thm.invoke_oracle_i thy (Sign.full_name thy name);\n\
    \in\n\
    \  fun " ^ name ^ " thy x = invoke_" ^ name ^ " (thy, Arg x);\n\
    \end;\n";
  in Context.use_mltext_theory txt false end;



(*** the ProtoPure theory ***)

val aT = TFree ("'a", []);
val A = Free ("A", propT);

val proto_pure =
  Context.pre_pure_thy
  |> Compress.init_data
  |> Sign.init_data
  |> Theory.init_data
  |> Proofterm.init_data
  |> TheoremsData.init
  |> Theory.add_types
   [("fun", 2, NoSyn),
    ("prop", 0, NoSyn),
    ("itself", 1, NoSyn),
    ("dummy", 0, NoSyn)]
  |> Theory.add_nonterminals Syntax.basic_nonterms
  |> Theory.add_syntax
   [("_lambda",     "[pttrns, 'a] => logic",     Mixfix ("(3%_./ _)", [0, 3], 3)),
    ("_abs",        "'a",                        NoSyn),
    ("",            "'a => args",                Delimfix "_"),
    ("_args",       "['a, args] => args",        Delimfix "_,/ _"),
    ("",            "id => idt",                 Delimfix "_"),
    ("_idtdummy",   "idt",                       Delimfix "'_"),
    ("_idtyp",      "[id, type] => idt",         Mixfix ("_::_", [], 0)),
    ("_idtypdummy", "type => idt",               Mixfix ("'_()::_", [], 0)),
    ("",            "idt => idt",                Delimfix "'(_')"),
    ("",            "idt => idts",               Delimfix "_"),
    ("_idts",       "[idt, idts] => idts",       Mixfix ("_/ _", [1, 0], 0)),
    ("",            "idt => pttrn",              Delimfix "_"),
    ("",            "pttrn => pttrns",           Delimfix "_"),
    ("_pttrns",     "[pttrn, pttrns] => pttrns", Mixfix ("_/ _", [1, 0], 0)),
    ("",            "id => aprop",               Delimfix "_"),
    ("",            "longid => aprop",           Delimfix "_"),
    ("",            "var => aprop",              Delimfix "_"),
    ("_DDDOT",      "aprop",                     Delimfix "..."),
    ("_aprop",      "aprop => prop",             Delimfix "PROP _"),
    ("_asm",        "prop => asms",              Delimfix "_"),
    ("_asms",       "[prop, asms] => asms",      Delimfix "_;/ _"),
    ("_bigimpl",    "[asms, prop] => prop",      Mixfix ("((3[| _ |])/ ==> _)", [0, 1], 1)),
    ("_ofclass",    "[type, logic] => prop",     Delimfix "(1OFCLASS/(1'(_,/ _')))"),
    ("_mk_ofclass", "_",                         NoSyn),
    ("_TYPE",       "type => logic",             Delimfix "(1TYPE/(1'(_')))"),
    ("",            "id => logic",               Delimfix "_"),
    ("",            "longid => logic",           Delimfix "_"),
    ("",            "var => logic",              Delimfix "_"),
    ("_DDDOT",      "logic",                     Delimfix "..."),
    ("_constify",   "num => num_const",          Delimfix "_"),
    ("_indexnum",   "num_const => index",        Delimfix "\\<^sub>_"),
    ("_index",      "logic => index",            Delimfix "(00\\<^bsub>_\\<^esub>)"),
    ("_indexdefault", "index",                   Delimfix ""),
    ("_indexvar",   "index",                     Delimfix "'\\<index>"),
    ("_struct",     "index => logic",            Mixfix ("\\<struct>_", [1000], 1000)),
    ("==>",         "prop => prop => prop",      Delimfix "op ==>"),
    (Term.dummy_patternN, "aprop",               Delimfix "'_")]
  |> Theory.add_syntax Syntax.appl_syntax
  |> Theory.add_modesyntax (Symbol.xsymbolsN, true)
   [("fun",      "[type, type] => type",  Mixfix ("(_/ \\<Rightarrow> _)", [1, 0], 0)),
    ("_bracket", "[types, type] => type", Mixfix ("([_]/ \\<Rightarrow> _)", [0, 0], 0)),
    ("_ofsort",  "[tid, sort] => type",   Mixfix ("_\\<Colon>_", [1000, 0], 1000)),
    ("_constrain", "['a, type] => 'a",    Mixfix ("_\\<Colon>_", [4, 0], 3)),
    ("_idtyp",   "[id, type] => idt",     Mixfix ("_\\<Colon>_", [], 0)),
    ("_idtypdummy", "type => idt",        Mixfix ("'_()\\<Colon>_", [], 0)),
    ("_lambda",  "[pttrns, 'a] => logic", Mixfix ("(3\\<lambda>_./ _)", [0, 3], 3)),
    ("==",       "['a, 'a] => prop",      InfixrName ("\\<equiv>", 2)),
    ("!!",       "[idts, prop] => prop",  Mixfix ("(3\\<And>_./ _)", [0, 0], 0)),
    ("==>",      "[prop, prop] => prop",  InfixrName ("\\<Longrightarrow>", 1)),
    ("_DDDOT",   "aprop",                 Delimfix "\\<dots>"),
    ("_bigimpl", "[asms, prop] => prop",  Mixfix ("((1\\<lbrakk>_\\<rbrakk>)/ \\<Longrightarrow> _)", [0, 1], 1)),
    ("_DDDOT",   "logic",                 Delimfix "\\<dots>")]
  |> Theory.add_modesyntax ("", false)
   [("prop", "prop => prop", Mixfix ("_", [0], 0)),
    ("_meta_conjunction", "prop => prop => prop", InfixrName ("&&", 2))]
  |> Theory.add_modesyntax ("HTML", false)
   [("_lambda",  "[pttrns, 'a] => logic", Mixfix ("(3\\<lambda>_./ _)", [0, 3], 3))]
  |> Theory.add_consts
   [("==", "'a => 'a => prop", InfixrName ("==", 2)),
    ("==>", "prop => prop => prop", Mixfix ("(_/ ==> _)", [2, 1], 1)),
    ("all", "('a => prop) => prop", Binder ("!!", 0, 0)),
    ("prop", "prop => prop", NoSyn),
    ("TYPE", "'a itself", NoSyn),
    (Term.dummy_patternN, "'a", Delimfix "'_")]
  |> Theory.add_finals_i false
    [Const ("==", [aT, aT] ---> propT),
     Const ("==>", [propT, propT] ---> propT),
     Const ("all", (aT --> propT) --> propT),
     Const ("TYPE", a_itselfT),
     Const (Term.dummy_patternN, aT)]
  |> Theory.add_trfuns Syntax.pure_trfuns
  |> Theory.add_trfunsT Syntax.pure_trfunsT
  |> Sign.local_path
  |> (add_defs_i false o map Thm.no_attributes)
       [("prop_def", Logic.mk_equals (Logic.protect A, A))] |> snd
  |> add_thmss [(("nothing", []), [])] |> snd
  |> Theory.add_axioms_i Proofterm.equality_axms
  |> Theory.end_theory;

structure ProtoPure =
struct
  val thy = proto_pure;
  val prop_def = get_axiom thy "prop_def";
end;

end;

structure BasicPureThy: BASIC_PURE_THY = PureThy;
open BasicPureThy;
