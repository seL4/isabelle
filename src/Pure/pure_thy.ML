(*  Title:      Pure/pure_thy.ML
    Author:     Markus Wenzel, TU Muenchen

Pure theory syntax and further logical content.
*)

signature PURE_THY =
sig
  val old_appl_syntax: theory -> bool
  val old_appl_syntax_setup: theory -> theory
  val token_markers: string list
end;

structure Pure_Thy: PURE_THY =
struct

(* auxiliary *)

val typ = Simple_Syntax.read_typ;
val prop = Simple_Syntax.read_prop;

val tycon = Lexicon.mark_type;
val const = Lexicon.mark_const;

val qualify = Binding.qualify true Context.PureN;

fun mixfix (sy, ps, p) = Mixfix (Input.string sy, ps, p, Position.no_range);
fun infix_ (sy, p) = Infix (Input.string sy, p, Position.no_range);
fun infixr_ (sy, p) = Infixr (Input.string sy, p, Position.no_range);
fun binder (sy, p, q) = Binder (Input.string sy, p, q, Position.no_range);


(* application syntax variants *)

val appl_syntax =
 [("_appl", typ "('b \<Rightarrow> 'a) \<Rightarrow> args \<Rightarrow> logic", mixfix ("(1_/(1'(_')))", [1000, 0], 1000)),
  ("_appl", typ "('b \<Rightarrow> 'a) \<Rightarrow> args \<Rightarrow> aprop", mixfix ("(1_/(1'(_')))", [1000, 0], 1000))];

val applC_syntax =
 [("",       typ "'a \<Rightarrow> cargs",                  Mixfix.mixfix "_"),
  ("_cargs", typ "'a \<Rightarrow> cargs \<Rightarrow> cargs",         mixfix ("_/ _", [1000, 1000], 1000)),
  ("_applC", typ "('b \<Rightarrow> 'a) \<Rightarrow> cargs \<Rightarrow> logic", mixfix ("(1_/ _)", [1000, 1000], 999)),
  ("_applC", typ "('b \<Rightarrow> 'a) \<Rightarrow> cargs \<Rightarrow> aprop", mixfix ("(1_/ _)", [1000, 1000], 999))];

structure Old_Appl_Syntax = Theory_Data
(
  type T = bool;
  val empty = false;
  val extend = I;
  fun merge (b1, b2) : T =
    if b1 = b2 then b1
    else error "Cannot merge theories with different application syntax";
);

val old_appl_syntax = Old_Appl_Syntax.get;

val old_appl_syntax_setup =
  Old_Appl_Syntax.put true #>
  Sign.syntax false Syntax.mode_default applC_syntax #>
  Sign.syntax true Syntax.mode_default appl_syntax;


(* main content *)

val token_markers =
  ["_tfree", "_tvar", "_free", "_bound", "_loose", "_var", "_numeral", "_inner_string"];

val _ = Theory.setup
  (Sign.init_naming #>
   Old_Appl_Syntax.put false #>
   Sign.add_types_global
   [(Binding.make ("fun", \<^here>), 2, NoSyn),
    (Binding.make ("prop", \<^here>), 0, NoSyn),
    (Binding.make ("itself", \<^here>), 1, NoSyn),
    (Binding.make ("dummy", \<^here>), 0, NoSyn),
    (qualify (Binding.make ("proof", \<^here>)), 0, NoSyn)]
  #> Theory.add_deps_type "fun"
  #> Theory.add_deps_type "prop"
  #> Theory.add_deps_type "itself"
  #> Theory.add_deps_type "dummy"
  #> Theory.add_deps_type "Pure.proof"
  #> Sign.add_nonterminals_global
    (map (fn name => Binding.make (name, \<^here>))
      (Lexicon.terminals @ ["logic", "type", "types", "sort", "classes",
        "args", "cargs", "pttrn", "pttrns", "idt", "idts", "aprop", "asms",
        "any", "prop'", "num_const", "float_const", "num_position",
        "float_position", "index", "struct", "tid_position",
        "tvar_position", "id_position", "longid_position", "var_position",
        "str_position", "string_position", "cartouche_position", "type_name",
        "class_name"]))
  #> Sign.syntax true Syntax.mode_default (map (fn x => (x, typ "'a", NoSyn)) token_markers)
  #> Sign.syntax true Syntax.mode_default
   [("",            typ "prop' \<Rightarrow> prop",               Mixfix.mixfix "_"),
    ("",            typ "logic \<Rightarrow> any",                Mixfix.mixfix "_"),
    ("",            typ "prop' \<Rightarrow> any",                Mixfix.mixfix "_"),
    ("",            typ "logic \<Rightarrow> logic",              Mixfix.mixfix "'(_')"),
    ("",            typ "prop' \<Rightarrow> prop'",              Mixfix.mixfix "'(_')"),
    ("_constrain",  typ "logic \<Rightarrow> type \<Rightarrow> logic",      mixfix ("_::_", [4, 0], 3)),
    ("_constrain",  typ "prop' \<Rightarrow> type \<Rightarrow> prop'",      mixfix ("_::_", [4, 0], 3)),
    ("_ignore_type", typ "'a",                         NoSyn),
    ("",            typ "tid_position \<Rightarrow> type",        Mixfix.mixfix "_"),
    ("",            typ "tvar_position \<Rightarrow> type",       Mixfix.mixfix "_"),
    ("",            typ "type_name \<Rightarrow> type",           Mixfix.mixfix "_"),
    ("_type_name",  typ "id \<Rightarrow> type_name",             Mixfix.mixfix "_"),
    ("_type_name",  typ "longid \<Rightarrow> type_name",         Mixfix.mixfix "_"),
    ("_ofsort",     typ "tid_position \<Rightarrow> sort \<Rightarrow> type", mixfix ("_::_", [1000, 0], 1000)),
    ("_ofsort",     typ "tvar_position \<Rightarrow> sort \<Rightarrow> type", mixfix ("_::_", [1000, 0], 1000)),
    ("_dummy_ofsort", typ "sort \<Rightarrow> type",              mixfix ("'_' ::_", [0], 1000)),
    ("",            typ "class_name \<Rightarrow> sort",          Mixfix.mixfix "_"),
    ("_class_name", typ "id \<Rightarrow> class_name",            Mixfix.mixfix "_"),
    ("_class_name", typ "longid \<Rightarrow> class_name",        Mixfix.mixfix "_"),
    ("_dummy_sort", typ "sort",                        Mixfix.mixfix "'_"),
    ("_topsort",    typ "sort",                        Mixfix.mixfix "{}"),
    ("_sort",       typ "classes \<Rightarrow> sort",             Mixfix.mixfix "{_}"),
    ("",            typ "class_name \<Rightarrow> classes",       Mixfix.mixfix "_"),
    ("_classes",    typ "class_name \<Rightarrow> classes \<Rightarrow> classes", Mixfix.mixfix "_,_"),
    ("_tapp",       typ "type \<Rightarrow> type_name \<Rightarrow> type",   mixfix ("_ _", [1000, 0], 1000)),
    ("_tappl",      typ "type \<Rightarrow> types \<Rightarrow> type_name \<Rightarrow> type", Mixfix.mixfix "((1'(_,/ _')) _)"),
    ("",            typ "type \<Rightarrow> types",               Mixfix.mixfix "_"),
    ("_types",      typ "type \<Rightarrow> types \<Rightarrow> types",      Mixfix.mixfix "_,/ _"),
    ("\<^type>fun", typ "type \<Rightarrow> type \<Rightarrow> type",        mixfix ("(_/ \<Rightarrow> _)", [1, 0], 0)),
    ("_bracket",    typ "types \<Rightarrow> type \<Rightarrow> type",       mixfix ("([_]/ \<Rightarrow> _)", [0, 0], 0)),
    ("",            typ "type \<Rightarrow> type",                Mixfix.mixfix "'(_')"),
    ("\<^type>dummy", typ "type",                      Mixfix.mixfix "'_"),
    ("_type_prop",  typ "'a",                          NoSyn),
    ("_lambda",     typ "pttrns \<Rightarrow> 'a \<Rightarrow> logic",       mixfix ("(3\<lambda>_./ _)", [0, 3], 3)),
    ("_abs",        typ "'a",                          NoSyn),
    ("",            typ "'a \<Rightarrow> args",                  Mixfix.mixfix "_"),
    ("_args",       typ "'a \<Rightarrow> args \<Rightarrow> args",          Mixfix.mixfix "_,/ _"),
    ("",            typ "id_position \<Rightarrow> idt",          Mixfix.mixfix "_"),
    ("_idtdummy",   typ "idt",                         Mixfix.mixfix "'_"),
    ("_idtyp",      typ "id_position \<Rightarrow> type \<Rightarrow> idt",  mixfix ("_::_", [], 0)),
    ("_idtypdummy", typ "type \<Rightarrow> idt",                 mixfix ("'_' ::_", [], 0)),
    ("",            typ "idt \<Rightarrow> idt",                  Mixfix.mixfix "'(_')"),
    ("",            typ "idt \<Rightarrow> idts",                 Mixfix.mixfix "_"),
    ("_idts",       typ "idt \<Rightarrow> idts \<Rightarrow> idts",         mixfix ("_/ _", [1, 0], 0)),
    ("",            typ "idt \<Rightarrow> pttrn",                Mixfix.mixfix "_"),
    ("",            typ "pttrn \<Rightarrow> pttrns",             Mixfix.mixfix "_"),
    ("_pttrns",     typ "pttrn \<Rightarrow> pttrns \<Rightarrow> pttrns",   mixfix ("_/ _", [1, 0], 0)),
    ("",            typ "aprop \<Rightarrow> aprop",              Mixfix.mixfix "'(_')"),
    ("",            typ "id_position \<Rightarrow> aprop",        Mixfix.mixfix "_"),
    ("",            typ "longid_position \<Rightarrow> aprop",    Mixfix.mixfix "_"),
    ("",            typ "var_position \<Rightarrow> aprop",       Mixfix.mixfix "_"),
    ("_DDDOT",      typ "aprop",                       Mixfix.mixfix "\<dots>"),
    ("_aprop",      typ "aprop \<Rightarrow> prop",               Mixfix.mixfix "PROP _"),
    ("_asm",        typ "prop \<Rightarrow> asms",                Mixfix.mixfix "_"),
    ("_asms",       typ "prop \<Rightarrow> asms \<Rightarrow> asms",        Mixfix.mixfix "_;/ _"),
    ("_bigimpl",    typ "asms \<Rightarrow> prop \<Rightarrow> prop",        mixfix ("((1\<lbrakk>_\<rbrakk>)/ \<Longrightarrow> _)", [0, 1], 1)),
    ("_ofclass",    typ "type \<Rightarrow> logic \<Rightarrow> prop",       Mixfix.mixfix "(1OFCLASS/(1'(_,/ _')))"),
    ("_mk_ofclass", typ "dummy",                       NoSyn),
    ("_TYPE",       typ "type \<Rightarrow> logic",               Mixfix.mixfix "(1TYPE/(1'(_')))"),
    ("",            typ "id_position \<Rightarrow> logic",        Mixfix.mixfix "_"),
    ("",            typ "longid_position \<Rightarrow> logic",    Mixfix.mixfix "_"),
    ("",            typ "var_position \<Rightarrow> logic",       Mixfix.mixfix "_"),
    ("_DDDOT",      typ "logic",                       Mixfix.mixfix "\<dots>"),
    ("_strip_positions", typ "'a", NoSyn),
    ("_position",   typ "num_token \<Rightarrow> num_position",   Mixfix.mixfix "_"),
    ("_position",   typ "float_token \<Rightarrow> float_position", Mixfix.mixfix "_"),
    ("_constify",   typ "num_position \<Rightarrow> num_const",   Mixfix.mixfix "_"),
    ("_constify",   typ "float_position \<Rightarrow> float_const", Mixfix.mixfix "_"),
    ("_index",      typ "logic \<Rightarrow> index",              Mixfix.mixfix "(\<open>unbreakable\<close>\<^bsub>_\<^esub>)"),
    ("_indexdefault", typ "index",                     Mixfix.mixfix ""),
    ("_indexvar",   typ "index",                       Mixfix.mixfix "'\<index>"),
    ("_struct",     typ "index \<Rightarrow> logic",              NoSyn),
    ("_update_name", typ "idt",                        NoSyn),
    ("_constrainAbs", typ "'a",                        NoSyn),
    ("_position_sort", typ "tid \<Rightarrow> tid_position",      Mixfix.mixfix "_"),
    ("_position_sort", typ "tvar \<Rightarrow> tvar_position",    Mixfix.mixfix "_"),
    ("_position",   typ "id \<Rightarrow> id_position",           Mixfix.mixfix "_"),
    ("_position",   typ "longid \<Rightarrow> longid_position",   Mixfix.mixfix "_"),
    ("_position",   typ "var \<Rightarrow> var_position",         Mixfix.mixfix "_"),
    ("_position",   typ "str_token \<Rightarrow> str_position",   Mixfix.mixfix "_"),
    ("_position",   typ "string_token \<Rightarrow> string_position", Mixfix.mixfix "_"),
    ("_position",   typ "cartouche \<Rightarrow> cartouche_position", Mixfix.mixfix "_"),
    ("_type_constraint_", typ "'a",                    NoSyn),
    ("_context_const", typ "id_position \<Rightarrow> logic",     Mixfix.mixfix "CONST _"),
    ("_context_const", typ "id_position \<Rightarrow> aprop",     Mixfix.mixfix "CONST _"),
    ("_context_const", typ "longid_position \<Rightarrow> logic", Mixfix.mixfix "CONST _"),
    ("_context_const", typ "longid_position \<Rightarrow> aprop", Mixfix.mixfix "CONST _"),
    ("_context_xconst", typ "id_position \<Rightarrow> logic",    Mixfix.mixfix "XCONST _"),
    ("_context_xconst", typ "id_position \<Rightarrow> aprop",    Mixfix.mixfix "XCONST _"),
    ("_context_xconst", typ "longid_position \<Rightarrow> logic", Mixfix.mixfix "XCONST _"),
    ("_context_xconst", typ "longid_position \<Rightarrow> aprop", Mixfix.mixfix "XCONST _"),
    (const "Pure.dummy_pattern", typ "aprop",          Mixfix.mixfix "'_"),
    ("_sort_constraint", typ "type \<Rightarrow> prop",           Mixfix.mixfix "(1SORT'_CONSTRAINT/(1'(_')))"),
    (const "Pure.term", typ "logic \<Rightarrow> prop",           Mixfix.mixfix "TERM _"),
    (const "Pure.conjunction", typ "prop \<Rightarrow> prop \<Rightarrow> prop", infixr_ ("&&&", 2))]
  #> Sign.syntax true Syntax.mode_default applC_syntax
  #> Sign.syntax true (Print_Mode.ASCII, true)
   [(tycon "fun",         typ "type \<Rightarrow> type \<Rightarrow> type",   mixfix ("(_/ => _)", [1, 0], 0)),
    ("_bracket",          typ "types \<Rightarrow> type \<Rightarrow> type",  mixfix ("([_]/ => _)", [0, 0], 0)),
    ("_lambda",           typ "pttrns \<Rightarrow> 'a \<Rightarrow> logic",  mixfix ("(3%_./ _)", [0, 3], 3)),
    (const "Pure.eq",     typ "'a \<Rightarrow> 'a \<Rightarrow> prop",       infix_ ("==", 2)),
    (const "Pure.all_binder", typ "idts \<Rightarrow> prop \<Rightarrow> prop", mixfix ("(3!!_./ _)", [0, 0], 0)),
    (const "Pure.imp",    typ "prop \<Rightarrow> prop \<Rightarrow> prop",   infixr_ ("==>", 1)),
    ("_DDDOT",            typ "aprop",                  Mixfix.mixfix "..."),
    ("_bigimpl",          typ "asms \<Rightarrow> prop \<Rightarrow> prop",   mixfix ("((3[| _ |])/ ==> _)", [0, 1], 1)),
    ("_DDDOT",            typ "logic",                  Mixfix.mixfix "...")]
  #> Sign.syntax true ("", false)
   [(const "Pure.prop", typ "prop \<Rightarrow> prop", mixfix ("_", [0], 0))]
  #> Sign.add_consts
   [(qualify (Binding.make ("eq", \<^here>)), typ "'a \<Rightarrow> 'a \<Rightarrow> prop", infix_ ("\<equiv>", 2)),
    (qualify (Binding.make ("imp", \<^here>)), typ "prop \<Rightarrow> prop \<Rightarrow> prop", infixr_ ("\<Longrightarrow>", 1)),
    (qualify (Binding.make ("all", \<^here>)), typ "('a \<Rightarrow> prop) \<Rightarrow> prop", binder ("\<And>", 0, 0)),
    (qualify (Binding.make ("prop", \<^here>)), typ "prop \<Rightarrow> prop", NoSyn),
    (qualify (Binding.make ("type", \<^here>)), typ "'a itself", NoSyn),
    (qualify (Binding.make ("dummy_pattern", \<^here>)), typ "'a", Mixfix.mixfix "'_"),
    (qualify (Binding.make ("Appt", \<^here>)), typ "Pure.proof \<Rightarrow> 'a \<Rightarrow> Pure.proof", NoSyn),
    (qualify (Binding.make ("AppP", \<^here>)), typ "Pure.proof \<Rightarrow> Pure.proof \<Rightarrow> Pure.proof", NoSyn),
    (qualify (Binding.make ("Abst", \<^here>)), typ "('a \<Rightarrow> Pure.proof) \<Rightarrow> Pure.proof", NoSyn),
    (qualify (Binding.make ("AbsP", \<^here>)), typ "prop \<Rightarrow> (Pure.proof \<Rightarrow> Pure.proof) \<Rightarrow> Pure.proof", NoSyn),
    (qualify (Binding.make ("Hyp", \<^here>)), typ "prop \<Rightarrow> Pure.proof", NoSyn),
    (qualify (Binding.make ("Oracle", \<^here>)), typ "prop \<Rightarrow> Pure.proof", NoSyn),
    (qualify (Binding.make ("PClass", \<^here>)), typ "('a itself \<Rightarrow> prop) \<Rightarrow> Pure.proof", NoSyn),
    (qualify (Binding.make ("MinProof", \<^here>)), typ "Pure.proof", NoSyn)]
  #> Theory.add_deps_const "Pure.eq"
  #> Theory.add_deps_const "Pure.imp"
  #> Theory.add_deps_const "Pure.all"
  #> Theory.add_deps_const "Pure.type"
  #> Theory.add_deps_const "Pure.dummy_pattern"
  #> Sign.parse_ast_translation Syntax_Trans.pure_parse_ast_translation
  #> Sign.parse_translation Syntax_Trans.pure_parse_translation
  #> Sign.print_ast_translation Syntax_Trans.pure_print_ast_translation
  #> Sign.add_consts
   [(qualify (Binding.make ("term", \<^here>)), typ "'a \<Rightarrow> prop", NoSyn),
    (qualify (Binding.make ("sort_constraint", \<^here>)), typ "'a itself \<Rightarrow> prop", NoSyn),
    (qualify (Binding.make ("conjunction", \<^here>)), typ "prop \<Rightarrow> prop \<Rightarrow> prop", NoSyn)]
  #> Sign.local_path
  #> (Global_Theory.add_defs false o map Thm.no_attributes)
   [(Binding.make ("prop_def", \<^here>),
      prop "(CONST Pure.prop :: prop \<Rightarrow> prop) (A::prop) \<equiv> A::prop"),
    (Binding.make ("term_def", \<^here>),
      prop "(CONST Pure.term :: 'a \<Rightarrow> prop) (x::'a) \<equiv> (\<And>A::prop. A \<Longrightarrow> A)"),
    (Binding.make ("sort_constraint_def", \<^here>),
      prop "(CONST Pure.sort_constraint :: 'a itself \<Rightarrow> prop) (CONST Pure.type :: 'a itself) \<equiv>\
      \ (CONST Pure.term :: 'a itself \<Rightarrow> prop) (CONST Pure.type :: 'a itself)"),
    (Binding.make ("conjunction_def", \<^here>),
      prop "(A &&& B) \<equiv> (\<And>C::prop. (A \<Longrightarrow> B \<Longrightarrow> C) \<Longrightarrow> C)")] #> snd
  #> fold (fn (a, prop) =>
      snd o Thm.add_axiom_global (Binding.make (a, \<^here>), prop)) Proofterm.equality_axms);

end;
