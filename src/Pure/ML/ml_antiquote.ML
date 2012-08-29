(*  Title:      Pure/ML/ml_antiquote.ML
    Author:     Makarius

Common ML antiquotations.
*)

signature ML_ANTIQUOTE =
sig
  val variant: string -> Proof.context -> string * Proof.context
  val macro: binding -> Proof.context context_parser -> theory -> theory
  val inline: binding -> string context_parser -> theory -> theory
  val declaration: string -> binding -> string context_parser -> theory -> theory
  val value: binding -> string context_parser -> theory -> theory
end;

structure ML_Antiquote: ML_ANTIQUOTE =
struct

(** generic tools **)

(* ML names *)

val init_context = ML_Syntax.reserved |> Name.declare "ML_context";

structure Names = Proof_Data
(
  type T = Name.context;
  fun init _ = init_context;
);

fun variant a ctxt =
  let
    val names = Names.get ctxt;
    val (b, names') = Name.variant a names;
    val ctxt' = Names.put names' ctxt;
  in (b, ctxt') end;


(* specific antiquotations *)

fun macro name scan = ML_Context.add_antiq name
  (fn _ => scan :|-- (fn ctxt => Scan.depend (fn _ => Scan.succeed
    (Context.Proof ctxt, fn background => (K ("", ""), background)))));

fun inline name scan = ML_Context.add_antiq name
  (fn _ => scan >> (fn s => fn background => (K ("", s), background)));

fun declaration kind name scan = ML_Context.add_antiq name
  (fn _ => scan >> (fn s => fn background =>
    let
      val (a, background') =
        variant (translate_string (fn "." => "_" | c => c) (Binding.name_of name)) background;
      val env = kind ^ " " ^ a ^ " = " ^ s ^ ";\n";
      val body = "Isabelle." ^ a;
    in (K (env, body), background') end));

val value = declaration "val";



(** misc antiquotations **)

val _ = Context.>> (Context.map_theory

 (inline (Binding.name "assert")
    (Scan.succeed "(fn b => if b then () else raise General.Fail \"Assertion failed\")") #>

  inline (Binding.name "make_string") (Scan.succeed ml_make_string) #>

  value (Binding.name "binding")
    (Scan.lift (Parse.position Args.name) >> ML_Syntax.make_binding) #>

  value (Binding.name "theory")
    (Args.theory -- Scan.lift (Parse.position Args.name) >> (fn (thy, (name, pos)) =>
      (Position.report pos (Theory.get_markup (Context.get_theory thy name));
        "Context.get_theory (Proof_Context.theory_of ML_context) " ^ ML_Syntax.print_string name))
    || Scan.succeed "Proof_Context.theory_of ML_context") #>

  inline (Binding.name "context") (Scan.succeed "Isabelle.ML_context") #>

  inline (Binding.name "typ") (Args.typ >> (ML_Syntax.atomic o ML_Syntax.print_typ)) #>
  inline (Binding.name "term") (Args.term >> (ML_Syntax.atomic o ML_Syntax.print_term)) #>
  inline (Binding.name "prop") (Args.prop >> (ML_Syntax.atomic o ML_Syntax.print_term)) #>

  macro (Binding.name "let")
    (Args.context --
      Scan.lift
        (Parse.and_list1 (Parse.and_list1 Args.name_source -- (Args.$$$ "=" |-- Args.name_source)))
        >> (fn (ctxt, args) => #2 (Proof_Context.match_bind true args ctxt))) #>

  macro (Binding.name "note")
    (Args.context :|-- (fn ctxt =>
      Parse.and_list1' (Scan.lift (Args.opt_thm_name I "=") -- Attrib.thms
        >> (fn ((a, srcs), ths) => ((a, map (Attrib.attribute_cmd ctxt) srcs), [(ths, [])])))
      >> (fn args => #2 (Proof_Context.note_thmss "" args ctxt)))) #>

  value (Binding.name "ctyp") (Args.typ >> (fn T =>
    "Thm.ctyp_of (Proof_Context.theory_of ML_context) " ^
      ML_Syntax.atomic (ML_Syntax.print_typ T))) #>

  value (Binding.name "cterm") (Args.term >> (fn t =>
    "Thm.cterm_of (Proof_Context.theory_of ML_context) " ^
     ML_Syntax.atomic (ML_Syntax.print_term t))) #>

  value (Binding.name "cprop") (Args.prop >> (fn t =>
    "Thm.cterm_of (Proof_Context.theory_of ML_context) " ^
     ML_Syntax.atomic (ML_Syntax.print_term t))) #>

  value (Binding.name "cpat")
    (Args.context --
      Scan.lift Args.name_source >> uncurry Proof_Context.read_term_pattern >> (fn t =>
        "Thm.cterm_of (Proof_Context.theory_of ML_context) " ^
          ML_Syntax.atomic (ML_Syntax.print_term t)))));


(* type classes *)

fun class syn = Args.context -- Scan.lift Args.name_source >> (fn (ctxt, s) =>
  Proof_Context.read_class ctxt s
  |> syn ? Lexicon.mark_class
  |> ML_Syntax.print_string);

val _ = Context.>> (Context.map_theory
 (inline (Binding.name "class") (class false) #>
  inline (Binding.name "class_syntax") (class true) #>

  inline (Binding.name "sort")
    (Args.context -- Scan.lift Args.name_source >> (fn (ctxt, s) =>
      ML_Syntax.atomic (ML_Syntax.print_sort (Syntax.read_sort ctxt s))))));


(* type constructors *)

fun type_name kind check = Args.context -- Scan.lift (Parse.position Args.name_source)
  >> (fn (ctxt, (s, pos)) =>
    let
      val Type (c, _) = Proof_Context.read_type_name_proper ctxt false s;
      val decl = Type.the_decl (Proof_Context.tsig_of ctxt) (c, pos);
      val res =
        (case try check (c, decl) of
          SOME res => res
        | NONE => error ("Not a " ^ kind ^ ": " ^ quote c ^ Position.here pos));
    in ML_Syntax.print_string res end);

val _ = Context.>> (Context.map_theory
 (inline (Binding.name "type_name")
    (type_name "logical type" (fn (c, Type.LogicalType _) => c)) #>
  inline (Binding.name "type_abbrev")
    (type_name "type abbreviation" (fn (c, Type.Abbreviation _) => c)) #>
  inline (Binding.name "nonterminal")
    (type_name "nonterminal" (fn (c, Type.Nonterminal) => c)) #>
  inline (Binding.name "type_syntax")
    (type_name "type" (fn (c, _) => Lexicon.mark_type c))));


(* constants *)

fun const_name check = Args.context -- Scan.lift (Parse.position Args.name_source)
  >> (fn (ctxt, (s, pos)) =>
    let
      val Const (c, _) = Proof_Context.read_const_proper ctxt false s;
      val res = check (Proof_Context.consts_of ctxt, c)
        handle TYPE (msg, _, _) => error (msg ^ Position.here pos);
    in ML_Syntax.print_string res end);

val _ = Context.>> (Context.map_theory
 (inline (Binding.name "const_name")
    (const_name (fn (consts, c) => (Consts.the_const consts c; c))) #>
  inline (Binding.name "const_abbrev")
    (const_name (fn (consts, c) => (Consts.the_abbreviation consts c; c))) #>
  inline (Binding.name "const_syntax")
    (const_name (fn (_, c) => Lexicon.mark_const c)) #>

  inline (Binding.name "syntax_const")
    (Args.context -- Scan.lift (Parse.position Args.name) >> (fn (ctxt, (c, pos)) =>
      if is_some (Syntax.lookup_const (Proof_Context.syn_of ctxt) c)
      then ML_Syntax.print_string c
      else error ("Unknown syntax const: " ^ quote c ^ Position.here pos))) #>

  inline (Binding.name "const")
    (Args.context -- Scan.lift Args.name_source -- Scan.optional
        (Scan.lift (Args.$$$ "(") |-- Parse.enum1' "," Args.typ --| Scan.lift (Args.$$$ ")")) []
      >> (fn ((ctxt, raw_c), Ts) =>
        let
          val Const (c, _) = Proof_Context.read_const_proper ctxt true raw_c;
          val consts = Proof_Context.consts_of ctxt;
          val n = length (Consts.typargs consts (c, Consts.type_scheme consts c));
          val _ = length Ts <> n andalso
            error ("Constant requires " ^ string_of_int n ^ " type argument(s): " ^
              quote c ^ enclose "(" ")" (commas (replicate n "_")));
          val const = Const (c, Consts.instance consts (c, Ts));
        in ML_Syntax.atomic (ML_Syntax.print_term const) end))));


(* outer syntax *)

fun with_keyword f =
  Args.theory -- Scan.lift (Parse.position Parse.string) >> (fn (thy, (name, pos)) =>
    (f ((name, Thy_Header.the_keyword thy name), pos)
      handle ERROR msg => error (msg ^ Position.here pos)));

val _ = Context.>> (Context.map_theory
 (value (Binding.name "keyword")
    (with_keyword
      (fn ((name, NONE), _) => "Parse.$$$ " ^ ML_Syntax.print_string name
        | ((name, SOME _), pos) =>
            error ("Expected minor keyword " ^ quote name ^ Position.here pos))) #>
  value (Binding.name "command_spec")
    (with_keyword
      (fn ((name, SOME kind), pos) =>
          "Keyword.command_spec " ^ ML_Syntax.atomic
            ((ML_Syntax.print_pair
              (ML_Syntax.print_pair ML_Syntax.print_string
                (ML_Syntax.print_pair
                  (ML_Syntax.print_pair ML_Syntax.print_string
                    (ML_Syntax.print_list ML_Syntax.print_string))
                  (ML_Syntax.print_list ML_Syntax.print_string)))
              ML_Syntax.print_position) ((name, kind), pos))
        | ((name, NONE), pos) =>
            error ("Expected command keyword " ^ quote name ^ Position.here pos)))));

end;

