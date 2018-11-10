(*  Title:      Pure/Tools/ghc.ML
    Author:     Makarius

Support for GHC: Glasgow Haskell Compiler.
*)

signature GHC =
sig
  val print_codepoint: UTF8.codepoint -> string
  val print_symbol: Symbol.symbol -> string
  val print_string: string -> string
  val antiquotation: binding -> 'a Token.context_parser ->
    ({context: Proof.context, source: Token.src, argument: 'a} -> string) -> theory -> theory
  val read_source: Proof.context -> Input.source -> string
  val set_result: string -> Proof.context -> Proof.context
end;

structure GHC: GHC =
struct

(** string literals **)

fun print_codepoint c =
  (case c of
    34 => "\\\""
  | 39 => "\\'"
  | 92 => "\\\\"
  | 7 => "\\a"
  | 8 => "\\b"
  | 9 => "\\t"
  | 10 => "\\n"
  | 11 => "\\v"
  | 12 => "\\f"
  | 13 => "\\r"
  | c =>
      if c >= 32 andalso c < 127 then chr c
      else "\\" ^ string_of_int c ^ "\\&");

fun print_symbol sym =
  (case Symbol.decode sym of
    Symbol.Char s => print_codepoint (ord s)
  | Symbol.UTF8 s => UTF8.decode_permissive s |> map print_codepoint |> implode
  | Symbol.Sym s => "\\092<" ^ s ^ ">"
  | Symbol.Control s => "\\092<^" ^ s ^ ">"
  | _ => translate_string (print_codepoint o ord) sym);

val print_string = quote o implode o map print_symbol o Symbol.explode;


(** antiquotations **)

(* theory data *)

structure Antiqs = Theory_Data
(
  type T = (Token.src -> Proof.context -> string) Name_Space.table;
  val empty : T = Name_Space.empty_table Markup.haskell_antiquotationN;
  val extend = I;
  fun merge tabs : T = Name_Space.merge_tables tabs;
);

val get_antiquotations = Antiqs.get o Proof_Context.theory_of;

fun antiquotation name scan body thy =
  let
    fun antiq src ctxt =
      let val (x, ctxt') = Token.syntax scan src ctxt
      in body {context = ctxt', source = src, argument = x} end;
  in thy |> Antiqs.map (Name_Space.define (Context.Theory thy) true (name, antiq) #> #2) end;


(* read source and expand antiquotations *)

val scan_antiq =
  Antiquote.scan_control >> Antiquote.Control ||
  Scan.one (Symbol.not_eof o Symbol_Pos.symbol) >> (Antiquote.Text o Symbol_Pos.symbol);

fun read_source ctxt source =
  let
    val _ =
      Context_Position.report ctxt (Input.pos_of source)
        (Markup.language_haskell (Input.is_delimited source));

    val (input, _) =
      Input.source_explode source
      |> Scan.error (Scan.finite Symbol_Pos.stopper (Scan.repeat scan_antiq));

    val _ = Context_Position.reports ctxt (Antiquote.antiq_reports input);

    fun expand antiq =
      (case antiq of
        Antiquote.Text s => s
      | Antiquote.Control {name, body, ...} =>
          let
            val src = Token.make_src name (if null body then [] else [Token.read_cartouche body]);
            val (src', f) = Token.check_src ctxt get_antiquotations src;
          in f src' ctxt end
      | Antiquote.Antiq antiq => error ("Bad antiquotation " ^ Position.here (#1 (#range antiq))));
  in implode (map expand input) end;


(* concrete antiquotation: ML expression as Haskell string literal *)

structure Local_Data = Proof_Data
(
  type T = string option;
  fun init _ = NONE;
);

val set_result = Local_Data.put o SOME;

fun the_result ctxt =
  (case Local_Data.get ctxt of
    SOME s => s
  | NONE => raise Fail "No result");

fun path_antiq check =
  Args.context -- Scan.lift (Parse.position Parse.path) >> (fn (ctxt, (name, pos)) =>
    (check ctxt Path.current (name, pos) |> Path.implode |> print_string));

val _ =
  Theory.setup
    (antiquotation \<^binding>\<open>cartouche\<close> (Scan.lift Args.cartouche_input)
      (fn {context = ctxt, argument, ...} =>
        ctxt |> Context.proof_map
          (ML_Context.expression (Input.pos_of argument)
            (ML_Lex.read "Theory.local_setup (GHC.set_result (" @
             ML_Lex.read_source argument @ ML_Lex.read "))"))
        |> the_result |> print_string) #>
    antiquotation \<^binding>\<open>path\<close> (path_antiq Resources.check_path) #argument #>
    antiquotation \<^binding>\<open>file\<close> (path_antiq Resources.check_file) #argument #>
    antiquotation \<^binding>\<open>dir\<close> (path_antiq Resources.check_dir) #argument);

end;
