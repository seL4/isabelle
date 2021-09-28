(*  Title:      HOL/Library/code_test.ML
    Author:     Andreas Lochbihler, ETH Zürich

Test infrastructure for the code generator.
*)

signature CODE_TEST =
sig
  val add_driver:
    string * ((Proof.context -> (string * string) list * string -> Path.T -> string) * string) ->
    theory -> theory
  val debug: bool Config.T
  val test_terms: Proof.context -> term list -> string -> unit
  val test_code_cmd: string list -> string list -> Proof.context -> unit
  val eval_term: string -> Proof.context -> term -> term
  val check_settings: string -> string -> string -> unit
  val compile: string -> string -> unit
  val evaluate: string -> string -> string
  val evaluate_in_polyml: Proof.context -> (string * string) list * string -> Path.T -> string
  val evaluate_in_mlton: Proof.context -> (string * string) list * string -> Path.T -> string
  val evaluate_in_smlnj: Proof.context -> (string * string) list * string -> Path.T -> string
  val evaluate_in_ocaml: Proof.context -> (string * string) list * string -> Path.T -> string
  val ghc_options: string Config.T
  val evaluate_in_ghc: Proof.context -> (string * string) list * string -> Path.T -> string
  val evaluate_in_scala: Proof.context -> (string * string) list * string -> Path.T -> string
  val target_Scala: string
  val target_Haskell: string
end

structure Code_Test: CODE_TEST =
struct

(* convert a list of terms into nested tuples and back *)

fun mk_tuples [] = \<^term>\<open>()\<close>
  | mk_tuples [t] = t
  | mk_tuples (t :: ts) = HOLogic.mk_prod (t, mk_tuples ts)

fun dest_tuples (Const (\<^const_name>\<open>Pair\<close>, _) $ l $ r) = l :: dest_tuples r
  | dest_tuples t = [t]


fun last_field sep str =
  let
    val n = size sep
    val len = size str
    fun find i =
      if i < 0 then NONE
      else if String.substring (str, i, n) = sep then SOME i
      else find (i - 1)
  in
    (case find (len - n) of
      NONE => NONE
    | SOME i => SOME (String.substring (str, 0, i), String.extract (str, i + n, NONE)))
  end

fun split_first_last start stop s =
  (case first_field start s of
    NONE => NONE
  | SOME (initial, rest) =>
      (case last_field stop rest of
        NONE => NONE
      | SOME (middle, tail) => SOME (initial, middle, tail)))


(* data slot for drivers *)

structure Drivers = Theory_Data
(
  type T =
    (string * ((Proof.context -> (string * string) list * string -> Path.T -> string) * string)) list
  val empty = []
  val extend = I
  fun merge data : T = AList.merge (op =) (K true) data
)

val add_driver = Drivers.map o AList.update (op =)
val get_driver = AList.lookup (op =) o Drivers.get

(*
  Test drivers must produce output of the following format:

  The start of the relevant data is marked with start_marker,
  its end with end_marker.

  Between these two markers, every line corresponds to one test.
  Lines of successful tests start with success, failures start with failure.
  The failure failure may continue with the YXML encoding of the evaluated term.
  There must not be any additional whitespace in between.
*)


(* parsing of results *)

val success = "True"
val failure = "False"
val start_marker = "*@*Isabelle/Code_Test-start*@*"
val end_marker = "*@*Isabelle/Code_Test-end*@*"

fun parse_line line =
  if String.isPrefix success line then (true, NONE)
  else if String.isPrefix failure line then (false,
    if size line > size failure then
      String.extract (line, size failure, NONE)
      |> YXML.parse_body
      |> Term_XML.Decode.term_raw
      |> dest_tuples
      |> SOME
    else NONE)
  else raise Fail ("Cannot parse result of evaluation:\n" ^ line)

fun parse_result target out =
  (case split_first_last start_marker end_marker out of
    NONE => error ("Evaluation failed for " ^ target ^ "!\nCompiler output:\n" ^ out)
  | SOME (_, middle, _) => middle |> trim_split_lines |> map parse_line)


(* pretty printing of test results *)

fun pretty_eval _ NONE _ = []
  | pretty_eval ctxt (SOME evals) ts =
      [Pretty.fbrk,
       Pretty.big_list "Evaluated terms"
         (map (fn (t, eval) => Pretty.block
           [Syntax.pretty_term ctxt t, Pretty.brk 1, Pretty.str "=", Pretty.brk 1,
            Syntax.pretty_term ctxt eval])
         (ts ~~ evals))]

fun pretty_failure ctxt target (((_, evals), query), eval_ts) =
  Pretty.block (Pretty.text ("Test in " ^ target ^ " failed for") @
    [Pretty.brk 1, Pretty.quote (Syntax.pretty_term ctxt query)] @
    pretty_eval ctxt evals eval_ts)

fun pretty_failures ctxt target failures =
  Pretty.blk (0, Pretty.fbreaks (map (pretty_failure ctxt target) failures))


(* driver invocation *)

val debug = Attrib.setup_config_bool \<^binding>\<open>test_code_debug\<close> (K false)

fun with_debug_dir name f =
  (Path.explode "$ISABELLE_HOME_USER" + Path.basic (name ^ serial_string ()))
  |> Isabelle_System.make_directory
  |> Exn.capture f
  |> Exn.release;

fun dynamic_value_strict ctxt t compiler =
  let
    val thy = Proof_Context.theory_of ctxt
    val (driver, target) =
      (case get_driver thy compiler of
        NONE => error ("No driver for target " ^ compiler)
      | SOME drv => drv)
    val with_dir = if Config.get ctxt debug then with_debug_dir else Isabelle_System.with_tmp_dir
    fun eval result =
      with_dir "Code_Test" (driver ctxt ((apfst o map o apfst) Long_Name.implode result))
      |> parse_result compiler
    fun evaluator program _ vs_ty deps =
      Exn.interruptible_capture eval
        (Code_Target.compilation_text ctxt target program deps true vs_ty)
    fun postproc f = map (apsnd (Option.map (map f)))
  in Exn.release (Code_Thingol.dynamic_value ctxt (Exn.map_res o postproc) evaluator t) end


(* term preprocessing *)

fun add_eval (Const (\<^const_name>\<open>Trueprop\<close>, _) $ t) = add_eval t
  | add_eval (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ lhs $ rhs) = (fn acc =>
      acc
      |> add_eval rhs
      |> add_eval lhs
      |> cons rhs
      |> cons lhs)
  | add_eval (Const (\<^const_name>\<open>Not\<close>, _) $ t) = add_eval t
  | add_eval (Const (\<^const_name>\<open>Orderings.ord_class.less_eq\<close>, _) $ lhs $ rhs) = (fn acc =>
      lhs :: rhs :: acc)
  | add_eval (Const (\<^const_name>\<open>Orderings.ord_class.less\<close>, _) $ lhs $ rhs) = (fn acc =>
      lhs :: rhs :: acc)
  | add_eval _ = I

fun mk_term_of [] = \<^Const>\<open>None \<^typ>\<open>unit \<Rightarrow> yxml_of_term\<close>\<close>
  | mk_term_of ts =
      let
        val tuple = mk_tuples ts
        val T = fastype_of tuple
      in
        \<^term>\<open>Some :: (unit \<Rightarrow> yxml_of_term) \<Rightarrow> (unit \<Rightarrow> yxml_of_term) option\<close> $
          (absdummy \<^typ>\<open>unit\<close> (\<^Const>\<open>yxml_string_of_term\<close> $
            (Const (\<^const_name>\<open>Code_Evaluation.term_of\<close>, T --> \<^Type>\<open>term\<close>) $ tuple)))
      end

fun test_terms ctxt ts target =
  let
    val thy = Proof_Context.theory_of ctxt

    fun term_of t = Sign.of_sort thy (fastype_of t, \<^sort>\<open>term_of\<close>)

    fun ensure_bool t =
      (case fastype_of t of
        \<^typ>\<open>bool\<close> => ()
      | _ =>
        error (Pretty.string_of
          (Pretty.block [Pretty.str "Test case not of type bool:", Pretty.brk 1,
            Syntax.pretty_term ctxt t])))

    val _ = List.app ensure_bool ts

    val evals = map (fn t => filter term_of (add_eval t [])) ts
    val eval = map mk_term_of evals

    val t =
      HOLogic.mk_list \<^typ>\<open>bool \<times> (unit \<Rightarrow> yxml_of_term) option\<close>
        (map HOLogic.mk_prod (ts ~~ eval))

    val result = dynamic_value_strict ctxt t target

    val failed =
      filter_out (fst o fst o fst) (result ~~ ts ~~ evals)
      handle ListPair.UnequalLengths =>
        error ("Evaluation failed!\nWrong number of test results: " ^ string_of_int (length result))
  in
    (case failed of
      [] => ()
    | _ => error (Pretty.string_of (pretty_failures ctxt target failed)))
  end

fun test_code_cmd raw_ts targets ctxt =
  let
    val ts = Syntax.read_terms ctxt raw_ts
    val frees = fold Term.add_frees ts []
    val _ =
      if null frees then ()
      else error (Pretty.string_of
        (Pretty.block (Pretty.str "Terms contain free variables:" :: Pretty.brk 1 ::
          Pretty.commas (map (Syntax.pretty_term ctxt o Free) frees))))
  in List.app (test_terms ctxt ts) targets end

fun eval_term target ctxt t =
  let
    val frees = Term.add_frees t []
    val _ =
      if null frees then ()
      else
        error (Pretty.string_of
          (Pretty.block (Pretty.str "Term contains free variables:" :: Pretty.brk 1 ::
            Pretty.commas (map (Syntax.pretty_term ctxt o Free) frees))))

    val T = fastype_of t
    val _ =
      if Sign.of_sort (Proof_Context.theory_of ctxt) (T, \<^sort>\<open>term_of\<close>) then ()
      else error ("Type " ^ Syntax.string_of_typ ctxt T ^
       " of term not of sort " ^ Syntax.string_of_sort ctxt \<^sort>\<open>term_of\<close>)

    val t' =
      HOLogic.mk_list \<^typ>\<open>bool \<times> (unit \<Rightarrow> yxml_of_term) option\<close>
        [HOLogic.mk_prod (\<^term>\<open>False\<close>, mk_term_of [t])]

    val result = dynamic_value_strict ctxt t' target
  in (case result of [(_, SOME [t])] => t | _ => error "Evaluation failed") end


(* check and invoke compiler *)

fun check_settings compiler var descr =
  if getenv var = "" then
    error (Pretty.string_of (Pretty.para
      ("Environment variable " ^ var ^ " is not set. To test code generation with " ^
        compiler ^ ", set this variable to your " ^ descr ^
        " in the $ISABELLE_HOME_USER/etc/settings file.")))
  else ()

fun compile compiler cmd =
  let val (out, ret) = Isabelle_System.bash_output cmd in
    if ret = 0 then ()
    else error ("Compilation with " ^ compiler ^ " failed:\n" ^ cmd ^ "\n" ^ out)
  end

fun evaluate compiler cmd =
  let val (out, res) = Isabelle_System.bash_output cmd in
    if res = 0 then out
    else error ("Evaluation for " ^ compiler ^ " terminated with error code " ^
      string_of_int res ^ "\nCompiler output:\n" ^ out)
  end


(* driver for PolyML *)

val polymlN = "PolyML"

fun evaluate_in_polyml (_: Proof.context) (code_files, value_name) dir =
  let
    val code_path = dir + Path.basic "generated.sml"
    val driver_path = dir + Path.basic "driver.sml"
    val out_path = dir + Path.basic "out"

    val code = #2 (the_single code_files)
    val driver = \<^verbatim>\<open>
fun main () =
  let
    fun format (true, _) = \<close> ^ ML_Syntax.print_string success ^ \<^verbatim>\<open> ^ "\n"
      | format (false, NONE) = \<close> ^ ML_Syntax.print_string failure ^ \<^verbatim>\<open> ^ "\n"
      | format (false, SOME t) = \<close> ^ ML_Syntax.print_string failure ^ \<^verbatim>\<open> ^ t () ^ "\n"
    val result = \<close> ^ value_name ^ \<^verbatim>\<open> ()
    val result_text = \<close> ^
      ML_Syntax.print_string start_marker ^
      \<^verbatim>\<open> ^ String.concat (map format result) ^ \<close> ^
      ML_Syntax.print_string end_marker ^ \<^verbatim>\<open>
    val out = BinIO.openOut \<close> ^ ML_Syntax.print_platform_path out_path ^ \<^verbatim>\<open>
    val _ = BinIO.output (out, Byte.stringToBytes result_text)
    val _ = BinIO.closeOut out
  in () end;
\<close>
    val _ = File.write code_path code
    val _ = File.write driver_path driver
    val _ =
      ML_Context.eval
        {environment = ML_Env.SML, redirect = false, verbose = false, debug = NONE,
          writeln = writeln, warning = warning}
        Position.none
        (ML_Lex.read_text (code, Path.position code_path) @
         ML_Lex.read_text (driver, Path.position driver_path) @
         ML_Lex.read "main ()")
      handle ERROR msg => error ("Evaluation for " ^ polymlN ^ " failed:\n" ^ msg)
  in File.read out_path end


(* driver for mlton *)

val mltonN = "MLton"
val ISABELLE_MLTON = "ISABELLE_MLTON"

fun evaluate_in_mlton (_: Proof.context) (code_files, value_name) dir =
  let
    val compiler = mltonN
    val generatedN = "generated.sml"
    val driverN = "driver.sml"
    val projectN = "test"

    val code_path = dir + Path.basic generatedN
    val driver_path = dir + Path.basic driverN
    val basis_path = dir + Path.basic (projectN ^ ".mlb")
    val driver = \<^verbatim>\<open>
fun format (true, _) = \<close> ^ ML_Syntax.print_string success ^ \<^verbatim>\<open> ^ "\n"
  | format (false, NONE) = \<close> ^ ML_Syntax.print_string failure ^ \<^verbatim>\<open> ^ "\n"
  | format (false, SOME t) = \<close> ^ ML_Syntax.print_string failure ^ \<^verbatim>\<open> ^ t () ^ "\n"
val result = \<close> ^ value_name ^ \<^verbatim>\<open> ()
val _ = print \<close> ^ ML_Syntax.print_string start_marker ^ \<^verbatim>\<open>
val _ = List.app (print o format) result
val _ = print \<close> ^ ML_Syntax.print_string end_marker ^ \<^verbatim>\<open>
\<close>
    val _ = check_settings compiler ISABELLE_MLTON "MLton executable"
    val _ = List.app (File.write code_path o snd) code_files
    val _ = File.write driver_path driver
    val _ = File.write basis_path ("$(SML_LIB)/basis/basis.mlb\n" ^ generatedN ^ "\n" ^ driverN)
  in
    compile compiler ("\"$ISABELLE_MLTON\" -default-type intinf " ^ File.bash_path basis_path);
    evaluate compiler (File.bash_path (dir + Path.basic projectN))
  end


(* driver for SML/NJ *)

val smlnjN = "SMLNJ"
val ISABELLE_SMLNJ = "ISABELLE_SMLNJ"

fun evaluate_in_smlnj (_: Proof.context) (code_files, value_name) dir =
  let
    val compiler = smlnjN
    val generatedN = "generated.sml"
    val driverN = "driver.sml"

    val code_path = dir + Path.basic generatedN
    val driver_path = dir + Path.basic driverN
    val driver = \<^verbatim>\<open>
structure Test =
struct
  fun main () =
    let
      fun format (true, _) = \<close> ^ ML_Syntax.print_string success ^ \<^verbatim>\<open> ^ "\n"
        | format (false, NONE) = \<close> ^ ML_Syntax.print_string failure ^ \<^verbatim>\<open> ^ "\n"
        | format (false, SOME t) = \<close> ^ ML_Syntax.print_string failure ^ \<^verbatim>\<open> ^ t () ^ "\n"
      val result = \<close> ^ value_name ^ \<^verbatim>\<open> ()
      val _ = print \<close> ^ ML_Syntax.print_string start_marker ^ \<^verbatim>\<open>
      val _ = List.app (print o format) result
      val _ = print \<close> ^ ML_Syntax.print_string end_marker ^ \<^verbatim>\<open>
    in 0 end
end
\<close>
    val _ = check_settings compiler ISABELLE_SMLNJ "SMLNJ executable"
    val _ = List.app (File.write code_path o snd) code_files
    val _ = File.write driver_path driver
    val ml_source =
      "Control.MC.matchRedundantError := false; Control.MC.matchRedundantWarn := false;" ^
      "use " ^ ML_Syntax.print_string (File.platform_path code_path) ^
      "; use " ^ ML_Syntax.print_string (File.platform_path driver_path) ^
      "; Test.main ();"
  in evaluate compiler ("echo " ^ Bash.string ml_source ^ " | \"$ISABELLE_SMLNJ\"") end


(* driver for OCaml *)

val ocamlN = "OCaml"
val ISABELLE_OCAMLFIND = "ISABELLE_OCAMLFIND"

fun evaluate_in_ocaml (_: Proof.context) (code_files, value_name) dir =
  let
    val compiler = ocamlN

    val code_path = dir + Path.basic "generated.ml"
    val driver_path = dir + Path.basic "driver.ml"
    val driver =
      "let format_term = function\n" ^
      "  | None -> \"\"\n" ^
      "  | Some t -> t ();;\n" ^
      "let format = function\n" ^
      "  | (true, _) -> \"" ^ success ^ "\\n\"\n" ^
      "  | (false, x) -> \"" ^ failure ^ "\" ^ format_term x ^ \"\\n\";;\n" ^
      "let result = " ^ ("Generated." ^ value_name) ^ " ();;\n" ^
      "let main x =\n" ^
      "  let _ = print_string \"" ^ start_marker ^ "\" in\n" ^
      "  let _ = List.map (fun x -> print_string (format x)) result in\n" ^
      "  print_string \"" ^ end_marker ^ "\";;\n" ^
      "main ();;"
    val compiled_path = dir + Path.basic "test"

    val _ = check_settings compiler ISABELLE_OCAMLFIND "ocamlfind executable"
    val _ = List.app (File.write code_path o snd) code_files
    val _ = File.write driver_path driver
    val cmd =
      "\"$ISABELLE_OCAMLFIND\" ocamlopt -w pu -package zarith -linkpkg" ^
      " -o " ^ File.bash_path compiled_path ^ " -I " ^ File.bash_path dir ^ " " ^
      File.bash_path code_path ^ " " ^ File.bash_path driver_path ^ " </dev/null"
  in compile compiler cmd; evaluate compiler (File.bash_path compiled_path) end


(* driver for GHC *)

val ghcN = "GHC"
val ISABELLE_GHC = "ISABELLE_GHC"

val ghc_options = Attrib.setup_config_string \<^binding>\<open>code_test_ghc\<close> (K "")

fun evaluate_in_ghc ctxt (code_files, value_name) dir =
  let
    val compiler = ghcN
    val modules = map fst code_files

    val driver_path = dir + Path.basic "Main.hs"
    val driver =
      "module Main where {\n" ^
      implode (map (fn module => "import qualified " ^ unsuffix ".hs" module ^ ";\n") modules) ^
      "main = do {\n" ^
      "    let {\n" ^
      "      format_term Nothing = \"\";\n" ^
      "      format_term (Just t) = t ();\n" ^
      "      format (True, _) = \"" ^ success ^ "\\n\";\n" ^
      "      format (False, to) = \"" ^ failure ^ "\" ++ format_term to ++ \"\\n\";\n" ^
      "      result = " ^ value_name ^ " ();\n" ^
      "    };\n" ^
      "    Prelude.putStr \"" ^ start_marker ^ "\";\n" ^
      "    Prelude.mapM_ (putStr . format) result;\n" ^
      "    Prelude.putStr \"" ^ end_marker ^ "\";\n" ^
      "  }\n" ^
      "}\n"

    val _ = check_settings compiler ISABELLE_GHC "GHC executable"
    val _ = List.app (fn (name, code) => File.write (dir + Path.basic name) code) code_files
    val _ = File.write driver_path driver

    val compiled_path = dir + Path.basic "test"
    val cmd =
      "\"$ISABELLE_GHC\" " ^ Code_Haskell.language_params ^ " " ^
      Config.get ctxt ghc_options ^ " -o " ^
      File.bash_platform_path compiled_path ^ " " ^
      File.bash_platform_path driver_path ^ " -i" ^
      File.bash_platform_path dir
  in compile compiler cmd; evaluate compiler (File.bash_path compiled_path) end


(* driver for Scala *)

val scalaN = "Scala"

fun evaluate_in_scala (_: Proof.context) (code_files, value_name) dir =
  let
    val generatedN = "Generated_Code"
    val driverN = "Driver.scala"

    val code_path = dir + Path.basic (generatedN ^ ".scala")
    val driver_path = dir + Path.basic driverN
    val out_path = dir + Path.basic "out"

    val code = #2 (the_single code_files)
    val driver = \<^verbatim>\<open>
{
  val result = \<close> ^ value_name ^ \<^verbatim>\<open>(())
  val result_text =
    result.map(
      {
        case (true, _) => "True\n"
        case (false, None) => "False\n"
        case (false, Some(t)) => "False" + t(()) + "\n"
      }).mkString
  isabelle.File.write(
    isabelle.Path.explode(\<close> ^ quote (Path.implode (Path.expand out_path)) ^ \<^verbatim>\<open>),
    \<close> ^ quote start_marker ^ \<^verbatim>\<open> + result_text + \<close> ^ quote end_marker ^ \<^verbatim>\<open>)
}\<close>
    val _ = File.write code_path code
    val _ = File.write driver_path driver
    val _ = Scala_Compiler.toplevel true (code ^ driver)
      handle ERROR msg => error ("Evaluation for " ^ scalaN ^ " failed:\n" ^ msg)
  in File.read out_path end


(* command setup *)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>test_code\<close>
    "compile test cases to target languages, execute them and report results"
      (Scan.repeat1 Parse.prop -- (\<^keyword>\<open>in\<close> |-- Scan.repeat1 Parse.name)
        >> (fn (ts, targets) => Toplevel.keep (test_code_cmd ts targets o Toplevel.context_of)))

val target_Scala = "Scala_eval"
val target_Haskell = "Haskell_eval"

val _ =
  Theory.setup
   (Code_Target.add_derived_target (target_Scala, [(Code_Scala.target, I)]) #>
    Code_Target.add_derived_target (target_Haskell, [(Code_Haskell.target, I)]) #>
    fold add_driver
      [(polymlN, (evaluate_in_polyml, Code_ML.target_SML)),
       (mltonN, (evaluate_in_mlton, Code_ML.target_SML)),
       (smlnjN, (evaluate_in_smlnj, Code_ML.target_SML)),
       (ocamlN, (evaluate_in_ocaml, Code_ML.target_OCaml)),
       (ghcN, (evaluate_in_ghc, target_Haskell)),
       (scalaN, (evaluate_in_scala, target_Scala))] #>
    fold (fn target => Value_Command.add_evaluator (Binding.name target, eval_term target) #> #2)
      [polymlN, mltonN, smlnjN, ocamlN, ghcN, scalaN])

end
