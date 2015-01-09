(*  Title:      Code_Test.ML
    Author:     Andreas Lochbihler, ETH Zurich

Test infrastructure for the code generator
*)

signature CODE_TEST = sig
  val add_driver : string * ((Proof.context -> (string * string) list * string -> Path.T -> string) * string) -> theory -> theory
  val get_driver : theory -> string -> ((Proof.context -> (string * string) list * string -> Path.T -> string) * string) option
  val overlord : bool Config.T
  val successN : string
  val failureN : string
  val start_markerN : string
  val end_markerN : string
  val test_terms : Proof.context -> term list -> string -> unit
  val test_targets : Proof.context -> term list -> string list -> unit list
  val test_code_cmd : string list -> string list -> Toplevel.state -> unit

  val eval_term : string -> Proof.context -> term -> term

  val gen_driver :
   (theory -> Path.T -> string list -> string ->
    {files : (Path.T * string) list,
     compile_cmd : string option, run_cmd : string, mk_code_file : string -> Path.T})
   -> string -> string -> string
   -> theory -> (string * string) list * string -> Path.T -> string

  val ISABELLE_POLYML : string
  val polymlN : string
  val evaluate_in_polyml : Proof.context -> (string * string) list * string -> Path.T -> string

  val mltonN : string
  val ISABELLE_MLTON : string
  val evaluate_in_mlton : Proof.context -> (string * string) list * string -> Path.T -> string

  val smlnjN : string
  val ISABELLE_SMLNJ : string
  val evaluate_in_smlnj : Proof.context -> (string * string) list * string -> Path.T -> string

  val ocamlN : string
  val ISABELLE_OCAMLC : string
  val evaluate_in_ocaml : Proof.context -> (string * string) list * string -> Path.T -> string

  val ghcN : string
  val ISABELLE_GHC : string
  val ghc_options : string Config.T
  val evaluate_in_ghc : Proof.context -> (string * string) list * string -> Path.T -> string

  val scalaN : string
  val ISABELLE_SCALA : string
  val evaluate_in_scala : Proof.context -> (string * string) list * string -> Path.T -> string
end

structure Code_Test : CODE_TEST = struct

(* convert a list of terms into nested tuples and back *)
fun mk_tuples [] = @{term "()"}
  | mk_tuples [t] = t
  | mk_tuples (t :: ts) = HOLogic.mk_prod (t, mk_tuples ts)

fun dest_tuples (Const (@{const_name Pair}, _) $ l $ r) = l :: dest_tuples r
  | dest_tuples t = [t]


fun map_option _ NONE = NONE
  | map_option f (SOME x) = SOME (f x)

fun last_field sep str =
  let
    val n = size sep;
    val len = size str;
    fun find i =
      if i < 0 then NONE
      else if String.substring (str, i, n) = sep then SOME i
      else find (i - 1);
  in
    (case find (len - n) of
      NONE => NONE
    | SOME i => SOME (String.substring (str, 0, i), String.extract (str, i + n, NONE)))
  end;

fun split_first_last start stop s =
  case first_field start s
   of NONE => NONE
    | SOME (initial, rest) =>
      case last_field stop rest
       of NONE => NONE
        | SOME (middle, tail) => SOME (initial, middle, tail);

(* Data slot for drivers *)

structure Drivers = Theory_Data
(
  type T = (string * ((Proof.context -> (string * string) list * string -> Path.T -> string) * string)) list;
  val empty = [];
  val extend = I;
  fun merge data : T = AList.merge (op =) (K true) data;
)

val add_driver = Drivers.map o AList.update (op =);
val get_driver = AList.lookup (op =) o Drivers.get;

(*
  Test drivers must produce output of the following format:
  
  The start of the relevant data is marked with start_markerN,
  its end with end_markerN.

  Between these two markers, every line corresponds to one test.
  Lines of successful tests start with successN, failures start with failureN.
  The failure failureN may continue with the YXML encoding of the evaluated term.
  There must not be any additional whitespace in between.
*)

(* Parsing of results *)

val successN = "True"
val failureN = "False"
val start_markerN = "*@*Isabelle/Code_Test-start*@*"
val end_markerN = "*@*Isabelle/Code_Test-end*@*"

fun parse_line line =
  if String.isPrefix successN line then (true, NONE)
  else if String.isPrefix failureN line then (false, 
    if size line > size failureN then
      String.extract (line, size failureN, NONE)
      |> YXML.parse_body
      |> Term_XML.Decode.term
      |> dest_tuples
      |> SOME
    else NONE)
  else raise Fail ("Cannot parse result of evaluation:\n" ^ line)

fun parse_result target out =
  case split_first_last start_markerN end_markerN out
    of NONE => error ("Evaluation failed for " ^ target ^ "!\nBash output:\n" ^ out)
     | SOME (_, middle, _) => middle |> trim_line |> split_lines |> map parse_line

(* Pretty printing of test results *)

fun pretty_eval _ NONE _ = []
  | pretty_eval ctxt (SOME evals) ts = 
    [Pretty.fbrk,
     Pretty.big_list "Evaluated terms"
       (map (fn (t, eval) => Pretty.block 
         [Syntax.pretty_term ctxt t, Pretty.brk 1, Pretty.str "=", Pretty.brk 1,
          Syntax.pretty_term ctxt eval])
       (ts ~~ evals))]

fun pretty_failure ctxt target (((_, evals), query), eval_ts) =
  Pretty.block (Pretty.text ("Test in " ^ target ^ " failed for") @ [Pretty.brk 1, Pretty.quote (Syntax.pretty_term ctxt query)]
    @ pretty_eval ctxt evals eval_ts)

fun pretty_failures ctxt target failures =
  Pretty.blk (0, Pretty.fbreaks (map (pretty_failure ctxt target) failures))

(* Driver invocation *)

val overlord = Attrib.setup_config_bool @{binding "code_test_overlord"} (K false);

fun with_overlord_dir name f =
  let
    val path = Path.append (Path.explode "$ISABELLE_HOME_USER") (Path.basic (name ^ serial_string ()))
    val _ = Isabelle_System.mkdirs path;
  in
    Exn.release (Exn.capture f path)
  end;

fun dynamic_value_strict ctxt t compiler =
  let
    val thy = Proof_Context.theory_of ctxt
    val (driver, target) = case get_driver thy compiler
     of NONE => error ("No driver for target " ^ compiler)
      | SOME f => f;
    val debug = Config.get (Proof_Context.init_global thy) overlord
    val with_dir = if debug then with_overlord_dir else Isabelle_System.with_tmp_dir
    fun evaluate f = with_dir "Code_Test" (driver ctxt f) |> parse_result compiler
    fun evaluator program _ vs_ty deps =
      Exn.interruptible_capture evaluate (Code_Target.evaluator ctxt target program deps true vs_ty);
    fun postproc f = map (apsnd (map_option (map f)))
  in
    Exn.release (Code_Thingol.dynamic_value ctxt (Exn.map_result o postproc) evaluator t)
  end;

(* Term preprocessing *)

fun add_eval (Const (@{const_name Trueprop}, _) $ t) = add_eval t
  | add_eval (Const (@{const_name "HOL.eq"}, _) $ lhs $ rhs) = (fn acc =>
    acc
    |> add_eval rhs
    |> add_eval lhs
    |> cons rhs
    |> cons lhs)
  | add_eval (Const (@{const_name "Not"}, _) $ t) = add_eval t
  | add_eval (Const (@{const_name "Orderings.ord_class.less_eq"}, _) $ lhs $ rhs) = (fn acc =>
    lhs :: rhs :: acc)
  | add_eval (Const (@{const_name "Orderings.ord_class.less"}, _) $ lhs $ rhs) = (fn acc =>
    lhs :: rhs :: acc)
  | add_eval _ = I

fun mk_term_of [] = @{term "None :: (unit \<Rightarrow> yxml_of_term) option"}
  | mk_term_of ts =
  let
    val tuple = mk_tuples ts
    val T = fastype_of tuple
  in
    @{term "Some :: (unit \<Rightarrow> yxml_of_term) \<Rightarrow> (unit \<Rightarrow> yxml_of_term) option"} $
      (absdummy @{typ unit} (@{const yxml_string_of_term} $
        (Const (@{const_name Code_Evaluation.term_of}, T --> @{typ term}) $ tuple)))
  end

fun test_terms ctxt ts target =
  let
    val thy = Proof_Context.theory_of ctxt

    fun term_of t = Sign.of_sort thy (fastype_of t, @{sort term_of})

    fun ensure_bool t = case fastype_of t of @{typ bool} => ()
      | _ => error ("Test case not of type bool: " ^ Pretty.string_of (Syntax.pretty_term ctxt t))

    val _ = map ensure_bool ts

    val evals = map (fn t => filter term_of (add_eval t [])) ts
    val eval = map mk_term_of evals

    val T = HOLogic.mk_prodT (@{typ bool}, Type (@{type_name option}, [@{typ unit} --> @{typ yxml_of_term}]))
    val t = HOLogic.mk_list T (map HOLogic.mk_prod (ts ~~ eval))

    val result = dynamic_value_strict ctxt t target;

    val failed =
      filter_out (fst o fst o fst) (result ~~ ts ~~ evals)
      handle ListPair.UnequalLengths => 
        error ("Evaluation failed!\nWrong number of test results: " ^ Int.toString (length result))
    val _ = case failed of [] => () 
      | _ => error (Pretty.string_of (pretty_failures ctxt target failed))
  in
    ()
  end

fun test_targets ctxt = map o test_terms ctxt

fun test_code_cmd raw_ts targets state =
  let
    val ctxt = Toplevel.context_of state;
    val ts = Syntax.read_terms ctxt raw_ts;
    val frees = fold Term.add_free_names ts []
    val _ = if frees = [] then () else
      error ("Terms contain free variables: " ^
      Pretty.string_of (Pretty.block (Pretty.commas (map Pretty.str frees))))
  in
    test_targets ctxt ts targets; ()
  end

fun eval_term target ctxt t =
  let
    val frees = Term.add_free_names t []
    val _ = if frees = [] then () else
      error ("Term contains free variables: " ^
      Pretty.string_of (Pretty.block (Pretty.commas (map Pretty.str frees))))

    val thy = Proof_Context.theory_of ctxt

    val T_t = fastype_of t
    val _ = if Sign.of_sort thy (T_t, @{sort term_of}) then () else error 
      ("Type " ^ Pretty.string_of (Syntax.pretty_typ ctxt T_t) ^ 
       " of term not of sort " ^ Pretty.string_of (Syntax.pretty_sort ctxt @{sort term_of}))

    val T = HOLogic.mk_prodT (@{typ bool}, Type (@{type_name option}, [@{typ unit} --> @{typ yxml_of_term}]))
    val t' = HOLogic.mk_list T [HOLogic.mk_prod (@{term "False"}, mk_term_of [t])]

    val result = dynamic_value_strict ctxt t' target;
  in
    case result of [(_, SOME [t])] => t | _ => error "Evaluation failed"
  end

(* Generic driver *)

fun gen_driver mk_driver env_var env_var_dest compilerN ctxt (code_files, value_name) =
  let
    val compiler = getenv env_var
    val _ = if compiler <> "" then () else error (Pretty.string_of (Pretty.para 
         ("Environment variable " ^ env_var ^ " is not set. To test code generation with " ^
         compilerN ^ ", set this variable to your " ^ env_var_dest ^ " in the settings file.")))

    fun compile NONE = ()
      | compile (SOME cmd) =
        let
          val (out, ret) = Isabelle_System.bash_output cmd
        in
          if ret = 0 then () else error
            ("Compilation with " ^ compilerN ^ " failed:\n" ^ cmd ^ "\n" ^ out)
        end

    fun run (path : Path.T)= 
      let
        val modules = map fst code_files
        val {files, compile_cmd, run_cmd, mk_code_file}
          =  mk_driver ctxt path modules value_name

        val _ = map (fn (name, code) => File.write (mk_code_file name) code) code_files
        val _ = map (fn (name, content) => File.write name content) files

        val _ = compile compile_cmd

        val (out, res) = Isabelle_System.bash_output run_cmd
        val _ = if res = 0 then () else error
          ("Evaluation for " ^ compilerN ^ " terminated with error code " ^ Int.toString res ^
           "\nBash output:\n" ^ out)
      in
        out
      end
  in
    run
  end

(* Driver for PolyML *)

val ISABELLE_POLYML = "ISABELLE_POLYML"
val polymlN = "PolyML";

fun mk_driver_polyml _ path _ value_name =
  let
    val generatedN = "generated.sml"
    val driverN = "driver.sml"

    val code_path = Path.append path (Path.basic generatedN)
    val driver_path = Path.append path (Path.basic driverN)
    val driver = 
      "fun main prog_name = \n" ^
      "  let\n" ^
      "    fun format_term NONE = \"\"\n" ^ 
      "      | format_term (SOME t) = t ();\n" ^
      "    fun format (true, _) = \"" ^ successN ^ "\\n\"\n" ^
      "      | format (false, to) = \"" ^ failureN ^ "\" ^ format_term to ^ \"\\n\";\n" ^
      "    val result = " ^ value_name ^ " ();\n" ^
      "    val _ = print \"" ^ start_markerN ^ "\";\n" ^
      "    val _ = map (print o format) result;\n" ^
      "    val _ = print \"" ^ end_markerN ^ "\";\n" ^
      "  in\n" ^
      "    ()\n" ^
      "  end;\n"
    val cmd =
      "echo \"use \\\"" ^ Path.implode code_path ^ "\\\"; use \\\"" ^ 
      Path.implode driver_path ^ "\\\"; main ();\" | " ^ 
      Path.implode (Path.variable ISABELLE_POLYML)
  in
    {files = [(driver_path, driver)], compile_cmd = NONE, run_cmd = cmd, mk_code_file = K code_path}
  end

fun evaluate_in_polyml ctxt =
  gen_driver mk_driver_polyml ISABELLE_POLYML "PolyML executable" polymlN ctxt

(* Driver for mlton *)

val mltonN = "MLton"
val ISABELLE_MLTON = "ISABELLE_MLTON"

fun mk_driver_mlton _ path _ value_name =
  let
    val generatedN = "generated.sml"
    val driverN = "driver.sml"
    val projectN = "test"
    val ml_basisN = projectN ^ ".mlb"

    val code_path = Path.append path (Path.basic generatedN)
    val driver_path = Path.append path (Path.basic driverN)
    val ml_basis_path = Path.append path (Path.basic ml_basisN)
    val driver = 
      "fun format_term NONE = \"\"\n" ^ 
      "  | format_term (SOME t) = t ();\n" ^
      "fun format (true, _) = \"" ^ successN ^ "\\n\"\n" ^
      "  | format (false, to) = \"" ^ failureN ^ "\" ^ format_term to ^ \"\\n\";\n" ^
      "val result = " ^ value_name ^ " ();\n" ^
      "val _ = print \"" ^ start_markerN ^ "\";\n" ^
      "val _ = map (print o format) result;\n" ^
      "val _ = print \"" ^ end_markerN ^ "\";\n"
    val ml_basis =
      "$(SML_LIB)/basis/basis.mlb\n" ^
      generatedN ^ "\n" ^
      driverN

    val compile_cmd =
      File.shell_path (Path.variable ISABELLE_MLTON) ^
      " -default-type intinf " ^ File.shell_path ml_basis_path
    val run_cmd = File.shell_path (Path.append path (Path.basic projectN))
  in
    {files = [(driver_path, driver), (ml_basis_path, ml_basis)],
     compile_cmd = SOME compile_cmd, run_cmd = run_cmd, mk_code_file = K code_path}
  end

fun evaluate_in_mlton ctxt =
  gen_driver mk_driver_mlton ISABELLE_MLTON "MLton executable" mltonN ctxt

(* Driver for SML/NJ *)

val smlnjN = "SMLNJ"
val ISABELLE_SMLNJ = "ISABELLE_SMLNJ"

fun mk_driver_smlnj _ path _ value_name =
  let
    val generatedN = "generated.sml"
    val driverN = "driver.sml"

    val code_path = Path.append path (Path.basic generatedN)
    val driver_path = Path.append path (Path.basic driverN)
    val driver = 
      "structure Test = struct\n" ^
      "fun main prog_name =\n" ^
      "  let\n" ^
      "    fun format_term NONE = \"\"\n" ^ 
      "      | format_term (SOME t) = t ();\n" ^
      "    fun format (true, _) = \"" ^ successN ^ "\\n\"\n" ^
      "      | format (false, to) = \"" ^ failureN ^ "\" ^ format_term to ^ \"\\n\";\n" ^
      "    val result = " ^ value_name ^ " ();\n" ^
      "    val _ = print \"" ^ start_markerN ^ "\";\n" ^
      "    val _ = map (print o format) result;\n" ^
      "    val _ = print \"" ^ end_markerN ^ "\";\n" ^
      "  in\n" ^
      "    0\n" ^
      "  end;\n" ^
      "end;"
    val cmd =
      "echo \"Control.MC.matchRedundantError := false; Control.MC.matchRedundantWarn := false;" ^
      "use \\\"" ^ Path.implode code_path ^ "\\\"; use \\\"" ^ Path.implode driver_path ^ "\\\";" ^
      "Test.main ();\" | " ^ Path.implode (Path.variable ISABELLE_SMLNJ)
  in
    {files = [(driver_path, driver)], compile_cmd = NONE, run_cmd = cmd, mk_code_file = K code_path}
  end

fun evaluate_in_smlnj ctxt =
  gen_driver mk_driver_smlnj ISABELLE_SMLNJ "SMLNJ executable" smlnjN ctxt

(* Driver for OCaml *)

val ocamlN = "OCaml"
val ISABELLE_OCAMLC = "ISABELLE_OCAMLC"

fun mk_driver_ocaml _ path _ value_name =
  let
    val generatedN = "generated.ml"
    val driverN = "driver.ml"

    val code_path = Path.append path (Path.basic generatedN)
    val driver_path = Path.append path (Path.basic driverN)
    val driver = 
      "let format_term = function\n" ^
      "  | None -> \"\"\n" ^ 
      "  | Some t -> t ();;\n" ^
      "let format = function\n" ^
      "  | (true, _) -> \"" ^ successN ^ "\\n\"\n" ^
      "  | (false, x) -> \"" ^ failureN ^ "\" ^ format_term x ^ \"\\n\";;\n" ^
      "let result = " ^ ("Generated." ^ value_name) ^ " ();;\n" ^
      "let main x =\n" ^
      "  let _ = print_string \"" ^ start_markerN ^ "\" in\n" ^
      "  let _ = List.map (fun x -> print_string (format x)) result in\n" ^
      "  print_string \"" ^ end_markerN ^ "\";;\n" ^
      "main ();;"

    val compiled_path = Path.append path (Path.basic "test")
    val compile_cmd =
      Path.implode (Path.variable ISABELLE_OCAMLC) ^ " -w pu -o " ^ Path.implode compiled_path ^
      " -I " ^ Path.implode path ^
      " nums.cma " ^ Path.implode code_path ^ " " ^ Path.implode driver_path

    val run_cmd = File.shell_path compiled_path
  in
    {files = [(driver_path, driver)],
     compile_cmd = SOME compile_cmd, run_cmd = run_cmd, mk_code_file = K code_path}
  end

fun evaluate_in_ocaml ctxt =
  gen_driver mk_driver_ocaml ISABELLE_OCAMLC "ocamlc executable" ocamlN ctxt

(* Driver for GHC *)

val ghcN = "GHC"
val ISABELLE_GHC = "ISABELLE_GHC"

val ghc_options = Attrib.setup_config_string @{binding code_test_ghc} (K "")

fun mk_driver_ghc ctxt path modules value_name =
  let
    val driverN = "Main.hs"

    fun mk_code_file name = Path.append path (Path.basic (name ^ ".hs"))
    val driver_path = Path.append path (Path.basic driverN)
    val driver = 
      "module Main where {\n" ^
      String.concat (map (fn module => "import qualified " ^ module ^ ";\n") modules) ^
      "main = do {\n" ^
      "    let {\n" ^
      "      format_term Nothing = \"\";\n" ^ 
      "      format_term (Just t) = t ();\n" ^
      "      format (True, _) = \"" ^ successN ^ "\\n\";\n" ^
      "      format (False, to) = \"" ^ failureN ^ "\" ++ format_term to ++ \"\\n\";\n" ^
      "      result = " ^ value_name ^ " ();\n" ^
      "    };\n" ^
      "    Prelude.putStr \"" ^ start_markerN ^ "\";\n" ^
      "    Prelude.mapM_ (putStr . format) result;\n" ^
      "    Prelude.putStr \"" ^ end_markerN ^ "\";\n" ^
      "  }\n" ^
      "}\n"

    val compiled_path = Path.append path (Path.basic "test")
    val compile_cmd =
      Path.implode (Path.variable ISABELLE_GHC) ^ " " ^ Code_Haskell.language_params ^ " " ^
      Config.get ctxt ghc_options ^ " -o " ^ Path.implode compiled_path ^ " " ^
      Path.implode driver_path ^ " -i" ^ Path.implode path

    val run_cmd = File.shell_path compiled_path
  in
    {files = [(driver_path, driver)],
     compile_cmd = SOME compile_cmd, run_cmd = run_cmd, mk_code_file = mk_code_file}
  end

fun evaluate_in_ghc ctxt =
  gen_driver mk_driver_ghc ISABELLE_GHC "GHC executable" ghcN ctxt

(* Driver for Scala *)

val scalaN = "Scala"
val ISABELLE_SCALA = "ISABELLE_SCALA"

fun mk_driver_scala _ path _ value_name =
  let
    val generatedN = "Generated_Code"
    val driverN = "Driver.scala"

    val code_path = Path.append path (Path.basic (generatedN ^ ".scala"))
    val driver_path = Path.append path (Path.basic driverN)
    val driver = 
      "import " ^ generatedN ^ "._\n" ^
      "object Test {\n" ^
      "  def format_term(x : Option[Unit => String]) : String = x match {\n" ^
      "    case None => \"\"\n" ^
      "    case Some(x) => x(())\n" ^
      "  }\n" ^
      "  def format(term : (Boolean, Option[Unit => String])) : String = term match {\n" ^
      "      case (true, _) => \"True\\n\"\n" ^
      "      case (false, x) => \"False\" + format_term(x) + \"\\n\"\n" ^
      "  }\n" ^
      "  def main(args:Array[String]) = {\n" ^
      "    val result = " ^ value_name ^ "(());\n" ^
      "    print(\"" ^ start_markerN ^ "\");\n" ^
      "    result.map{test:(Boolean, Option[Unit => String]) => print(format(test))};\n" ^
      "    print(\"" ^ end_markerN ^ "\");\n" ^
      "  }\n" ^
      "}\n"

    val compile_cmd =
      Path.implode (Path.append (Path.variable ISABELLE_SCALA) (Path.basic "scalac")) ^
      " -d " ^ File.shell_path path ^ " -classpath " ^ File.shell_path path ^ " " ^
      File.shell_path code_path ^ " " ^ File.shell_path driver_path

    val run_cmd =
      Path.implode (Path.append (Path.variable ISABELLE_SCALA) (Path.basic "scala")) ^
      " -cp " ^ File.shell_path path ^ " Test"
  in
    {files = [(driver_path, driver)],
     compile_cmd = SOME compile_cmd, run_cmd = run_cmd, mk_code_file = K code_path}
  end

fun evaluate_in_scala ctxt =
  gen_driver mk_driver_scala ISABELLE_SCALA "Scala directory" scalaN ctxt

val test_codeP = Scan.repeat1 Parse.prop -- (@{keyword "in"} |-- Scan.repeat1 Parse.name)

val _ = 
  Outer_Syntax.command @{command_spec "test_code"}
    "compile test cases to target languages, execute them and report results"
      (test_codeP >> (fn (raw_ts, targets) => Toplevel.keep (test_code_cmd raw_ts targets)))

val _ = Theory.setup (fold add_driver
  [(polymlN, (evaluate_in_polyml, Code_ML.target_SML)),
   (mltonN, (evaluate_in_mlton, Code_ML.target_SML)),
   (smlnjN, (evaluate_in_smlnj, Code_ML.target_SML)),
   (ocamlN, (evaluate_in_ocaml, Code_ML.target_OCaml)),
   (ghcN, (evaluate_in_ghc, Code_Haskell.target)),
   (scalaN, (evaluate_in_scala, Code_Scala.target))]
  #> fold (fn target => Value.add_evaluator (target, eval_term target))
    [polymlN, mltonN, smlnjN, ocamlN, ghcN, scalaN]);

end

