(*  Title:      Pure/Tools/generated_files.ML
    Author:     Makarius

Generated source files for other languages: with antiquotations, without Isabelle symbols.
*)

signature GENERATED_FILES =
sig
  val add_files: Path.binding * string -> theory -> theory
  type file = {path: Path.T, pos: Position.T, content: string}
  val file_binding: file -> Path.binding
  val file_markup: file -> Markup.T
  val print_file: file -> string
  val report_file: Proof.context -> Position.T -> file -> unit
  val get_files: theory -> file list
  val get_file: theory -> Path.binding -> file
  val get_files_in: Path.binding list * theory -> (file * Position.T) list
  val check_files_in: Proof.context ->
    (string * Position.T) list * (string * Position.T) option -> Path.binding list * theory
  val write_file: Path.T -> file -> unit
  val export_file: theory -> file -> unit
  type file_type =
    {name: string, ext: string, make_comment: string -> string, make_string: string -> string}
  val file_type:
    binding -> {ext: string, make_comment: string -> string, make_string: string -> string} ->
    theory -> theory
  val antiquotation: binding -> 'a Token.context_parser ->
    ({context: Proof.context, source: Token.src, file_type: file_type, argument: 'a} -> string) ->
    theory -> theory
  val set_string: string -> Proof.context -> Proof.context
  val generate_file: Path.binding * Input.source -> Proof.context -> local_theory
  val generate_file_cmd: (string * Position.T) * Input.source -> local_theory -> local_theory
  val export_generated_files: Proof.context -> (Path.binding list * theory) list -> unit
  val export_generated_files_cmd: Proof.context ->
    ((string * Position.T) list * (string * Position.T) option) list -> unit
  val with_compile_dir: (Path.T -> unit) -> unit
  val compile_generated_files: Proof.context ->
    (Path.binding list * theory) list ->
    (Path.T list * Path.T) list ->
    (Path.binding list * bool option) list ->
    Path.binding -> Input.source -> unit
  val compile_generated_files_cmd: Proof.context ->
    ((string * Position.T) list * (string * Position.T) option) list ->
    (Input.source list * Input.source) list ->
    ((string * Position.T) list * bool option) list ->
    string * Position.T -> Input.source -> unit
  val execute: Path.T -> Input.source -> string -> string
end;

structure Generated_Files: GENERATED_FILES =
struct

(** context data **)

type file = Path.T * (Position.T * string);

type file_type =
  {name: string, ext: string, make_comment: string -> string, make_string: string -> string};

type antiquotation = Token.src -> Proof.context -> file_type -> string;

fun err_dup_files path pos pos' =
  error ("Duplicate generated file: " ^ Path.print path ^ Position.here_list [pos, pos']);

structure Data = Theory_Data
(
  type T =
    file list Symtab.table *  (*files for named theory*)
    file_type Name_Space.table *  (*file types*)
    antiquotation Name_Space.table;  (*antiquotations*)
  val empty =
    (Symtab.empty,
     Name_Space.empty_table Markup.file_typeN,
     Name_Space.empty_table Markup.antiquotationN);
  val extend = I;
  fun merge ((files1, types1, antiqs1), (files2, types2, antiqs2)) =
    let
      val files' =
        (files1, files2) |> Symtab.join (K (Library.merge (fn ((path1, file1), (path2, file2)) =>
          if path1 <> path2 then false
          else if file1 = file2 then true
          else err_dup_files path1 (#1 file1) (#1 file2))));
      val types' = Name_Space.merge_tables (types1, types2);
      val antiqs' = Name_Space.merge_tables (antiqs1, antiqs2);
    in (files', types', antiqs') end;
);

fun lookup_files thy =
  Symtab.lookup_list (#1 (Data.get thy)) (Context.theory_long_name thy);

fun update_files thy_files' thy =
  (Data.map o @{apply 3(1)}) (Symtab.update (Context.theory_long_name thy, thy_files')) thy;

fun add_files (binding, content) thy =
  let
    val _ = Path.proper_binding binding;
    val (path, pos) = Path.dest_binding binding;
    val thy_files = lookup_files thy;
    val thy_files' =
      (case AList.lookup (op =) thy_files path of
        SOME (pos', _) => err_dup_files path pos pos'
      | NONE => (path, (pos, content)) :: thy_files);
  in update_files thy_files' thy end;


(* get files *)

type file = {path: Path.T, pos: Position.T, content: string};

fun file_binding (file: file) = Path.binding (#path file, #pos file);

fun file_markup (file: file) = (Markup.entityN, Position.def_properties_of (#pos file));

fun print_file (file: file) = Markup.markup (file_markup file) (quote (Path.implode (#path file)));

fun report_file ctxt pos file = Context_Position.report ctxt pos (file_markup file);


fun get_files thy =
  lookup_files thy |> rev |> map (fn (path, (pos, content)) =>
    {path = path, pos = pos, content = content}: file);

fun get_file thy binding =
  let val (path, pos) = Path.dest_binding binding in
    (case find_first (fn file => #path file = path) (get_files thy) of
      SOME file => file
    | NONE =>
        error ("Missing generated file " ^ Path.print path ^
          " in theory " ^ quote (Context.theory_long_name thy) ^ Position.here pos))
  end;

fun get_files_in ([], thy) = map (rpair Position.none) (get_files thy)
  | get_files_in (files, thy) =
      map (fn binding => (get_file thy binding, Path.pos_of_binding binding)) files;


(* check and output files *)

fun check_files_in ctxt (files, opt_thy) =
  let
    val thy =
      (case opt_thy of
        SOME name => Theory.check {long = false} ctxt name
      | NONE => Proof_Context.theory_of ctxt);
  in (map Path.explode_binding files, thy) end;

fun write_file dir (file: file) =
  let
    val path = Path.expand (dir + #path file);
    val _ = Isabelle_System.make_directory (Path.dir path);
    val _ = File.generate path (#content file);
  in () end;

fun export_file thy (file: file) =
  Export.export thy (file_binding file) [XML.Text (#content file)];


(* file types *)

fun get_file_type thy ext =
  if ext = "" then error "Bad file extension"
  else
    (#2 (Data.get thy), NONE) |-> Name_Space.fold_table
      (fn (_, file_type) => fn res =>
        if #ext file_type = ext then SOME file_type else res)
    |> (fn SOME file_type => file_type
         | NONE => error ("Unknown file type for extension " ^ quote ext));

fun file_type binding {ext, make_comment, make_string} thy =
  let
    val name = Binding.name_of binding;
    val pos = Binding.pos_of binding;
    val file_type = {name = name, ext = ext, make_comment = make_comment, make_string = make_string};

    val table = #2 (Data.get thy);
    val space = Name_Space.space_of_table table;
    val context = Context.Theory thy |> Name_Space.map_naming (K Name_Space.global_naming);
    val (_, data') = table |> Name_Space.define context true (Binding.make (name, pos), file_type);

    val _ =
      (case try (#name o get_file_type thy) ext of
        NONE => ()
      | SOME name' =>
          error ("Extension " ^ quote ext ^ " already registered for file type " ^
            quote (Markup.markup (Name_Space.markup space name') name') ^ Position.here pos));
  in thy |> (Data.map o @{apply 3(2)}) (K data') end;


(* antiquotations *)

val get_antiquotations = #3 o Data.get o Proof_Context.theory_of;

fun antiquotation name scan body thy =
  let
    fun ant src ctxt file_type : string =
      let val (x, ctxt') = Token.syntax scan src ctxt
      in body {context = ctxt', source = src, file_type = file_type, argument = x} end;
  in
    thy
    |> (Data.map o @{apply 3(3)}) (Name_Space.define (Context.Theory thy) true (name, ant) #> #2)
  end;

val scan_antiq =
  Antiquote.scan_control >> Antiquote.Control ||
  Scan.one (Symbol.not_eof o Symbol_Pos.symbol) >> (Antiquote.Text o Symbol_Pos.symbol);

fun read_source ctxt (file_type: file_type) source =
  let
    val _ =
      Context_Position.report ctxt (Input.pos_of source)
        (Markup.language
          {name = #name file_type, symbols = false, antiquotes = true,
            delimited = Input.is_delimited source});

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
            val (src', ant) = Token.check_src ctxt get_antiquotations src;
          in ant src' ctxt file_type end
      | Antiquote.Antiq antiq => error ("Bad antiquotation " ^ Position.here (#1 (#range antiq))));
  in implode (map expand input) end;



(** Isar commands **)

(* generate_file *)

fun generate_file (binding, source) lthy =
  let
    val thy = Proof_Context.theory_of lthy;

    val (path, pos) = Path.dest_binding binding;
    val file_type =
      get_file_type thy (#2 (Path.split_ext path))
        handle ERROR msg => error (msg ^ Position.here pos);

    val header = #make_comment file_type " generated by Isabelle ";
    val content = header ^ "\n" ^ read_source lthy file_type source;
  in lthy |> (Local_Theory.background_theory o add_files) (binding, content) end;

fun generate_file_cmd (file, source) lthy =
  generate_file (Path.explode_binding file, source) lthy;


(* export_generated_files *)

fun export_generated_files ctxt args =
  let val thy = Proof_Context.theory_of ctxt in
    (case map #1 (maps get_files_in args) of
      [] => ()
    | files =>
       (List.app (export_file thy) files;
        writeln (Export.message thy Path.current);
        writeln (cat_lines (map (prefix "  " o print_file) files))))
  end;

fun export_generated_files_cmd ctxt args =
  export_generated_files ctxt (map (check_files_in ctxt) args);


(* compile_generated_files *)

val compile_dir = Config.declare_string ("compile_dir", \<^here>) (K "");

fun with_compile_dir body : unit =
  body (Path.explode (Config.get (Context.the_local_context ()) compile_dir));

fun compile_generated_files ctxt args external export export_prefix source =
  Isabelle_System.with_tmp_dir "compile" (fn dir =>
    let
      val thy = Proof_Context.theory_of ctxt;

      val files = maps get_files_in args;
      val _ = List.app (fn (file, pos) => report_file ctxt pos file) files;
      val _ = List.app (write_file dir o #1) files;
      val _ =
        external |> List.app (fn (files, base_dir) =>
          files |> List.app (fn file => Isabelle_System.copy_file_base (base_dir, file) dir));
      val _ =
        ML_Context.eval_in (SOME (Config.put compile_dir (Path.implode dir) ctxt))
          ML_Compiler.flags (Input.pos_of source)
          (ML_Lex.read "Generated_Files.with_compile_dir (" @
            ML_Lex.read_source source @ ML_Lex.read ")");
      val _ =
        export |> List.app (fn (bindings, executable) =>
          bindings |> List.app (fn binding0 =>
            let
              val binding = binding0 |> Path.map_binding (executable = SOME true ? Path.exe);
              val (path, pos) = Path.dest_binding binding;
              val content =
                (case try File.read (dir + path) of
                  SOME context => context
                | NONE => error ("Missing result file " ^ Path.print path ^ Position.here pos));
              val _ = Export.report_export thy export_prefix;
              val binding' =
                Path.map_binding (Path.append (Path.path_of_binding export_prefix)) binding;
            in
              (if is_some executable then Export.export_executable else Export.export)
                thy binding' [XML.Text content]
            end));
      val _ =
        if null export then ()
        else writeln (Export.message thy (Path.path_of_binding export_prefix));
    in () end);

fun compile_generated_files_cmd ctxt args external export export_prefix source =
  compile_generated_files ctxt
    (map (check_files_in ctxt) args)
    (external |> map (fn (raw_files, raw_base_dir) =>
      let
        val base_dir = Resources.check_dir ctxt NONE raw_base_dir;
        fun check source =
         (Resources.check_file ctxt (SOME base_dir) source;
          Path.explode (Input.string_of source));
        val files = map check raw_files;
      in (files, base_dir) end))
    ((map o apfst o map) Path.explode_binding export)
    (Path.explode_binding export_prefix)
    source;


(* execute compiler -- auxiliary *)

fun execute dir title compile =
  Isabelle_System.bash_process ("cd " ^ File.bash_path dir ^ " && " ^ compile)
  |> Process_Result.check
  |> Process_Result.out
    handle ERROR msg =>
      let val (s, pos) = Input.source_content title
      in error (s ^ " failed" ^ Position.here pos ^ ":\n" ^ msg) end;



(** concrete file types **)

val _ =
  Theory.setup
    (file_type \<^binding>\<open>Haskell\<close>
      {ext = "hs",
       make_comment = enclose "{-" "-}",
       make_string = GHC.print_string});



(** concrete antiquotations **)

(* ML expression as string literal *)

structure Local_Data = Proof_Data
(
  type T = string option;
  fun init _ = NONE;
);

val set_string = Local_Data.put o SOME;

fun the_string ctxt =
  (case Local_Data.get ctxt of
    SOME s => s
  | NONE => raise Fail "No result string");

val _ =
  Theory.setup
    (antiquotation \<^binding>\<open>cartouche\<close> (Scan.lift Args.cartouche_input)
      (fn {context = ctxt, file_type, argument, ...} =>
        ctxt |> Context.proof_map
          (ML_Context.expression (Input.pos_of argument)
            (ML_Lex.read "Theory.local_setup (Generated_Files.set_string (" @
             ML_Lex.read_source argument @ ML_Lex.read "))"))
        |> the_string |> #make_string file_type));


(* file-system paths *)

fun path_antiquotation binding check =
  antiquotation binding
    (Args.context -- Scan.lift Parse.path_input >>
      (fn (ctxt, source) => (check ctxt (SOME Path.current) source |> Path.implode)))
    (fn {file_type, argument, ...} => #make_string file_type argument);

val _ =
  Theory.setup
   (path_antiquotation \<^binding>\<open>path\<close> Resources.check_path #>
    path_antiquotation \<^binding>\<open>file\<close> Resources.check_file #>
    path_antiquotation \<^binding>\<open>dir\<close> Resources.check_dir);

end;
