(*  Title:      Pure/Build/resources.ML
    Author:     Makarius

Resources for theories and auxiliary files.
*)

signature RESOURCES =
sig
  val default_qualifier: string
  val init_session:
    {session_positions: (string * Properties.T) list,
     session_directories: (string * string) list,
     command_timings: Properties.T list,
     load_commands: (string * Position.T) list,
     scala_functions: (string * ((bool * bool) * Position.T)) list,
     global_theories: (string * string) list,
     loaded_theories: string list} -> unit
  val init_session_yxml: Bytes.T -> unit
  val init_session_env: unit -> unit
  val finish_session_base: unit -> unit
  val global_theory: string -> string option
  val loaded_theory: string -> bool
  val check_session: Proof.context -> string * Position.T -> string
  val last_timing: Toplevel.transition -> Time.time
  val check_load_command: Proof.context -> string * Position.T -> string
  val check_scala_function: Proof.context -> string * Position.T -> string * (bool * bool)
  val master_directory: theory -> Path.T
  val imports_of: theory -> (string * Position.T) list
  val begin_theory: Path.T -> Thy_Header.header -> theory list -> theory
  val thy_path: Path.T -> Path.T
  val theory_qualifier: string -> string
  val find_theory_file: string -> Path.T option
  val import_name: string -> Path.T -> string ->
    {node_name: Path.T, master_dir: Path.T, theory_name: string}
  val check_thy: Path.T -> string ->
   {master: Path.T * SHA1.digest, text: string, theory_pos: Position.T,
    imports: (string * Position.T) list, keywords: Thy_Header.keywords}
  val read_file_node: string -> Path.T -> Path.T * Position.T -> Token.file
  val read_file: Path.T -> Path.T * Position.T -> Token.file
  val parsed_files: (Path.T -> Path.T list) ->
    Token.file Exn.result list * Input.source -> theory -> Token.file list
  val parse_files: (Path.T -> Path.T list) -> (theory -> Token.file list) parser
  val parse_file: (theory -> Token.file) parser
  val provide: Path.T * SHA1.digest -> theory -> theory
  val provide_file: Token.file -> theory -> theory
  val provide_file': Token.file -> theory -> Token.file * theory
  val provide_parse_files: (Path.T -> Path.T list) -> (theory -> Token.file list * theory) parser
  val provide_parse_file: (theory -> Token.file * theory) parser
  val loaded_files_current: theory -> bool
  val check_path: Proof.context -> Path.T option -> Input.source -> Path.T
  val check_file: Proof.context -> Path.T option -> Input.source -> Path.T
  val check_dir: Proof.context -> Path.T option -> Input.source -> Path.T
  val check_session_dir: Proof.context -> Path.T option -> Input.source -> Path.T
end;

structure Resources: RESOURCES =
struct

(* command timings *)

type timings = ((string * Time.time) Inttab.table) Symtab.table;  (*file -> offset -> name, time*)

val empty_timings: timings = Symtab.empty;

fun update_timings props =
  (case Markup.parse_command_timing_properties props of
    SOME ({file, offset, name}, time) =>
      Symtab.map_default (file, Inttab.empty)
        (Inttab.map_default (offset, (name, time)) (fn (_, t) => (name, t + time)))
  | NONE => I);

fun make_timings command_timings =
  fold update_timings command_timings empty_timings;

fun approximative_id name pos =
  (case (Position.file_of pos, Position.offset_of pos) of
    (SOME file, SOME offset) =>
      if name = "" then NONE else SOME {file = file, offset = offset, name = name}
  | _ => NONE);

fun get_timings timings tr =
  (case approximative_id (Toplevel.name_of tr) (Toplevel.pos_of tr) of
    SOME {file, offset, name} =>
      (case Symtab.lookup timings file of
        SOME offsets =>
          (case Inttab.lookup offsets offset of
            SOME (name', time) => if name = name' then SOME time else NONE
          | NONE => NONE)
      | NONE => NONE)
  | NONE => NONE)
  |> the_default Time.zeroTime;


(* session base *)

val default_qualifier = "Draft";

type entry = {pos: Position.T, serial: serial};

fun make_entry props : entry =
  {pos = Position.of_properties props, serial = serial ()};

val empty_session_base =
  ({session_positions = []: (string * entry) list,
    session_directories = Symtab.empty: Path.T list Symtab.table,
    timings = empty_timings,
    load_commands = []: (string * Position.T) list,
    scala_functions = Symtab.empty: ((bool * bool) * Position.T) Symtab.table},
   {global_theories = Symtab.empty: string Symtab.table,
    loaded_theories = Symset.empty: Symset.T});

val global_session_base =
  Synchronized.var "Sessions.base" empty_session_base;

fun init_session
    {session_positions, session_directories, command_timings, load_commands,
      scala_functions, global_theories, loaded_theories} =
  Synchronized.change global_session_base
    (fn _ =>
      ({session_positions = sort_by #1 (map (apsnd make_entry) session_positions),
        session_directories =
          Symtab.build (session_directories |> fold_rev (fn (dir, name) =>
            Symtab.cons_list (name, Path.explode dir))),
        timings = make_timings command_timings,
        load_commands = load_commands,
        scala_functions = Symtab.make scala_functions},
       {global_theories = Symtab.make global_theories,
        loaded_theories = Symset.make loaded_theories}));

fun init_session_yxml yxml =
  let
    val (session_positions, (session_directories, (command_timings,
        (load_commands, (scala_functions, (global_theories, loaded_theories)))))) =
      YXML.parse_body_bytes yxml |>
        let open XML.Decode in
          (pair (list (pair string properties))
            (pair (list (pair string string))
              (pair (list properties)
                (pair (list (pair string properties))
                  (pair (list (pair string (pair (pair bool bool) properties)))
                    (pair (list (pair string string)) (list string)))))))
        end;
  in
    init_session
      {session_positions = session_positions,
       session_directories = session_directories,
       command_timings = command_timings,
       load_commands = (map o apsnd) Position.of_properties load_commands,
       scala_functions = (map o apsnd o apsnd) Position.of_properties scala_functions,
       global_theories = global_theories,
       loaded_theories = loaded_theories}
  end;

fun init_session_env () =
  (case getenv "ISABELLE_INIT_SESSION" of
    "" => ()
  | name =>
      try Bytes.read (Path.explode name)
      |> Option.app init_session_yxml);

val _ = init_session_env ();

fun finish_session_base () =
  Synchronized.change global_session_base
    (apfst (K (#1 empty_session_base)));

fun get_session_base f = f (Synchronized.value global_session_base);
fun get_session_base1 f = get_session_base (f o #1);
fun get_session_base2 f = get_session_base (f o #2);

fun global_theory a = Symtab.lookup (get_session_base2 #global_theories) a;
fun loaded_theory a = Symset.member (get_session_base2 #loaded_theories) a;

fun check_session ctxt arg =
  Completion.check_item "session"
    (fn (name, {pos, serial}) =>
      Position.make_entity_markup {def = false} serial Markup.sessionN (name, pos))
    (get_session_base1 #session_positions) ctxt arg;

fun last_timing tr = get_timings (get_session_base1 #timings) tr;

fun check_load_command ctxt arg =
  Completion.check_entity Markup.load_commandN (get_session_base1 #load_commands) ctxt arg;


(* Scala functions *)

fun check_scala_function ctxt arg =
  let
    val table = get_session_base1 #scala_functions;
    val funs = Symtab.fold (fn (a, (_, pos)) => cons (a, pos)) table [] |> sort_by #1;
    val name = Completion.check_entity Markup.scala_functionN funs ctxt arg;
    val flags = #1 (the (Symtab.lookup table name));
  in (name, flags) end;

val _ = Theory.setup
 (Document_Output.antiquotation_verbatim_embedded \<^binding>\<open>scala_function\<close>
    (Scan.lift Parse.embedded_position) (#1 oo check_scala_function) #>
  ML_Antiquotation.inline_embedded \<^binding>\<open>scala_function\<close>
    (Args.context -- Scan.lift Parse.embedded_position
      >> (uncurry check_scala_function #> #1 #> ML_Syntax.print_string)) #>
  ML_Antiquotation.value_embedded \<^binding>\<open>scala\<close>
    (Args.context -- Scan.lift Parse.embedded_position >> (fn (ctxt, arg) =>
      let
        val (name, (single, bytes)) = check_scala_function ctxt arg;
        val func =
          (if single then "Scala.function1" else "Scala.function") ^
          (if bytes then "_bytes" else "");
      in ML_Syntax.atomic (func ^ " " ^ ML_Syntax.print_string name) end)));


(* manage source files *)

type files =
 {master_dir: Path.T,  (*master directory of theory source*)
  imports: (string * Position.T) list,  (*source specification of imports*)
  provided: (Path.T * SHA1.digest) list};  (*source path, digest*)

fun make_files (master_dir, imports, provided): files =
 {master_dir = master_dir, imports = imports, provided = provided};

structure Files = Theory_Data
(
  type T = files;
  val empty = make_files (Path.current, [], []);
  fun merge ({master_dir, imports, provided = provided1}, {provided = provided2, ...}) =
    let val provided' = Library.merge (op =) (provided1, provided2)
    in make_files (master_dir, imports, provided') end
);

fun map_files f =
  Files.map (fn {master_dir, imports, provided} =>
    make_files (f (master_dir, imports, provided)));


val master_directory = #master_dir o Files.get;
val imports_of = #imports o Files.get;

fun begin_theory master_dir {name, imports, keywords} parents =
  let
    val thy =
      Theory.begin_theory name parents
      |> map_files (fn _ => (Path.explode (File.symbolic_path master_dir), imports, []))
      |> Thy_Header.add_keywords keywords;
    val ctxt = Proof_Context.init_global thy;
    val _ = List.app (ignore o check_load_command ctxt o #load_command o #2) keywords;
  in thy end;


(* theory files *)

val thy_path = Path.ext "thy";

fun theory_qualifier theory =
  (case global_theory theory of
    SOME qualifier => qualifier
  | NONE => Long_Name.qualifier theory);

fun literal_theory theory =
  Long_Name.is_qualified theory orelse is_some (global_theory theory);

fun theory_name qualifier theory =
  if literal_theory theory then theory
  else Long_Name.qualify qualifier theory;

fun find_theory_file thy_name =
  let
    val thy_file = thy_path (Path.basic (Long_Name.base_name thy_name));
    val session = theory_qualifier thy_name;
    val dirs = Symtab.lookup_list (get_session_base1 #session_directories) session;
  in
    dirs |> get_first (fn dir =>
      let val path = dir + thy_file
      in if File.is_file path then SOME path else NONE end)
  end;

fun make_theory_node node_name theory =
  {node_name = node_name, master_dir = Path.dir node_name, theory_name = theory};

fun loaded_theory_node theory =
  {node_name = Path.basic theory, master_dir = Path.current, theory_name = theory};

fun import_name qualifier dir s =
  let
    val theory = theory_name qualifier (Thy_Header.import_name s);
    fun theory_node path = make_theory_node path theory;
    val literal_import = literal_theory theory andalso qualifier <> theory_qualifier theory;
    val _ =
      if literal_import andalso not (Thy_Header.is_base_name s) then
        error ("Bad import of theory from other session via file-path: " ^ quote s)
      else ();
  in
    if loaded_theory theory then loaded_theory_node theory
    else
      (case find_theory_file theory of
        SOME node_name => theory_node node_name
      | NONE =>
          if Thy_Header.is_base_name s andalso Long_Name.is_qualified s
          then loaded_theory_node theory
          else theory_node (File.full_path dir (thy_path (Path.expand (Path.explode s)))))
  end;

fun check_file dir file = File.check_file (File.full_path dir file);

fun check_thy dir thy_name =
  let
    val thy_base_name = Long_Name.base_name thy_name;
    val master_file =
      (case find_theory_file thy_name of
        SOME path => check_file Path.current path
      | NONE => check_file dir (thy_path (Path.basic thy_base_name)));
    val text = File.read master_file;

    val {name = (name, pos), imports, keywords} =
      Thy_Header.read (Position.file (File.symbolic_path master_file)) text;
    val _ =
      thy_base_name <> name andalso
        error ("Bad theory name " ^ quote name ^
          " for file " ^ Path.print (Path.base master_file) ^ Position.here pos);
  in
   {master = (master_file, SHA1.digest text), text = text, theory_pos = pos,
    imports = imports, keywords = keywords}
  end;


(* read_file *)

fun read_file_node file_node master_dir (src_path, pos) =
  let
    fun read_local () =
      let
        val path = File.check_file (File.full_path master_dir src_path);
        val text = File.read path;
        val file_pos = Position.file (File.symbolic_path path);
      in (text, file_pos) end;

    fun read_remote () =
      let
        val text = Bytes.content (Isabelle_System.download file_node);
        val file_pos = Position.file file_node;
      in (text, file_pos) end;

    val (text, file_pos) =
      (case try Url.explode file_node of
        NONE => read_local ()
      | SOME (Url.File _) => read_local ()
      | _ => read_remote ());

    val lines = split_lines text;
    val digest = SHA1.digest text;
  in {src_path = src_path, lines = lines, digest = digest, pos = Position.copy_id pos file_pos} end
  handle ERROR msg => error (msg ^ Position.here pos);

val read_file = read_file_node "";


(* load files *)

fun parsed_files make_paths (files, source) thy =
  if null files then
    let
      val master_dir = master_directory thy;
      val name = Input.string_of source;
      val pos = Input.pos_of source;
      val delimited = Input.is_delimited source;
      val src_paths = make_paths (Path.explode name);
      val reports =
        src_paths |> maps (fn src_path =>
          [(pos, Markup.path (File.symbolic_path (master_dir + src_path))),
           (pos, Markup.language_path delimited)]);
      val _ = Position.reports reports;
    in map (read_file master_dir o rpair pos) src_paths end
  else map Exn.release files;

fun parse_files make_paths =
  (Scan.ahead Parse.not_eof >> Token.get_files) -- Parse.path_input >> parsed_files make_paths;

val parse_file = parse_files single >> (fn f => f #> the_single);


fun provide (src_path, digest) =
  map_files (fn (master_dir, imports, provided) =>
    if AList.defined (op =) provided src_path then
      error ("Duplicate use of source file: " ^ Path.print src_path)
    else (master_dir, imports, (src_path, digest) :: provided));

fun provide_file (file: Token.file) = provide (#src_path file, #digest file);
fun provide_file' file thy = (file, provide_file file thy);

fun provide_parse_files make_paths =
  parse_files make_paths >> (fn files => fn thy => fold_map provide_file' (files thy) thy);

val provide_parse_file = provide_parse_files single >> (fn f => f #>> the_single);


fun load_file thy src_path =
  let
    val full_path = check_file (master_directory thy) src_path;
    val text = File.read full_path;
    val digest = SHA1.digest text;
  in ((full_path, digest), text) end;

fun loaded_files_current thy =
  #provided (Files.get thy) |>
    forall (fn (src_path, digest) =>
      (case try (load_file thy) src_path of
        NONE => false
      | SOME ((_, digest'), _) => digest = digest'));


(* formal check *)

fun formal_check (check: Path.T -> Path.T) ctxt opt_dir source =
  let
    val name = Input.string_of source;
    val pos = Input.pos_of source;
    val delimited = Input.is_delimited source;

    val _ = Context_Position.report ctxt pos (Markup.language_path delimited);

    fun err msg = error (msg ^ Position.here pos);
    val dir =
      (case opt_dir of
        SOME dir => dir
      | NONE => master_directory (Proof_Context.theory_of ctxt));
    val path = dir + Path.explode name handle ERROR msg => err msg;
    val _ = Path.expand path handle ERROR msg => err msg;
    val _ = Context_Position.report ctxt pos (Markup.path (File.symbolic_path path));
    val _ = check path handle ERROR msg => err msg;
  in path end;

val check_path = formal_check I;
val check_file = formal_check File.check_file;
val check_dir = formal_check File.check_dir;

fun check_session_dir ctxt opt_dir s =
  let
    val dir = Path.expand (check_dir ctxt opt_dir s);
    val ok =
      File.is_file (dir + Path.explode("ROOT")) orelse
      File.is_file (dir + Path.explode("ROOTS"));
  in
    if ok then dir
    else
      error ("Bad session root directory (missing ROOT or ROOTS): " ^
        Path.print dir ^ Position.here (Input.pos_of s))
  end;


(* antiquotations *)

local

fun document_antiq (check: Proof.context -> Path.T option -> Input.source -> Path.T) =
  Args.context -- Scan.lift Parse.path_input >> (fn (ctxt, source) =>
   (check ctxt NONE source;
    Latex.string (Latex.output_ascii_breakable "/" (Input.string_of source))
    |> Latex.macro "isatt"));

fun ML_antiq check =
  Args.context -- Scan.lift Parse.path_input >> (fn (ctxt, source) =>
    check ctxt (SOME Path.current) source |> ML_Syntax.print_path);

in

val _ = Theory.setup
 (Document_Output.antiquotation_verbatim_embedded \<^binding>\<open>session\<close>
    (Scan.lift Parse.embedded_position) check_session #>
  Document_Output.antiquotation_raw_embedded \<^binding>\<open>path\<close> (document_antiq check_path) (K I) #>
  Document_Output.antiquotation_raw_embedded \<^binding>\<open>file\<close> (document_antiq check_file) (K I) #>
  Document_Output.antiquotation_raw_embedded \<^binding>\<open>dir\<close> (document_antiq check_dir) (K I) #>
  ML_Antiquotation.value_embedded \<^binding>\<open>path\<close> (ML_antiq check_path) #>
  ML_Antiquotation.value_embedded \<^binding>\<open>file\<close> (ML_antiq check_file) #>
  ML_Antiquotation.value_embedded \<^binding>\<open>dir\<close> (ML_antiq check_dir) #>
  ML_Antiquotation.value_embedded \<^binding>\<open>path_binding\<close>
    (Scan.lift (Parse.position Parse.path) >>
      (ML_Syntax.print_path_binding o Path.explode_binding)) #>
  ML_Antiquotation.value \<^binding>\<open>master_dir\<close>
    (Args.theory >> (ML_Syntax.print_path o master_directory)));

end;

end;
