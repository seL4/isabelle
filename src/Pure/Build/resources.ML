(*  Title:      Pure/Build/resources.ML
    Author:     Makarius

Resources for theories and auxiliary files.
*)

signature RESOURCES =
sig
  val default_qualifier: string
  type scala_fun = {single: bool, bytes: bool, pos: Position.T}
  val init_session:
    {session_positions: (string * Properties.T) list,
     session_directories: (string * string) list,
     command_timings: Properties.T list,
     load_commands: (string * Position.T) list,
     scala_functions: (string * scala_fun) list,
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
  val check_scala_function: Proof.context -> string * Position.T -> string * scala_fun
  val master_directory: theory -> Path.T
  type node_name = {node: string, master_dir: Path.T, theory: string}
  val node_name: string -> node_name
  val empty_node_name: node_name
  val decode_node_name: node_name XML.Decode.T
  type thy =
   {name: node_name,
    pos: Position.T,
    imports: (node_name * Position.T) list,
    options: Options.update_pos,
    keywords: Thy_Header.keywords,
    condition_bad: bool * string,
    errors: string list,
    initiators: node_name list}
  val no_thy: thy
  val decode_thy: thy XML.Decode.T
  val map_thy_pos: (Position.T -> Position.T) -> thy -> thy
  val map_thy_errors: (string list -> string list) -> thy -> thy
  val check_thy_errors: thy -> thy
  val skip_theory: thy -> bool
  val skip_proofs: thy -> bool
  val skipping_theory: (string -> unit) -> thy -> unit
  val begin_theory: thy -> theory list -> theory
  val theory_qualifier: string -> string
  val find_theory_file: string -> Path.T option
  val import_name: string -> Path.T -> string ->
    {node_name: Path.T, master_dir: Path.T, theory_name: string}
  val read_file_node: string -> Path.T -> Path.T * Position.T -> Token.file
  val read_file: Path.T -> Path.T * Position.T -> Token.file
  val parsed_files: (Path.T -> Path.T list) ->
    Token.file Exn.result list * Input.source -> theory -> Token.file list
  val parse_files: (Path.T -> Path.T list) -> (theory -> Token.file list) parser
  val parse_file: (theory -> Token.file) parser
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

type scala_fun = {single: bool, bytes: bool, pos: Position.T};

val default_qualifier = "Draft";

type entry = {pos: Position.T, serial: serial};

fun make_entry props : entry =
  {pos = Position.of_properties props, serial = serial ()};

val empty_session_base =
  ({session_positions = []: (string * entry) list,
    session_directories = Symtab.empty: Path.T list Symtab.table,
    timings = empty_timings,
    load_commands = []: (string * Position.T) list,
    scala_functions = Symtab.empty: scala_fun Symtab.table},
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
        let
          open XML.Decode;
          val scala_fun =
            triple bool bool properties #>
            (fn (a, b, p) => {single = a, bytes = b, pos = Position.of_properties p});
        in
          (pair (list (pair string properties))
            (pair (list (pair string string))
              (pair (list properties)
                (pair (list (pair string properties))
                  (pair (list (pair string scala_fun))
                    (pair (list (pair string string)) (list string)))))))
        end;
  in
    init_session
      {session_positions = session_positions,
       session_directories = session_directories,
       command_timings = command_timings,
       load_commands = (map o apsnd) Position.of_properties load_commands,
       scala_functions = scala_functions,
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
    val funs = Symtab.fold (fn (a, {pos, ...}) => cons (a, pos)) table [] |> sort_by #1;
    val name = Completion.check_entity Markup.scala_functionN funs ctxt arg;
  in (name, the (Symtab.lookup table name)) end;

val _ = Theory.setup
 (Document_Output.antiquotation_verbatim_embedded \<^binding>\<open>scala_function\<close>
    (Scan.lift Parse.embedded_position) (#1 oo check_scala_function) #>
  ML_Antiquotation.inline_embedded \<^binding>\<open>scala_function\<close>
    (Args.context -- Scan.lift Parse.embedded_position
      >> (uncurry check_scala_function #> #1 #> ML_Syntax.print_string)) #>
  ML_Antiquotation.value_embedded \<^binding>\<open>scala\<close>
    (Args.context -- Scan.lift Parse.embedded_position >> (fn (ctxt, arg) =>
      let
        val (name, {single, bytes, ...}) = check_scala_function ctxt arg;
        val func =
          (if single then "Scala.function1" else "Scala.function") ^
          (if bytes then "_bytes" else "");
      in ML_Syntax.atomic (func ^ " " ^ ML_Syntax.print_string name) end)));


(* theory resources and entries *)

structure Data = Theory_Data
(
  type T = Path.T;  (*master directory of theory source*)
  val empty = Path.current;
  val merge = fst;
);

val master_directory = Data.get;


type node_name = {node: string, master_dir: Path.T, theory: string};

fun node_name node : node_name = {node = node, master_dir = Path.current, theory = ""};
val empty_node_name: node_name = {node = "", master_dir = Path.current, theory = ""};

val decode_node_name: node_name XML.Decode.T =
  let open XML.Decode
  in triple string (Path.explode o string) string end
  #> (fn (node, master_dir, theory) => {node = node, master_dir = master_dir, theory = theory});


type thy =
 {name: node_name,
  pos: Position.T,
  imports: (node_name * Position.T) list,
  options: Options.update_pos,
  keywords: Thy_Header.keywords,
  condition_bad: bool * string,
  errors: string list,
  initiators: node_name list};

val no_thy: thy =
 {name = empty_node_name, pos = Position.none, imports = [], options = [],
   keywords = [], condition_bad = (false, ""), errors = [], initiators = []};

val decode_thy: thy XML.Decode.T =
  let
    open XML.Decode;
    val position = Position.of_properties o properties;
    val string_none = rpair Position.none o string;
    val keyword = pair string_none (Keyword.command_spec o pair string (list string));
  in
    pair decode_node_name
      (pair position
        (pair (list (pair decode_node_name position))
          (pair (list (pair string_none (option string_none)))
            (pair (list keyword) (pair (pair bool YXML.string_of_body)
              ((pair (list YXML.string_of_body) (list decode_node_name))))))))
  end
  #> (fn (name, (pos, (imports, (options, (keywords, (condition_bad, (errors, initiators))))))) =>
      {name = name, pos = pos, imports = imports, options = options, keywords = keywords,
        condition_bad = condition_bad, errors = errors, initiators = initiators});

fun map_thy_pos f
  ({name, pos, imports, options, keywords, condition_bad, errors, initiators}: thy) : thy =
   {name = name, pos = f pos, imports = map (apsnd f) imports,
    options = map (fn (a, b) => (apsnd f a, Option.map (apsnd f) b)) options,
    keywords = keywords, condition_bad = condition_bad, errors = errors, initiators = initiators};

fun map_thy_errors f
  ({name, pos, imports, options, keywords, condition_bad, errors, initiators}: thy) : thy =
   {name = name, pos = pos, imports = imports, options = options, keywords = keywords,
    condition_bad = condition_bad, errors = f errors, initiators = initiators};

fun check_thy_errors (thy: thy) =
  (case #errors thy of
    [] => thy
  | errs =>
      error (Protocol_Message.command_positions_yxml (Position.thread_data ()) (cat_lines errs)));


(* begin theory *)

fun skip_theory ({condition_bad = (proofs, bad), ...}: thy) = bad <> "" andalso not proofs;
fun skip_proofs ({condition_bad = (proofs, bad), ...}: thy) = bad <> "" andalso proofs;

fun skipping_theory output (thy as {name = {theory, ...}, condition_bad = (_, bad), ...}: thy) =
  let fun out msg = output (msg ^ " " ^ quote theory ^ " " ^ bad) in
    if skip_theory thy then out "Skipping theory"
    else if skip_proofs thy then out "Skipping proofs of theory"
    else ()
  end;

fun begin_theory ({name, pos, keywords, ...}: thy) parents =
  let
    val master_dir = Path.explode (File.symbolic_path (#master_dir name));
    val thy =
      Theory.begin_theory (#theory name, pos) parents
      |> Data.put master_dir
      |> Thy_Header.add_keywords keywords;
    val ctxt = Proof_Context.init_global thy;
    val _ = List.app (ignore o check_load_command ctxt o #load_command o #2) keywords;
  in thy end;


(* theory files *)

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
    val thy_file = Path.thy (Path.basic (Long_Name.base_name thy_name));
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
          else theory_node (File.full_path dir (Path.thy (Path.expand (Path.explode s)))))
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
  in {src_path = src_path, lines = lines, pos = Position.copy_id pos file_pos} end
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
