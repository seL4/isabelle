(*  Title:      Pure/PIDE/resources.ML
    Author:     Makarius

Resources for theories and auxiliary files.
*)

signature RESOURCES =
sig
  val default_qualifier: string
  val init_session_base:
    {global_theories: (string * string) list,
     loaded_theories: string list,
     known_theories: (string * string) list} -> unit
  val finish_session_base: unit -> unit
  val global_theory: string -> string option
  val loaded_theory: string -> bool
  val known_theory: string -> Path.T option
  val master_directory: theory -> Path.T
  val imports_of: theory -> (string * Position.T) list
  val begin_theory: Path.T -> Thy_Header.header -> theory list -> theory
  val thy_path: Path.T -> Path.T
  val theory_qualifier: string -> string
  val import_name: string -> Path.T -> string -> {master_dir: Path.T, theory_name: string}
  val check_thy: Path.T -> string ->
   {master: Path.T * SHA1.digest, text: string, theory_pos: Position.T,
    imports: (string * Position.T) list, keywords: Thy_Header.keywords}
  val parse_files: string -> (theory -> Token.file list) parser
  val provide: Path.T * SHA1.digest -> theory -> theory
  val provide_parse_files: string -> (theory -> Token.file list * theory) parser
  val loaded_files_current: theory -> bool
end;

structure Resources: RESOURCES =
struct

(* session base *)

val default_qualifier = "Draft";

val empty_session_base =
  {global_theories = Symtab.empty: string Symtab.table,
   loaded_theories = Symtab.empty: unit Symtab.table,
   known_theories = Symtab.empty: Path.T Symtab.table};

val global_session_base =
  Synchronized.var "Sessions.base" empty_session_base;

fun init_session_base {global_theories, loaded_theories, known_theories} =
  Synchronized.change global_session_base
    (fn _ =>
      {global_theories = Symtab.make global_theories,
       loaded_theories = Symtab.make_set loaded_theories,
       known_theories = Symtab.make (map (apsnd Path.explode) known_theories)});

fun finish_session_base () =
  Synchronized.change global_session_base
    (fn {global_theories, loaded_theories, ...} =>
      {global_theories = global_theories,
       loaded_theories = loaded_theories,
       known_theories = #known_theories empty_session_base});

fun get_session_base f = f (Synchronized.value global_session_base);

fun global_theory a = Symtab.lookup (get_session_base #global_theories) a;
fun loaded_theory a = Symtab.defined (get_session_base #loaded_theories) a;
fun known_theory a = Symtab.lookup (get_session_base #known_theories) a;


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
  fun extend _ = empty;
  fun merge _ = empty;
);

fun map_files f =
  Files.map (fn {master_dir, imports, provided} =>
    make_files (f (master_dir, imports, provided)));


val master_directory = #master_dir o Files.get;
val imports_of = #imports o Files.get;

fun begin_theory master_dir {name, imports, keywords} parents =
  Theory.begin_theory name parents
  |> map_files (fn _ => (master_dir, imports, []))
  |> Thy_Header.add_keywords keywords;


(* theory files *)

val thy_path = Path.ext "thy";

fun theory_qualifier theory =
  (case global_theory theory of
    SOME qualifier => qualifier
  | NONE => Long_Name.qualifier theory);

fun theory_name qualifier theory =
  if loaded_theory theory then (true, theory)
  else
    let val theory' =
      if Long_Name.is_qualified theory orelse is_some (global_theory theory)
      then theory
      else Long_Name.qualify qualifier theory
    in (false, theory') end;

fun import_name qualifier dir s =
  (case theory_name qualifier (Thy_Header.import_name s) of
    (true, theory) => {master_dir = Path.current, theory_name = theory}
  | (false, theory) =>
      let val node_name =
        (case known_theory theory of
          SOME node_name => node_name
        | NONE => File.full_path dir (thy_path (Path.expand (Path.explode s))))
      in {master_dir = Path.dir node_name, theory_name = theory} end);

fun check_file dir file = File.check_file (File.full_path dir file);

fun check_thy dir thy_name =
  let
    val thy_base_name = Long_Name.base_name thy_name;
    val master_file =
      (case known_theory thy_name of
        SOME known_path => check_file Path.current known_path
      | NONE => check_file dir (thy_path (Path.basic thy_base_name)));
    val text = File.read master_file;

    val {name = (name, pos), imports, keywords} =
      Thy_Header.read (Path.position master_file) text;
    val _ =
      thy_base_name <> name andalso
        error ("Bad theory name " ^ quote name ^
          " for file " ^ Path.print (Path.base master_file) ^ Position.here pos);
  in
   {master = (master_file, SHA1.digest text), text = text, theory_pos = pos,
    imports = imports, keywords = keywords}
  end;


(* load files *)

fun parse_files cmd =
  Scan.ahead Parse.not_eof -- Parse.path >> (fn (tok, name) => fn thy =>
    (case Token.get_files tok of
      [] =>
        let
          val keywords = Thy_Header.get_keywords thy;
          val master_dir = master_directory thy;
          val pos = Token.pos_of tok;
          val src_paths = Keyword.command_files keywords cmd (Path.explode name);
        in map (Command.read_file master_dir pos) src_paths end
    | files => map Exn.release files));

fun provide (src_path, id) =
  map_files (fn (master_dir, imports, provided) =>
    if AList.defined (op =) provided src_path then
      error ("Duplicate use of source file: " ^ Path.print src_path)
    else (master_dir, imports, (src_path, id) :: provided));

fun provide_parse_files cmd =
  parse_files cmd >> (fn files => fn thy =>
    let
      val fs = files thy;
      val thy' = fold (fn {src_path, digest, ...} => provide (src_path, digest)) fs thy;
    in (fs, thy') end);

fun load_file thy src_path =
  let
    val full_path = check_file (master_directory thy) src_path;
    val text = File.read full_path;
    val id = SHA1.digest text;
  in ((full_path, id), text) end;

fun loaded_files_current thy =
  #provided (Files.get thy) |>
    forall (fn (src_path, id) =>
      (case try (load_file thy) src_path of
        NONE => false
      | SOME ((_, id'), _) => id = id'));


(* antiquotations *)

local

fun err msg pos = error (msg ^ Position.here pos);

fun check_path check_file ctxt dir (name, pos) =
  let
    val _ = Context_Position.report ctxt pos Markup.language_path;

    val path = Path.append dir (Path.explode name) handle ERROR msg => err msg pos;
    val _ = Path.expand path handle ERROR msg => err msg pos;
    val _ = Context_Position.report ctxt pos (Markup.path (Path.smart_implode path));
    val _ =
      (case check_file of
        NONE => path
      | SOME check => (check path handle ERROR msg => err msg pos));
  in path end;

fun document_antiq check_file ctxt (name, pos) =
  let
    val dir = master_directory (Proof_Context.theory_of ctxt);
    val _ = check_path check_file ctxt dir (name, pos);
  in
    space_explode "/" name
    |> map Latex.output_ascii
    |> space_implode (Latex.output_ascii "/" ^ "\\discretionary{}{}{}")
    |> enclose "\\isatt{" "}"
  end;

fun ML_antiq check_file ctxt (name, pos) =
  let val path = check_path check_file ctxt Path.current (name, pos);
  in "Path.explode " ^ ML_Syntax.print_string (Path.implode path) end;

in

val _ = Theory.setup
 (Thy_Output.antiquotation @{binding path} (Scan.lift (Parse.position Parse.path))
    (document_antiq NONE o #context) #>
  Thy_Output.antiquotation @{binding file} (Scan.lift (Parse.position Parse.path))
    (document_antiq (SOME File.check_file) o #context) #>
  Thy_Output.antiquotation @{binding dir} (Scan.lift (Parse.position Parse.path))
    (document_antiq (SOME File.check_dir) o #context) #>
  ML_Antiquotation.value @{binding path}
    (Args.context -- Scan.lift (Parse.position Parse.path)
      >> uncurry (ML_antiq NONE)) #>
  ML_Antiquotation.value @{binding file}
    (Args.context -- Scan.lift (Parse.position Parse.path)
      >> uncurry (ML_antiq (SOME File.check_file))) #>
  ML_Antiquotation.value @{binding dir}
    (Args.context -- Scan.lift (Parse.position Parse.path)
      >> uncurry (ML_antiq (SOME File.check_dir))));

end;

end;
