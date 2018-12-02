(*  Title:      Pure/Tools/generated_files.ML
    Author:     Makarius

Generated source files for other languages: with antiquotations, without Isabelle symbols.
*)

signature GENERATED_FILES =
sig
  val add_files: (Path.T * Position.T) * string -> theory -> theory
  val get_files: theory -> (Path.T * string) list
  val write_files: theory -> Path.T -> Path.T list
  type file_type =
    {name: string, ext: string, make_comment: string -> string, make_string: string -> string}
  val file_type:
    binding -> {ext: string, make_comment: string -> string, make_string: string -> string} ->
    theory -> theory
  val antiquotation: binding -> 'a Token.context_parser ->
    ({context: Proof.context, source: Token.src, file_type: file_type, argument: 'a} -> string) ->
    theory -> theory
  val set_string: string -> Proof.context -> Proof.context
  val generate_file_cmd: (string * Position.T) * Input.source -> local_theory -> local_theory
end;

structure Generated_Files: GENERATED_FILES =
struct

(** context data **)

type file_type =
  {name: string, ext: string, make_comment: string -> string, make_string: string -> string};

type antiquotation = Token.src -> Proof.context -> file_type -> string;

structure Data = Theory_Data
(
  type T =
    (Path.T * (Position.T * string)) list *  (*files for current theory*)
    file_type Name_Space.table *  (*file types*)
    antiquotation Name_Space.table;  (*antiquotations*)
  val empty =
    ([],
     Name_Space.empty_table Markup.file_typeN,
     Name_Space.empty_table Markup.antiquotationN);
  val extend = @{apply 3(1)} (K []);
  fun merge ((_, types1, antiqs1), (_, types2, antiqs2)) =
    ([],
     Name_Space.merge_tables (types1, types2),
     Name_Space.merge_tables (antiqs1, antiqs2));
);


(* files *)

fun add_files ((path0, pos), text) =
  let
    val path = Path.expand path0;
    fun err msg ps = error (msg ^ ": " ^ Path.print path ^ Position.here_list ps);
    val _ =
      if Path.is_absolute path then err "Illegal absolute path" [pos]
      else if Path.has_parent path then err "Illegal parent path" [pos]
      else ();
  in
    (Data.map o @{apply 3(1)}) (fn files =>
      (case AList.lookup (op =) files path of
        SOME (pos', _) => err "Duplicate generated file" [pos, pos']
      | NONE => (path, (pos, text)) :: files))
  end;

val get_files = map (apsnd #2) o rev o #1 o Data.get;

fun write_files thy dir =
  get_files thy |> map (fn (path, text) =>
    let
      val path' = Path.expand (Path.append dir path);
      val _ = Isabelle_System.mkdirs (Path.dir path');
      val _ = File.generate path' text;
    in path end);


(* file types *)

fun the_file_type thy ext =
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
      (case try (#name o the_file_type thy) ext of
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


(* generate files *)

fun generate_file_cmd ((file, pos), source) lthy =
  let
    val thy = Proof_Context.theory_of lthy;

    val path = Path.explode file;
    val file_type =
      the_file_type thy (#2 (Path.split_ext path))
        handle ERROR msg => error (msg ^ Position.here pos);

    val header = #make_comment file_type " generated by Isabelle ";
    val text = header ^ "\n" ^ read_source lthy file_type source;
  in lthy |> (Local_Theory.background_theory o add_files) ((path, pos), text) end;

 

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
    (Args.context -- Scan.lift (Parse.position Parse.path) >>
      (fn (ctxt, (name, pos)) => (check ctxt Path.current (name, pos) |> Path.implode)))
    (fn {file_type, argument, ...} => #make_string file_type argument);

val _ =
  Theory.setup
   (path_antiquotation \<^binding>\<open>path\<close> Resources.check_path #>
    path_antiquotation \<^binding>\<open>file\<close> Resources.check_file #>
    path_antiquotation \<^binding>\<open>dir\<close> Resources.check_dir);

end;
