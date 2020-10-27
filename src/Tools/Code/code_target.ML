(*  Title:      Tools/Code/code_target.ML
    Author:     Florian Haftmann, TU Muenchen

Generic infrastructure for target language data.
*)

signature CODE_TARGET =
sig
  val cert_tyco: Proof.context -> string -> string
  val read_tyco: Proof.context -> string -> string

  datatype pretty_modules = Singleton of string * Pretty.T | Hierarchy of (string list * Pretty.T) list;
  val next_export: theory -> string * theory

  val export_code_for: ({physical: bool} * (Path.T * Position.T)) option -> string -> string
    -> int option -> Token.T list  -> Code_Thingol.program -> bool -> Code_Symbol.T list
    -> local_theory -> local_theory
  val produce_code_for: Proof.context -> string -> string -> int option -> Token.T list
    -> Code_Thingol.program -> bool -> Code_Symbol.T list -> (string list * string) list * string option list
  val present_code_for: Proof.context -> string -> string -> int option -> Token.T list
    -> Code_Thingol.program -> Code_Symbol.T list * Code_Symbol.T list -> string
  val check_code_for: string -> bool -> Token.T list
    -> Code_Thingol.program -> bool -> Code_Symbol.T list -> local_theory -> local_theory

  val export_code: bool -> string list
    -> (((string * string) * ({physical: bool} * (Path.T * Position.T)) option) * Token.T list) list
    -> local_theory -> local_theory
  val export_code_cmd: bool -> string list
    -> (((string * string) * ({physical: bool} * (string * Position.T)) option) * Token.T list) list
    -> local_theory -> local_theory
  val produce_code: Proof.context -> bool -> string list
    -> string -> string -> int option -> Token.T list -> (string list * string) list * string option list
  val present_code: Proof.context -> string list -> Code_Symbol.T list
    -> string -> string -> int option -> Token.T list -> string
  val check_code: bool -> string list -> ((string * bool) * Token.T list) list
    -> local_theory -> local_theory

  val codeN: string
  val generatedN: string
  val code_path: Path.T -> Path.T
  val code_export_message: theory -> unit
  val export: Path.binding -> string -> theory -> theory
  val compilation_text: Proof.context -> string -> Code_Thingol.program
    -> Code_Symbol.T list -> bool -> ((string * class list) list * Code_Thingol.itype) * Code_Thingol.iterm
    -> (string list * string) list * string
  val compilation_text': Proof.context -> string -> string option -> Code_Thingol.program
    -> Code_Symbol.T list -> bool -> ((string * class list) list * Code_Thingol.itype) * Code_Thingol.iterm
    -> ((string list * string) list * string) * (Code_Symbol.T -> string option)

  type serializer
  type literals = Code_Printer.literals
  type language
  type ancestry
  val assert_target: theory -> string -> string
  val add_language: string * language -> theory -> theory
  val add_derived_target: string * ancestry -> theory -> theory
  val the_literals: Proof.context -> string -> literals
  val parse_args: 'a parser -> Token.T list -> 'a
  val default_code_width: int Config.T

  type ('a, 'b, 'c, 'd, 'e, 'f) symbol_attr_decl
  val set_identifiers: (string, string, string, string, string, string) symbol_attr_decl
    -> theory -> theory
  val set_printings: (Code_Printer.raw_const_syntax, Code_Printer.tyco_syntax, string, unit, unit, string * Code_Symbol.T list) symbol_attr_decl
    -> theory -> theory
  val add_reserved: string -> string -> theory -> theory
end;

structure Code_Target : CODE_TARGET =
struct

open Basic_Code_Symbol;
open Basic_Code_Thingol;

type literals = Code_Printer.literals;
type ('a, 'b, 'c, 'd, 'e, 'f) symbol_attr_decl =
  (string * (string * 'a option) list, string * (string * 'b option) list,
    class * (string * 'c option) list, (class * class) * (string * 'd option) list,
    (class * string) * (string * 'e option) list,
    string * (string * 'f option) list) Code_Symbol.attr;

type tyco_syntax = Code_Printer.tyco_syntax;
type raw_const_syntax = Code_Printer.raw_const_syntax;


(** checking and parsing of symbols **)

fun cert_const ctxt const =
  let
    val _ = if Sign.declared_const (Proof_Context.theory_of ctxt) const then ()
      else error ("No such constant: " ^ quote const);
  in const end;

fun read_const ctxt = Code.read_const (Proof_Context.theory_of ctxt);

fun cert_tyco ctxt tyco =
  let
    val _ = if Sign.declared_tyname (Proof_Context.theory_of ctxt) tyco then ()
      else error ("No such type constructor: " ^ quote tyco);
  in tyco end;

fun read_tyco ctxt =
  #1 o dest_Type o Proof_Context.read_type_name {proper = true, strict = true} ctxt;

fun cert_class ctxt class =
  let
    val _ = Axclass.get_info (Proof_Context.theory_of ctxt) class;
  in class end;

val parse_classrel_ident = Parse.class --| \<^keyword>\<open><\<close> -- Parse.class;

fun cert_inst ctxt (class, tyco) =
  (cert_class ctxt class, cert_tyco ctxt tyco);

fun read_inst ctxt (raw_tyco, raw_class) =
  (read_tyco ctxt raw_tyco, Proof_Context.read_class ctxt raw_class);

val parse_inst_ident = Parse.name --| \<^keyword>\<open>::\<close> -- Parse.class;

fun cert_syms ctxt =
  Code_Symbol.map_attr (cert_const ctxt) (cert_tyco ctxt)
    (cert_class ctxt) (apply2 (cert_class ctxt)) (cert_inst ctxt) I;

fun read_syms ctxt =
  Code_Symbol.map_attr (read_const ctxt) (read_tyco ctxt)
    (Proof_Context.read_class ctxt) (apply2 (Proof_Context.read_class ctxt)) (read_inst ctxt) I;

fun cert_syms' ctxt =
  Code_Symbol.map_attr (apfst (cert_const ctxt)) (apfst (cert_tyco ctxt))
    (apfst (cert_class ctxt)) ((apfst o apply2) (cert_class ctxt)) (apfst (cert_inst ctxt)) I;

fun read_syms' ctxt =
  Code_Symbol.map_attr (apfst (read_const ctxt)) (apfst (read_tyco ctxt))
    (apfst (Proof_Context.read_class ctxt)) ((apfst o apply2) (Proof_Context.read_class ctxt)) (apfst (read_inst ctxt)) I;

fun check_name is_module s =
  let
    val _ = if s = "" then error "Bad empty code name" else ();
    val xs = Long_Name.explode s;
    val xs' = if is_module
        then map (Name.desymbolize NONE) xs
      else if length xs < 2
        then error ("Bad code name without module component: " ^ quote s)
      else
        let
          val (ys, y) = split_last xs;
          val ys' = map (Name.desymbolize NONE) ys;
          val y' = Name.desymbolize NONE y;
        in ys' @ [y'] end;
  in if xs' = xs
    then if is_module then (xs, "") else split_last xs
    else error ("Invalid code name: " ^ quote s ^ "\n"
      ^ "better try " ^ quote (Long_Name.implode xs'))
  end;


(** theory data **)

datatype pretty_modules = Singleton of string * Pretty.T | Hierarchy of (string list * Pretty.T) list;

type serializer = Token.T list
  -> Proof.context
  -> {
    reserved_syms: string list,
    identifiers: Code_Printer.identifiers,
    includes: (string * Pretty.T) list,
    class_syntax: string -> string option,
    tyco_syntax: string -> Code_Printer.tyco_syntax option,
    const_syntax: string -> Code_Printer.const_syntax option,
    module_name: string }
  -> Code_Thingol.program
  -> Code_Symbol.T list
  -> pretty_modules * (Code_Symbol.T -> string option);

type language = {serializer: serializer, literals: literals,
  check: {env_var: string, make_destination: Path.T -> Path.T, make_command: string -> string},
  evaluation_args: Token.T list};

type ancestry = (string * (Code_Thingol.program -> Code_Thingol.program)) list;

val merge_ancestry : ancestry * ancestry -> ancestry = AList.join (op =) (K snd);

type target = {serial: serial, language: language, ancestry: ancestry};

structure Targets = Theory_Data
(
  type T = (target * Code_Printer.data) Symtab.table * int;
  val empty = (Symtab.empty, 0);
  val extend = I;
  fun merge ((targets1, index1), (targets2, index2)) : T =
    let
      val targets' =
        Symtab.join (fn target_name => fn ((target1, data1), (target2, data2)) =>
          if #serial target1 = #serial target2 then
          ({serial = #serial target1, language = #language target1,
            ancestry = merge_ancestry (#ancestry target1, #ancestry target2)},
            Code_Printer.merge_data (data1, data2))
          else error ("Incompatible targets: " ^ quote target_name)) (targets1, targets2)
      val index' = Int.max (index1, index2);
    in (targets', index') end;
);

val exists_target = Symtab.defined o #1 o Targets.get;
val lookup_target_data = Symtab.lookup o #1 o Targets.get;
fun assert_target thy target_name =
  if exists_target thy target_name
  then target_name
  else error ("Unknown code target language: " ^ quote target_name);

fun reset_index thy =
  if #2 (Targets.get thy) = 0 then NONE
  else SOME ((Targets.map o apsnd) (K 0) thy);

val _ = Theory.setup (Theory.at_begin reset_index);

fun next_export thy =
  let
    val thy' = (Targets.map o apsnd) (fn i => i + 1) thy;
    val i = #2 (Targets.get thy');
  in ("export" ^ string_of_int i, thy') end;

fun fold1 f xs = fold f (tl xs) (hd xs);

fun join_ancestry thy target_name =
  let
    val _ = assert_target thy target_name;
    val the_target_data = the o lookup_target_data thy;
    val (target, this_data) = the_target_data target_name;
    val ancestry = #ancestry target;
    val modifies = rev (map snd ancestry);
    val modify = fold (curry (op o)) modifies I;
    val datas = rev (map (snd o the_target_data o fst) ancestry) @ [this_data];
    val data = fold1 (fn data' => fn data => Code_Printer.merge_data (data, data')) datas;
  in (modify, (target, data)) end;

fun allocate_target target_name target thy =
  let
    val _ = if exists_target thy target_name
      then error ("Attempt to overwrite existing target " ^ quote target_name)
      else ();
  in
    thy
    |> (Targets.map o apfst o Symtab.update) (target_name, (target, Code_Printer.empty_data))
  end;

fun add_language (target_name, language) =
  allocate_target target_name {serial = serial (), language = language,
    ancestry = []};

fun add_derived_target (target_name, initial_ancestry) thy =
  let
    val _ = if null initial_ancestry
      then error "Must derive from existing target(s)" else ();
    fun the_target_data target_name' = case lookup_target_data thy target_name' of
      NONE => error ("Unknown code target language: " ^ quote target_name')
    | SOME target_data' => target_data';
    val targets = rev (map (fst o the_target_data o fst) initial_ancestry);
    val supremum = fold1 (fn target' => fn target =>
      if #serial target = #serial target'
      then target else error "Incompatible targets") targets;
    val ancestries = map #ancestry targets @ [initial_ancestry];
    val ancestry = fold1 (fn ancestry' => fn ancestry =>
      merge_ancestry (ancestry, ancestry')) ancestries;
  in
    allocate_target target_name {serial = #serial supremum, language = #language supremum,
      ancestry = ancestry} thy
  end;

fun map_data target_name f thy =
  let
    val _ = assert_target thy target_name;
  in
    thy
    |> (Targets.map o apfst o Symtab.map_entry target_name o apsnd o Code_Printer.map_data) f
  end;

fun map_reserved target_name = map_data target_name o @{apply 3(1)};
fun map_identifiers target_name = map_data target_name o @{apply 3(2)};
fun map_printings target_name = map_data target_name o @{apply 3(3)};


(** serializers **)

val codeN = "code";
val generatedN = "Generated_Code";

val code_path = Path.append (Path.basic codeN);
fun code_export_message thy = writeln (Export.message thy (Path.basic codeN));

fun export binding content thy =
  let
    val thy' = thy |> Generated_Files.add_files (binding, content);
    val _ = Export.export thy' binding [XML.Text content];
  in thy' end;

local

fun export_logical (file_prefix, file_pos) format pretty_modules =
  let
    fun binding path = Path.binding (path, file_pos);
    val prefix = code_path file_prefix;
  in
    (case pretty_modules of
      Singleton (ext, p) => export (binding (Path.ext ext prefix)) (format p)
    | Hierarchy modules =>
        fold (fn (names, p) =>
          export (binding (prefix + Path.make names)) (format p)) modules)
    #> tap code_export_message
  end;

fun export_physical root format pretty_modules =
  (case pretty_modules of
    Singleton (_, p) => File.write root (format p)
  | Hierarchy code_modules =>
      (Isabelle_System.make_directory root;
        List.app (fn (names, p) =>
          File.write (Path.appends (root :: map Path.basic names)) (format p)) code_modules));

in

fun export_result some_file format (pretty_code, _) thy =
  (case some_file of
    NONE =>
      let val (file_prefix, thy') = next_export thy;
      in export_logical (Path.basic file_prefix, Position.none) format pretty_code thy' end
  | SOME ({physical = false}, file_prefix) =>
      export_logical file_prefix format pretty_code thy
  | SOME ({physical = true}, (file, _)) =>
      let
        val root = File.full_path (Resources.master_directory thy) file;
        val _ = File.check_dir (Path.dir root);
        val _ = export_physical root format pretty_code;
      in thy end);

fun produce_result syms width pretty_modules =
  let val format = Code_Printer.format [] width in
    (case pretty_modules of
      (Singleton (_, p), deresolve) => ([([], format p)], map deresolve syms)
    | (Hierarchy code_modules, deresolve) =>
        ((map o apsnd) format code_modules, map deresolve syms))
  end;

fun present_result selects width (pretty_modules, _) =
  let val format = Code_Printer.format selects width in
    (case pretty_modules of
      Singleton (_, p) => format p
    | Hierarchy code_modules => space_implode "\n\n" (map (format o #2) code_modules))
  end;

end;


(** serializer usage **)

(* technical aside: pretty printing width *)

val default_code_width = Attrib.setup_config_int \<^binding>\<open>default_code_width\<close> (K 80);

fun default_width ctxt = Config.get ctxt default_code_width;

val the_width = the_default o default_width;


(* montage *)

fun the_language ctxt =
  #language o fst o the o lookup_target_data (Proof_Context.theory_of ctxt);

fun the_literals ctxt = #literals o the_language ctxt;

fun the_evaluation_args ctxt = #evaluation_args o the_language ctxt;

local

fun activate_target ctxt target_name =
  let
    val thy = Proof_Context.theory_of ctxt;
    val (modify, (target, data)) = join_ancestry thy target_name;
    val serializer = (#serializer o #language) target;
  in { serializer = serializer, data = data, modify = modify } end;

fun project_program_for_syms ctxt syms_hidden syms1 program1 =
  let
    val syms2 = subtract (op =) syms_hidden syms1;
    val program2 = Code_Symbol.Graph.restrict (not o member (op =) syms_hidden) program1;
    val unimplemented = Code_Thingol.unimplemented program2;
    val _ =
      if null unimplemented then ()
      else error ("No code equations for " ^
        commas (map (Proof_Context.markup_const ctxt) unimplemented));
    val syms3 = Code_Symbol.Graph.all_succs program2 syms2;
    val program3 = Code_Symbol.Graph.restrict (member (op =) syms3) program2;
  in program3 end;

fun project_includes_for_syms syms includes =
   let
     fun select_include (name, (content, cs)) =
       if null cs orelse exists (member (op =) syms) cs
       then SOME (name, content) else NONE;
  in map_filter select_include includes end;

fun prepare_serializer ctxt target_name module_name args proto_program syms =
  let
    val { serializer, data, modify } = activate_target ctxt target_name;
    val printings = Code_Printer.the_printings data;
    val _ = if module_name = "" then () else (check_name true module_name; ())
    val hidden_syms = Code_Symbol.symbols_of printings;
    val prepared_program = project_program_for_syms ctxt hidden_syms syms proto_program;
    val prepared_syms = subtract (op =) hidden_syms syms;
    val all_syms = Code_Symbol.Graph.all_succs proto_program syms;
    val includes = project_includes_for_syms all_syms
      (Code_Symbol.dest_module_data printings);
    val prepared_serializer = serializer args ctxt {
      reserved_syms = Code_Printer.the_reserved data,
      identifiers = Code_Printer.the_identifiers data,
      includes = includes,
      const_syntax = Code_Symbol.lookup_constant_data printings,
      tyco_syntax = Code_Symbol.lookup_type_constructor_data printings,
      class_syntax = Code_Symbol.lookup_type_class_data printings,
      module_name = module_name };
  in
    (prepared_serializer o modify, (prepared_program, prepared_syms))
  end;

fun invoke_serializer ctxt target_name module_name args program all_public syms =
  let
    val (prepared_serializer, (prepared_program, prepared_syms)) =
      prepare_serializer ctxt target_name module_name args program syms;
    val exports = if all_public then [] else prepared_syms;
  in
    Code_Preproc.timed_exec "serializing"
      (fn () => prepared_serializer prepared_program exports) ctxt
  end;

fun assert_module_name "" = error "Empty module name not allowed here"
  | assert_module_name module_name = module_name;

in

fun export_code_for some_file target_name module_name some_width args program all_public cs lthy =
  let
    val format = Code_Printer.format [] (the_width lthy some_width);
    val res = invoke_serializer lthy target_name module_name args program all_public cs;
  in Local_Theory.background_theory (export_result some_file format res) lthy end;

fun produce_code_for ctxt target_name module_name some_width args =
  let
    val serializer = invoke_serializer ctxt target_name (assert_module_name module_name) args;
  in fn program => fn all_public => fn syms =>
    produce_result syms (the_width ctxt some_width)
      (serializer program all_public syms)
  end;

fun present_code_for ctxt target_name module_name some_width args =
  let
    val serializer = invoke_serializer ctxt target_name (assert_module_name module_name) args;
  in fn program => fn (syms, selects) =>
    present_result selects (the_width ctxt some_width) (serializer program false syms)
  end;

fun check_code_for target_name strict args program all_public syms lthy =
  let
    val { env_var, make_destination, make_command } = #check (the_language lthy target_name);
    val format = Code_Printer.format [] 80;
    fun ext_check p =
      let
        val destination = make_destination p;
        val lthy' = lthy
          |> Local_Theory.background_theory
            (export_result (SOME ({physical = true}, (destination, Position.none))) format
              (invoke_serializer lthy target_name generatedN args program all_public syms));
        val cmd = make_command generatedN;
        val context_cmd = "cd " ^ File.bash_path p ^ " && " ^ cmd ^ " 2>&1";
      in
        if Isabelle_System.bash context_cmd <> 0
        then error ("Code check failed for " ^ target_name ^ ": " ^ cmd)
        else lthy'
      end;
  in
    if not (env_var = "") andalso getenv env_var = "" then
      if strict
      then error (env_var ^ " not set; cannot check code for " ^ target_name)
      else (warning (env_var ^ " not set; skipped checking code for " ^ target_name); lthy)
    else Isabelle_System.with_tmp_dir "Code_Test" ext_check
  end;

fun dynamic_compilation_text prepared_serializer width prepared_program syms all_public ((vs, ty), t) =
  let
    val _ = if Code_Thingol.contains_dict_var t then
      error "Term to be evaluated contains free dictionaries" else ();
    val v' = singleton (Name.variant_list (map fst vs)) "a";
    val vs' = (v', []) :: vs;
    val ty' = ITyVar v' `-> ty;
    val program = prepared_program
      |> Code_Symbol.Graph.new_node (Code_Symbol.value,
          Code_Thingol.Fun (((vs', ty'), [(([IVar (SOME "dummy")], t), (NONE, true))]), NONE))
      |> fold (curry (perhaps o try o
          Code_Symbol.Graph.add_edge) Code_Symbol.value) syms;
    val (pretty_code, deresolve) =
      prepared_serializer program (if all_public then [] else [Code_Symbol.value]);
    val (compilation_code, [SOME value_name]) =
      produce_result [Code_Symbol.value] width (pretty_code, deresolve);
  in ((compilation_code, value_name), deresolve) end;

fun compilation_text' ctxt target_name some_module_name program syms =
  let
    val width = default_width ctxt;
    val evaluation_args = the_evaluation_args ctxt target_name;
    val (prepared_serializer, (prepared_program, _)) =
      prepare_serializer ctxt target_name (the_default generatedN some_module_name) evaluation_args program syms;
  in
    Code_Preproc.timed_exec "serializing"
      (fn () => dynamic_compilation_text prepared_serializer width prepared_program syms) ctxt
  end;

fun compilation_text ctxt target_name program syms =
  fst oo compilation_text' ctxt target_name NONE program syms

end; (* local *)


(* code generation *)

fun prep_destination (location, (s, pos)) =
  if location = {physical = false}
  then (location, Path.explode_pos (s, pos))
  else
    let
      val _ =
        if s = ""
        then error ("Bad bad empty " ^ Markup.markup Markup.keyword2 "file" ^ " argument")
        else ();
      val _ =
        legacy_feature
          (Markup.markup Markup.keyword1 "export_code" ^ " with " ^
            Markup.markup Markup.keyword2 "file" ^ " argument" ^ Position.here pos);
      val _ = Position.report pos Markup.language_path;
      val path = #1 (Path.explode_pos (s, pos));
      val _ = Position.report pos (Markup.path (Path.implode_symbolic path));
    in (location, (path, pos)) end;

fun export_code all_public cs seris lthy =
  let
    val program = Code_Thingol.consts_program lthy cs;
  in
    (seris, lthy) |-> fold (fn (((target_name, module_name), some_file), args) =>
      export_code_for some_file target_name module_name NONE args
        program all_public (map Constant cs))
  end;

fun export_code_cmd all_public raw_cs seris lthy =
  let
    val cs = Code_Thingol.read_const_exprs lthy raw_cs;
  in export_code all_public cs ((map o apfst o apsnd o Option.map) prep_destination seris) lthy end;

fun produce_code ctxt all_public cs target_name some_width some_module_name args =
  let
    val program = Code_Thingol.consts_program ctxt cs;
  in produce_code_for ctxt target_name some_width some_module_name args program all_public (map Constant cs) end;

fun present_code ctxt cs syms target_name some_width some_module_name args =
  let
    val program = Code_Thingol.consts_program ctxt cs;
  in present_code_for ctxt target_name some_width some_module_name args program (map Constant cs, syms) end;

fun check_code all_public cs seris lthy =
  let
    val program = Code_Thingol.consts_program lthy cs;
  in
    (seris, lthy) |-> fold (fn ((target_name, strict), args) =>
      check_code_for target_name strict args program all_public (map Constant cs))
  end;

fun check_code_cmd all_public raw_cs seris lthy =
  check_code all_public (Code_Thingol.read_const_exprs lthy raw_cs) seris lthy;


(** serializer configuration **)

(* reserved symbol names *)

fun add_reserved target_name sym thy =
  let
    val (_, (_, data)) = join_ancestry thy target_name;
    val _ = if member (op =) (Code_Printer.the_reserved data) sym
      then error ("Reserved symbol " ^ quote sym ^ " already declared")
      else ();
  in
    thy
    |> map_reserved target_name (insert (op =) sym)
  end;


(* checking of syntax *)

fun check_const_syntax ctxt target_name c syn =
  if Code_Printer.requires_args syn > Code.args_number (Proof_Context.theory_of ctxt) c
  then error ("Too many arguments in syntax for constant " ^ quote c)
  else Code_Printer.prep_const_syntax (Proof_Context.theory_of ctxt) (the_literals ctxt target_name) c syn;

fun check_tyco_syntax ctxt target_name tyco syn =
  if fst syn <> Sign.arity_number (Proof_Context.theory_of ctxt) tyco
  then error ("Number of arguments mismatch in syntax for type constructor " ^ quote tyco)
  else syn;


(* custom symbol names *)

fun arrange_name_decls x =
  let
    fun arrange is_module (sym, target_names) = map (fn (target, some_name) =>
      (target, (sym, Option.map (check_name is_module) some_name))) target_names;
  in
    Code_Symbol.maps_attr' (arrange false) (arrange false) (arrange false)
      (arrange false) (arrange false) (arrange true) x
  end;

fun cert_name_decls ctxt = cert_syms' ctxt #> arrange_name_decls;

fun read_name_decls ctxt = read_syms' ctxt #> arrange_name_decls;

fun set_identifier (target_name, sym_name) = map_identifiers target_name (Code_Symbol.set_data sym_name);

fun gen_set_identifiers prep_name_decl raw_name_decls thy =
  fold set_identifier (prep_name_decl (Proof_Context.init_global thy) raw_name_decls) thy;

val set_identifiers = gen_set_identifiers cert_name_decls;
val set_identifiers_cmd = gen_set_identifiers read_name_decls;


(* custom printings *)

fun arrange_printings prep_syms ctxt =
  let
    fun arrange check (sym, target_syns) =
      map (fn (target_name, some_syn) =>
        (target_name, (sym, Option.map (check ctxt target_name sym) some_syn))) target_syns;
  in
    Code_Symbol.maps_attr'
      (arrange check_const_syntax) (arrange check_tyco_syntax)
        (arrange ((K o K o K) I)) (arrange ((K o K o K) I)) (arrange ((K o K o K) I))
        (arrange (fn ctxt => fn _ => fn _ => fn (raw_content, raw_syms) =>
          (Pretty.blk (0, Pretty.fbreaks (map Code_Printer.str (split_lines raw_content))),
            map (prep_syms ctxt) raw_syms)))
  end;

fun cert_printings ctxt = cert_syms' ctxt #> arrange_printings cert_syms ctxt;

fun read_printings ctxt = read_syms' ctxt #> arrange_printings read_syms ctxt;

fun set_printing (target_name, sym_syn) = map_printings target_name (Code_Symbol.set_data sym_syn);

fun gen_set_printings prep_print_decl raw_print_decls thy =
  fold set_printing (prep_print_decl (Proof_Context.init_global thy) raw_print_decls) thy;

val set_printings = gen_set_printings cert_printings;
val set_printings_cmd = gen_set_printings read_printings;


(* concrete syntax *)

fun parse_args f args =
  case Scan.read Token.stopper f args
   of SOME x => x
    | NONE => error "Bad serializer arguments";


(** Isar setup **)

val (constantK, type_constructorK, type_classK, class_relationK, class_instanceK, code_moduleK) =
  (\<^keyword>\<open>constant\<close>, \<^keyword>\<open>type_constructor\<close>, \<^keyword>\<open>type_class\<close>,
    \<^keyword>\<open>class_relation\<close>, \<^keyword>\<open>class_instance\<close>, \<^keyword>\<open>code_module\<close>);

local

val parse_constants = constantK |-- Scan.repeat1 Parse.term >> map Constant;

val parse_type_constructors = type_constructorK |-- Scan.repeat1 Parse.type_const >> map Type_Constructor;

val parse_classes = type_classK |-- Scan.repeat1 Parse.class >> map Type_Class;

val parse_class_relations = class_relationK |-- Scan.repeat1 parse_classrel_ident >> map Class_Relation;

val parse_instances = class_instanceK |-- Scan.repeat1 parse_inst_ident >> map Class_Instance;

val parse_simple_symbols = Scan.repeats1 (parse_constants || parse_type_constructors || parse_classes
  || parse_class_relations || parse_instances);

fun parse_single_symbol_pragma parse_keyword parse_isa parse_target =
  parse_keyword |-- Parse.!!! (parse_isa --| (\<^keyword>\<open>\<rightharpoonup>\<close> || \<^keyword>\<open>=>\<close>)
    -- Parse.and_list1 (\<^keyword>\<open>(\<close> |-- (Parse.name --| \<^keyword>\<open>)\<close> -- Scan.option parse_target)));

fun parse_symbol_pragma parse_const parse_tyco parse_class parse_classrel parse_inst parse_module =
  parse_single_symbol_pragma constantK Parse.term parse_const
    >> Constant
  || parse_single_symbol_pragma type_constructorK Parse.type_const parse_tyco
    >> Type_Constructor
  || parse_single_symbol_pragma type_classK Parse.class parse_class
    >> Type_Class
  || parse_single_symbol_pragma class_relationK parse_classrel_ident parse_classrel
    >> Class_Relation
  || parse_single_symbol_pragma class_instanceK parse_inst_ident parse_inst
    >> Class_Instance
  || parse_single_symbol_pragma code_moduleK Parse.name parse_module
    >> Module;

fun parse_symbol_pragmas parse_const parse_tyco parse_class parse_classrel parse_inst parse_module =
  Parse.enum1 "|" (Parse.group (fn () => "code symbol pragma")
    (parse_symbol_pragma parse_const parse_tyco parse_class parse_classrel parse_inst parse_module));

val code_expr_argsP = Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.args --| \<^keyword>\<open>)\<close>) [];

fun code_expr_inP (all_public, raw_cs) =
  Scan.repeat (\<^keyword>\<open>in\<close> |-- Parse.!!! (Parse.name
    -- Scan.optional (\<^keyword>\<open>module_name\<close> |-- Parse.name) ""
    -- Scan.option
        ((\<^keyword>\<open>file_prefix\<close> >> K {physical = false} || \<^keyword>\<open>file\<close> >> K {physical = true})
          -- Parse.!!! (Parse.position Parse.path))
    -- code_expr_argsP))
      >> (fn seri_args => export_code_cmd all_public raw_cs seri_args);

fun code_expr_checkingP (all_public, raw_cs) =
  (\<^keyword>\<open>checking\<close> |-- Parse.!!!
    (Scan.repeat (Parse.name -- (Scan.optional (\<^keyword>\<open>?\<close> >> K false) true) -- code_expr_argsP)))
      >> (fn seri_args => check_code_cmd all_public raw_cs seri_args);

in

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>code_reserved\<close>
    "declare words as reserved for target language"
    (Parse.name -- Scan.repeat1 Parse.name
      >> (fn (target, reserveds) => (Toplevel.theory o fold (add_reserved target)) reserveds));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>code_identifier\<close> "declare mandatory names for code symbols"
    (parse_symbol_pragmas Parse.name Parse.name Parse.name Parse.name Parse.name Parse.name
      >> (Toplevel.theory o fold set_identifiers_cmd));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>code_printing\<close> "declare dedicated printing for code symbols"
    (parse_symbol_pragmas (Code_Printer.parse_const_syntax) (Code_Printer.parse_tyco_syntax)
      Parse.string (Parse.minus >> K ()) (Parse.minus >> K ())
      (Parse.text -- Scan.optional (\<^keyword>\<open>for\<close> |-- parse_simple_symbols) [])
      >> (Toplevel.theory o fold set_printings_cmd));

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>export_code\<close> "generate executable code for constants"
    (Scan.optional (\<^keyword>\<open>open\<close> >> K true) false -- Scan.repeat1 Parse.term
      :|-- (fn args => (code_expr_checkingP args || code_expr_inP args)));

end;

local

val parse_const_terms = Args.theory -- Scan.repeat1 Args.term
  >> uncurry (fn thy => map (Code.check_const thy));

fun parse_symbols keyword parse internalize mark_symbol =
  Scan.lift (keyword --| Args.colon) |-- Args.theory -- Scan.repeat1 parse
  >> uncurry (fn thy => map (mark_symbol o internalize thy));

val parse_consts = parse_symbols constantK Args.term
  Code.check_const Constant;

val parse_types = parse_symbols type_constructorK (Scan.lift Args.name)
  Sign.intern_type Type_Constructor;

val parse_classes = parse_symbols type_classK (Scan.lift Args.name)
  Sign.intern_class Type_Class;

val parse_instances = parse_symbols class_instanceK (Scan.lift (Args.name --| Args.$$$ "::" -- Args.name))
  (fn thy => fn (raw_tyco, raw_class) =>
    (Sign.intern_class thy raw_tyco, Sign.intern_type thy raw_class)) Class_Instance;

in

val _ = Theory.setup
  (Thy_Output.antiquotation_raw \<^binding>\<open>code_stmts\<close>
    (parse_const_terms --
      Scan.repeats (parse_consts || parse_types || parse_classes || parse_instances)
      -- Scan.lift (Args.parens (Args.name -- Scan.option Parse.int)))
    (fn ctxt => fn ((consts, symbols), (target_name, some_width)) =>
       present_code ctxt consts symbols
         target_name "Example" some_width []
       |> trim_line
       |> Thy_Output.verbatim (Config.put Document_Antiquotation.thy_output_display true ctxt)));

end;

end; (*struct*)
