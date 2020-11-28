(*  Title:      Pure/PIDE/markup.ML
    Author:     Makarius

Quasi-abstract markup elements.
*)

signature MARKUP =
sig
  type T = string * Properties.T
  val empty: T
  val is_empty: T -> bool
  val properties: Properties.T -> T -> T
  val nameN: string val name: string -> T -> T
  val xnameN: string val xname: string -> T -> T
  val kindN: string
  val serialN: string
  val serial_properties: int -> Properties.T
  val instanceN: string
  val meta_titleN: string val meta_title: T
  val meta_creatorN: string val meta_creator: T
  val meta_contributorN: string val meta_contributor: T
  val meta_dateN: string val meta_date: T
  val meta_licenseN: string val meta_license: T
  val meta_descriptionN: string val meta_description: T
  val languageN: string
  val symbolsN: string
  val delimitedN: string
  val is_delimited: Properties.T -> bool
  val language: {name: string, symbols: bool, antiquotes: bool, delimited: bool} -> T
  val language': {name: string, symbols: bool, antiquotes: bool} -> bool -> T
  val language_Isar: bool -> T
  val language_method: T
  val language_attribute: T
  val language_sort: bool -> T
  val language_type: bool -> T
  val language_term: bool -> T
  val language_prop: bool -> T
  val language_ML: bool -> T
  val language_SML: bool -> T
  val language_document: bool -> T
  val language_document_marker: T
  val language_antiquotation: T
  val language_text: bool -> T
  val language_verbatim: bool -> T
  val language_latex: bool -> T
  val language_rail: T
  val language_path: T
  val language_mixfix: T
  val bindingN: string val binding: T
  val entityN: string val entity: string -> string -> T
  val defN: string
  val refN: string
  val completionN: string val completion: T
  val no_completionN: string val no_completion: T
  val updateN: string val update: T
  val lineN: string
  val end_lineN: string
  val offsetN: string
  val end_offsetN: string
  val fileN: string
  val idN: string
  val position_properties: string list
  val position_property: Properties.entry -> bool
  val positionN: string val position: T
  val expressionN: string val expression: string -> T
  val citationN: string val citation: string -> T
  val pathN: string val path: string -> T
  val export_pathN: string val export_path: string -> T
  val urlN: string val url: string -> T
  val docN: string val doc: string -> T
  val toolN: string val tool: string -> T
  val markupN: string
  val consistentN: string
  val unbreakableN: string
  val block_properties: string list
  val indentN: string
  val widthN: string
  val blockN: string val block: bool -> int -> T
  val breakN: string val break: int -> int -> T
  val fbreakN: string val fbreak: T
  val itemN: string val item: T
  val wordsN: string val words: T
  val hiddenN: string val hidden: T
  val deleteN: string val delete: T
  val bash_functionN: string
  val scala_functionN: string
  val system_optionN: string
  val sessionN: string
  val theoryN: string
  val classN: string
  val type_nameN: string
  val constantN: string
  val fixedN: string val fixed: string -> T
  val caseN: string val case_: string -> T
  val dynamic_factN: string val dynamic_fact: string -> T
  val literal_factN: string val literal_fact: string -> T
  val method_modifierN: string
  val tfreeN: string val tfree: T
  val tvarN: string val tvar: T
  val freeN: string val free: T
  val skolemN: string val skolem: T
  val boundN: string val bound: T
  val varN: string val var: T
  val numeralN: string val numeral: T
  val literalN: string val literal: T
  val delimiterN: string val delimiter: T
  val inner_stringN: string val inner_string: T
  val inner_cartoucheN: string val inner_cartouche: T
  val token_rangeN: string val token_range: T
  val sortingN: string val sorting: T
  val typingN: string val typing: T
  val class_parameterN: string val class_parameter: T
  val ML_keyword1N: string val ML_keyword1: T
  val ML_keyword2N: string val ML_keyword2: T
  val ML_keyword3N: string val ML_keyword3: T
  val ML_delimiterN: string val ML_delimiter: T
  val ML_tvarN: string val ML_tvar: T
  val ML_numeralN: string val ML_numeral: T
  val ML_charN: string val ML_char: T
  val ML_stringN: string val ML_string: T
  val ML_commentN: string val ML_comment: T
  val ML_defN: string
  val ML_openN: string
  val ML_structureN: string
  val ML_typingN: string val ML_typing: T
  val ML_breakpointN: string val ML_breakpoint: int -> T
  val antiquotedN: string val antiquoted: T
  val antiquoteN: string val antiquote: T
  val file_typeN: string
  val antiquotationN: string
  val ML_antiquotationN: string
  val document_antiquotationN: string
  val document_antiquotation_optionN: string
  val raw_textN: string val raw_text: T
  val plain_textN: string val plain_text: T
  val paragraphN: string val paragraph: T
  val text_foldN: string val text_fold: T
  val document_markerN: string val document_marker: T
  val document_tagN: string val document_tag: string -> T
  val markdown_paragraphN: string val markdown_paragraph: T
  val markdown_itemN: string val markdown_item: T
  val markdown_bulletN: string val markdown_bullet: int -> T
  val markdown_listN: string val markdown_list: string -> T
  val itemizeN: string
  val enumerateN: string
  val descriptionN: string
  val inputN: string val input: bool -> Properties.T -> T
  val command_keywordN: string val command_keyword: T
  val commandN: string val command_properties: T -> T
  val keywordN: string val keyword_properties: T -> T
  val stringN: string val string: T
  val alt_stringN: string val alt_string: T
  val verbatimN: string val verbatim: T
  val cartoucheN: string val cartouche: T
  val commentN: string val comment: T
  val keyword1N: string val keyword1: T
  val keyword2N: string val keyword2: T
  val keyword3N: string val keyword3: T
  val quasi_keywordN: string val quasi_keyword: T
  val improperN: string val improper: T
  val operatorN: string val operator: T
  val comment1N: string val comment1: T
  val comment2N: string val comment2: T
  val comment3N: string val comment3: T
  val elapsedN: string
  val cpuN: string
  val gcN: string
  val timing_properties: {elapsed: Time.time, cpu: Time.time, gc: Time.time} -> Properties.T
  val parse_command_timing_properties:
    Properties.T -> ({file: string, offset: int, name: string} * Time.time) option
  val timingN: string val timing: {elapsed: Time.time, cpu: Time.time, gc: Time.time} -> T
  val command_indentN: string val command_indent: int -> T
  val goalN: string val goal: T
  val subgoalN: string val subgoal: string -> T
  val taskN: string
  val forkedN: string val forked: T
  val joinedN: string val joined: T
  val runningN: string val running: T
  val finishedN: string val finished: T
  val failedN: string val failed: T
  val canceledN: string val canceled: T
  val initializedN: string val initialized: T
  val finalizedN: string val finalized: T
  val consolidatingN: string val consolidating: T
  val consolidatedN: string val consolidated: T
  val exec_idN: string
  val initN: string
  val statusN: string val status: T
  val resultN: string val result: T
  val writelnN: string val writeln: T
  val stateN: string val state: T
  val informationN: string val information: T
  val tracingN: string val tracing: T
  val warningN: string val warning: T
  val legacyN: string val legacy: T
  val errorN: string val error: T
  val systemN: string val system: T
  val protocolN: string
  val reportN: string val report: T
  val no_reportN: string val no_report: T
  val badN: string val bad: unit -> T
  val intensifyN: string val intensify: T
  val browserN: string
  val graphviewN: string
  val theory_exportsN: string
  val sendbackN: string
  val paddingN: string
  val padding_line: Properties.entry
  val padding_command: Properties.entry
  val dialogN: string val dialog: serial -> string -> T
  val jedit_actionN: string
  val functionN: string
  val ML_statistics: {pid: int, stats_dir: string} -> Properties.T
  val commands_accepted: Properties.T
  val assign_update: Properties.T
  val removed_versions: Properties.T
  val invoke_scala: string -> string -> bool -> Properties.T
  val cancel_scala: string -> Properties.T
  val task_statistics: Properties.entry
  val command_timing: Properties.entry
  val theory_timing: Properties.entry
  val session_timing: Properties.entry
  val loading_theory: string -> Properties.T
  val finished_theory: string -> Properties.T
  val build_session_finished: Properties.T
  val print_operationsN: string
  val print_operations: Properties.T
  val exportN: string
  type export_args =
   {id: string option,
    serial: serial,
    theory_name: string,
    name: string,
    executable: bool,
    compress: bool,
    strict: bool}
  val export: export_args -> Properties.T
  val debugger_state: string -> Properties.T
  val debugger_output: string -> Properties.T
  val simp_trace_panelN: string
  val simp_trace_logN: string
  val simp_trace_stepN: string
  val simp_trace_recurseN: string
  val simp_trace_hintN: string
  val simp_trace_ignoreN: string
  val simp_trace_cancel: serial -> Properties.T
  type output = Output.output * Output.output
  val no_output: output
  val add_mode: string -> (T -> output) -> unit
  val output: T -> output
  val enclose: T -> Output.output -> Output.output
  val markup: T -> string -> string
  val markups: T list -> string -> string
  val markup_only: T -> string
  val markup_report: string -> string
end;

structure Markup: MARKUP =
struct

(** markup elements **)

(* basic markup *)

type T = string * Properties.T;

val empty = ("", []);

fun is_empty ("", _) = true
  | is_empty _ = false;


fun properties more_props ((elem, props): T) =
  (elem, fold_rev Properties.put more_props props);

fun markup_elem name = (name, (name, []): T);
fun markup_string name prop = (name, fn s => (name, [(prop, s)]): T);
fun markup_int name prop = (name, fn i => (name, [(prop, Value.print_int i)]): T);


(* misc properties *)

val nameN = "name";
fun name a = properties [(nameN, a)];

val xnameN = "xname";
fun xname a = properties [(xnameN, a)];

val kindN = "kind";

val serialN = "serial";
fun serial_properties i = [(serialN, Value.print_int i)];

val instanceN = "instance";


(* meta data -- see https://www.dublincore.org/specifications/dublin-core/dcmi-terms *)

val (meta_titleN, meta_title) = markup_elem "meta_title";
val (meta_creatorN, meta_creator) = markup_elem "meta_creator";
val (meta_contributorN, meta_contributor) = markup_elem "meta_contributor";
val (meta_dateN, meta_date) = markup_elem "meta_date";
val (meta_licenseN, meta_license) = markup_elem "meta_license";
val (meta_descriptionN, meta_description) = markup_elem "meta_description";


(* embedded languages *)

val languageN = "language";
val symbolsN = "symbols";
val antiquotesN = "antiquotes";
val delimitedN = "delimited"

fun is_delimited props =
  Properties.get props delimitedN = SOME "true";

fun language {name, symbols, antiquotes, delimited} =
  (languageN,
   [(nameN, name),
    (symbolsN, Value.print_bool symbols),
    (antiquotesN, Value.print_bool antiquotes),
    (delimitedN, Value.print_bool delimited)]);

fun language' {name, symbols, antiquotes} delimited =
  language {name = name, symbols = symbols, antiquotes = antiquotes, delimited = delimited};

val language_Isar = language' {name = "Isar", symbols = true, antiquotes = false};
val language_method =
  language {name = "method", symbols = true, antiquotes = false, delimited = false};
val language_attribute =
  language {name = "attribute", symbols = true, antiquotes = false, delimited = false};
val language_sort = language' {name = "sort", symbols = true, antiquotes = false};
val language_type = language' {name = "type", symbols = true, antiquotes = false};
val language_term = language' {name = "term", symbols = true, antiquotes = false};
val language_prop = language' {name = "prop", symbols = true, antiquotes = false};
val language_ML = language' {name = "ML", symbols = false, antiquotes = true};
val language_SML = language' {name = "SML", symbols = false, antiquotes = false};
val language_document = language' {name = "document", symbols = false, antiquotes = true};
val language_document_marker =
  language {name = "document_marker", symbols = true, antiquotes = true, delimited = true};
val language_antiquotation =
  language {name = "antiquotation", symbols = true, antiquotes = false, delimited = true};
val language_text = language' {name = "text", symbols = true, antiquotes = false};
val language_verbatim = language' {name = "verbatim_text", symbols = true, antiquotes = false};
val language_latex = language' {name = "latex", symbols = false, antiquotes = false};
val language_rail = language {name = "rail", symbols = true, antiquotes = true, delimited = true};
val language_path = language {name = "path", symbols = false, antiquotes = false, delimited = true};
val language_mixfix =
  language {name = "mixfix_annotation", symbols = true, antiquotes = false, delimited = true};


(* formal entities *)

val (bindingN, binding) = markup_elem "binding";

val entityN = "entity";
fun entity kind name =
  (entityN,
    (if name = "" then [] else [(nameN, name)]) @ (if kind = "" then [] else [(kindN, kind)]));

val defN = "def";
val refN = "ref";


(* completion *)

val (completionN, completion) = markup_elem "completion";
val (no_completionN, no_completion) = markup_elem "no_completion";

val (updateN, update) = markup_elem "update";


(* position *)

val lineN = "line";
val end_lineN = "end_line";

val offsetN = "offset";
val end_offsetN = "end_offset";

val fileN = "file";
val idN = "id";

val position_properties = [lineN, offsetN, end_offsetN, fileN, idN];
fun position_property (entry: Properties.entry) = member (op =) position_properties (#1 entry);

val (positionN, position) = markup_elem "position";


(* expression *)

val expressionN = "expression";
fun expression kind = (expressionN, if kind = "" then [] else [(kindN, kind)]);


(* citation *)

val (citationN, citation) = markup_string "citation" nameN;


(* external resources *)

val (pathN, path) = markup_string "path" nameN;
val (export_pathN, export_path) = markup_string "export_path" nameN;
val (urlN, url) = markup_string "url" nameN;
val (docN, doc) = markup_string "doc" nameN;
val (toolN, tool) = markup_string "tool" nameN;


(* pretty printing *)

val markupN = "markup";
val consistentN = "consistent";
val unbreakableN = "unbreakable";
val indentN = "indent";

val block_properties = [markupN, consistentN, unbreakableN, indentN];

val widthN = "width";

val blockN = "block";
fun block c i =
  (blockN,
    (if c then [(consistentN, Value.print_bool c)] else []) @
    (if i <> 0 then [(indentN, Value.print_int i)] else []));

val breakN = "break";
fun break w i =
  (breakN,
    (if w <> 0 then [(widthN, Value.print_int w)] else []) @
    (if i <> 0 then [(indentN, Value.print_int i)] else []));

val (fbreakN, fbreak) = markup_elem "fbreak";

val (itemN, item) = markup_elem "item";


(* text properties *)

val (wordsN, words) = markup_elem "words";

val (hiddenN, hidden) = markup_elem "hidden";

val (deleteN, delete) = markup_elem "delete";


(* misc entities *)

val bash_functionN = "bash_function";
val scala_functionN = "scala_function";
val system_optionN = "system_option";

val sessionN = "session";

val theoryN = "theory";
val classN = "class";
val type_nameN = "type_name";
val constantN = "constant";

val (fixedN, fixed) = markup_string "fixed" nameN;
val (caseN, case_) = markup_string "case" nameN;
val (dynamic_factN, dynamic_fact) = markup_string "dynamic_fact" nameN;
val (literal_factN, literal_fact) = markup_string "literal_fact" nameN;

val method_modifierN = "method_modifier";


(* inner syntax *)

val (tfreeN, tfree) = markup_elem "tfree";
val (tvarN, tvar) = markup_elem "tvar";
val (freeN, free) = markup_elem "free";
val (skolemN, skolem) = markup_elem "skolem";
val (boundN, bound) = markup_elem "bound";
val (varN, var) = markup_elem "var";
val (numeralN, numeral) = markup_elem "numeral";
val (literalN, literal) = markup_elem "literal";
val (delimiterN, delimiter) = markup_elem "delimiter";
val (inner_stringN, inner_string) = markup_elem "inner_string";
val (inner_cartoucheN, inner_cartouche) = markup_elem "inner_cartouche";

val (token_rangeN, token_range) = markup_elem "token_range";

val (sortingN, sorting) = markup_elem "sorting";
val (typingN, typing) = markup_elem "typing";
val (class_parameterN, class_parameter) = markup_elem "class_parameter";


(* ML *)

val (ML_keyword1N, ML_keyword1) = markup_elem "ML_keyword1";
val (ML_keyword2N, ML_keyword2) = markup_elem "ML_keyword2";
val (ML_keyword3N, ML_keyword3) = markup_elem "ML_keyword3";
val (ML_delimiterN, ML_delimiter) = markup_elem "ML_delimiter";
val (ML_tvarN, ML_tvar) = markup_elem "ML_tvar";
val (ML_numeralN, ML_numeral) = markup_elem "ML_numeral";
val (ML_charN, ML_char) = markup_elem "ML_char";
val (ML_stringN, ML_string) = markup_elem "ML_string";
val (ML_commentN, ML_comment) = markup_elem "ML_comment";

val ML_defN = "ML_def";
val ML_openN = "ML_open";
val ML_structureN = "ML_structure";
val (ML_typingN, ML_typing) = markup_elem "ML_typing";

val (ML_breakpointN, ML_breakpoint) = markup_int "ML_breakpoint" serialN;


(* antiquotations *)

val (antiquotedN, antiquoted) = markup_elem "antiquoted";
val (antiquoteN, antiquote) = markup_elem "antiquote";

val file_typeN = "file_type";
val antiquotationN = "antiquotation";
val ML_antiquotationN = "ML_antiquotation";
val document_antiquotationN = "document_antiquotation";
val document_antiquotation_optionN = "document_antiquotation_option";


(* document text *)

val (raw_textN, raw_text) = markup_elem "raw_text";
val (plain_textN, plain_text) = markup_elem "plain_text";

val (paragraphN, paragraph) = markup_elem "paragraph";
val (text_foldN, text_fold) = markup_elem "text_fold";

val (document_markerN, document_marker) = markup_elem "document_marker";
val (document_tagN, document_tag) = markup_string "document_tag" nameN;


(* Markdown document structure *)

val (markdown_paragraphN, markdown_paragraph) = markup_elem "markdown_paragraph";
val (markdown_itemN, markdown_item) = markup_elem "markdown_item";
val (markdown_bulletN, markdown_bullet) = markup_int "markdown_bullet" "depth";
val (markdown_listN, markdown_list) = markup_string "markdown_list" kindN;

val itemizeN = "itemize";
val enumerateN = "enumerate";
val descriptionN = "description";


(* formal input *)

val inputN = "input";
fun input delimited props = (inputN, (delimitedN, Value.print_bool delimited) :: props);


(* outer syntax *)

val (command_keywordN, command_keyword) = markup_elem "command_keyword";

val commandN = "command"; val command_properties = properties [(kindN, commandN)];
val keywordN = "keyword"; val keyword_properties = properties [(kindN, keywordN)];

val (keyword1N, keyword1) = markup_elem "keyword1";
val (keyword2N, keyword2) = markup_elem "keyword2";
val (keyword3N, keyword3) = markup_elem "keyword3";
val (quasi_keywordN, quasi_keyword) = markup_elem "quasi_keyword";
val (improperN, improper) = markup_elem "improper";
val (operatorN, operator) = markup_elem "operator";
val (stringN, string) = markup_elem "string";
val (alt_stringN, alt_string) = markup_elem "alt_string";
val (verbatimN, verbatim) = markup_elem "verbatim";
val (cartoucheN, cartouche) = markup_elem "cartouche";
val (commentN, comment) = markup_elem "comment";


(* comments *)

val (comment1N, comment1) = markup_elem "comment1";
val (comment2N, comment2) = markup_elem "comment2";
val (comment3N, comment3) = markup_elem "comment3";


(* timing *)

val elapsedN = "elapsed";
val cpuN = "cpu";
val gcN = "gc";

fun timing_properties {elapsed, cpu, gc} =
 [(elapsedN, Value.print_time elapsed),
  (cpuN, Value.print_time cpu),
  (gcN, Value.print_time gc)];

val timingN = "timing";
fun timing t = (timingN, timing_properties t);


(* command timing *)

fun parse_command_timing_properties props =
  (case (Properties.get props fileN, Properties.get props offsetN, Properties.get props nameN) of
    (SOME file, SOME offset, SOME name) =>
      SOME ({file = file, offset = Value.parse_int offset, name = name},
        Properties.seconds props elapsedN)
  | _ => NONE);


(* indentation *)

val (command_indentN, command_indent) = markup_int "command_indent" indentN;


(* goals *)

val (goalN, goal) = markup_elem "goal";
val (subgoalN, subgoal) = markup_string "subgoal" nameN;


(* command status *)

val taskN = "task";

val (forkedN, forked) = markup_elem "forked";
val (joinedN, joined) = markup_elem "joined";
val (runningN, running) = markup_elem "running";
val (finishedN, finished) = markup_elem "finished";
val (failedN, failed) = markup_elem "failed";
val (canceledN, canceled) = markup_elem "canceled";
val (initializedN, initialized) = markup_elem "initialized";
val (finalizedN, finalized) = markup_elem "finalized";
val (consolidatingN, consolidating) = markup_elem "consolidating";
val (consolidatedN, consolidated) = markup_elem "consolidated";


(* messages *)

val exec_idN = "exec_id";

val initN = "init";
val (statusN, status) = markup_elem "status";
val (resultN, result) = markup_elem "result";
val (writelnN, writeln) = markup_elem "writeln";
val (stateN, state) = markup_elem "state"
val (informationN, information) = markup_elem "information";
val (tracingN, tracing) = markup_elem "tracing";
val (warningN, warning) = markup_elem "warning";
val (legacyN, legacy) = markup_elem "legacy";
val (errorN, error) = markup_elem "error";
val (systemN, system) = markup_elem "system";
val protocolN = "protocol";

val (reportN, report) = markup_elem "report";
val (no_reportN, no_report) = markup_elem "no_report";

val badN = "bad";
fun bad () = (badN, serial_properties (serial ()));

val (intensifyN, intensify) = markup_elem "intensify";


(* active areas *)

val browserN = "browser"
val graphviewN = "graphview";
val theory_exportsN = "theory_exports";

val sendbackN = "sendback";
val paddingN = "padding";
val padding_line = (paddingN, "line");
val padding_command = (paddingN, "command");

val dialogN = "dialog";
fun dialog i result = (dialogN, [(serialN, Value.print_int i), (resultN, result)]);

val jedit_actionN = "jedit_action";


(* protocol message functions *)

val functionN = "function"

fun ML_statistics {pid, stats_dir} =
  [(functionN, "ML_statistics"), ("pid", Value.print_int pid), ("stats_dir", stats_dir)];

val commands_accepted = [(functionN, "commands_accepted")];

val assign_update = [(functionN, "assign_update")];
val removed_versions = [(functionN, "removed_versions")];

fun invoke_scala name id thread =
  [(functionN, "invoke_scala"), (nameN, name), (idN, id), ("thread", Value.print_bool thread)];

fun cancel_scala id = [(functionN, "cancel_scala"), (idN, id)];

val task_statistics = (functionN, "task_statistics");

val command_timing = (functionN, "command_timing");

val theory_timing = (functionN, "theory_timing");

val session_timing = (functionN, "session_timing");

fun loading_theory name = [("function", "loading_theory"), (nameN, name)];
fun finished_theory name = [("function", "finished_theory"), (nameN, name)];

val build_session_finished = [("function", "build_session_finished")];

val print_operationsN = "print_operations";
val print_operations = [(functionN, print_operationsN)];


(* export *)

val exportN = "export";

type export_args =
 {id: string option,
  serial: serial,
  theory_name: string,
  name: string,
  executable: bool,
  compress: bool,
  strict: bool};

fun export ({id, serial, theory_name, name, executable, compress, strict}: export_args) =
 [(functionN, exportN),
  (idN, the_default "" id),
  (serialN, Value.print_int serial),
  ("theory_name", theory_name),
  (nameN, name),
  ("executable", Value.print_bool executable),
  ("compress", Value.print_bool compress),
  ("strict", Value.print_bool strict)];


(* debugger *)

fun debugger_state name = [(functionN, "debugger_state"), (nameN, name)];
fun debugger_output name = [(functionN, "debugger_output"), (nameN, name)];


(* simplifier trace *)

val simp_trace_panelN = "simp_trace_panel";

val simp_trace_logN = "simp_trace_log";
val simp_trace_stepN = "simp_trace_step";
val simp_trace_recurseN = "simp_trace_recurse";
val simp_trace_hintN = "simp_trace_hint";
val simp_trace_ignoreN = "simp_trace_ignore";

fun simp_trace_cancel i = [(functionN, "simp_trace_cancel"), (serialN, Value.print_int i)];



(** print mode operations **)

type output = Output.output * Output.output;

val no_output = ("", "");

local
  val default = {output = Output_Primitives.markup_fn};
  val modes = Synchronized.var "Markup.modes" (Symtab.make [("", default)]);
in
  fun add_mode name output =
    Synchronized.change modes (fn tab =>
      (if not (Symtab.defined tab name) then ()
       else Output.warning ("Redefining markup mode " ^ quote name);
       Symtab.update (name, {output = output}) tab));
  fun get_mode () =
    the_default default
      (Library.get_first (Symtab.lookup (Synchronized.value modes)) (print_mode_value ()));
end;

fun output m = if is_empty m then no_output else #output (get_mode ()) m;

val enclose = output #-> Library.enclose;

fun markup m =
  let val (bg, en) = output m
  in Library.enclose (Output.escape bg) (Output.escape en) end;

val markups = fold_rev markup;

fun markup_only m = markup m "";

fun markup_report "" = ""
  | markup_report txt = markup report txt;

end;
