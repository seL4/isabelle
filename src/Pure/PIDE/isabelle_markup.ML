(*  Title:      Pure/PIDE/isabelle_markup.ML
    Author:     Makarius

Isabelle markup elements.
*)

signature ISABELLE_MARKUP =
sig
  val bindingN: string val binding: Markup.T
  val entityN: string val entity: string -> string -> Markup.T
  val get_entity_kind: Markup.T -> string option
  val defN: string
  val refN: string
  val lineN: string
  val offsetN: string
  val end_offsetN: string
  val fileN: string
  val idN: string
  val position_properties': string list
  val position_properties: string list
  val positionN: string val position: Markup.T
  val pathN: string val path: string -> Markup.T
  val indentN: string
  val blockN: string val block: int -> Markup.T
  val widthN: string
  val breakN: string val break: int -> Markup.T
  val fbreakN: string val fbreak: Markup.T
  val hiddenN: string val hidden: Markup.T
  val theoryN: string
  val classN: string
  val type_nameN: string
  val constantN: string
  val fixedN: string val fixed: string -> Markup.T
  val dynamic_factN: string val dynamic_fact: string -> Markup.T
  val tfreeN: string val tfree: Markup.T
  val tvarN: string val tvar: Markup.T
  val freeN: string val free: Markup.T
  val skolemN: string val skolem: Markup.T
  val boundN: string val bound: Markup.T
  val varN: string val var: Markup.T
  val numeralN: string val numeral: Markup.T
  val literalN: string val literal: Markup.T
  val delimiterN: string val delimiter: Markup.T
  val inner_stringN: string val inner_string: Markup.T
  val inner_commentN: string val inner_comment: Markup.T
  val token_rangeN: string val token_range: Markup.T
  val sortN: string val sort: Markup.T
  val typN: string val typ: Markup.T
  val termN: string val term: Markup.T
  val propN: string val prop: Markup.T
  val typingN: string val typing: Markup.T
  val ML_keywordN: string val ML_keyword: Markup.T
  val ML_delimiterN: string val ML_delimiter: Markup.T
  val ML_tvarN: string val ML_tvar: Markup.T
  val ML_numeralN: string val ML_numeral: Markup.T
  val ML_charN: string val ML_char: Markup.T
  val ML_stringN: string val ML_string: Markup.T
  val ML_commentN: string val ML_comment: Markup.T
  val ML_defN: string
  val ML_openN: string
  val ML_structN: string
  val ML_typingN: string val ML_typing: Markup.T
  val ML_sourceN: string val ML_source: Markup.T
  val doc_sourceN: string val doc_source: Markup.T
  val antiqN: string val antiq: Markup.T
  val ML_antiquotationN: string
  val doc_antiquotationN: string
  val doc_antiquotation_optionN: string
  val keywordN: string val keyword: Markup.T
  val operatorN: string val operator: Markup.T
  val commandN: string val command: Markup.T
  val stringN: string val string: Markup.T
  val altstringN: string val altstring: Markup.T
  val verbatimN: string val verbatim: Markup.T
  val commentN: string val comment: Markup.T
  val controlN: string val control: Markup.T
  val tokenN: string val token: Properties.T -> Markup.T
  val elapsedN: string
  val cpuN: string
  val gcN: string
  val timingN: string val timing: Timing.timing -> Markup.T
  val subgoalsN: string
  val proof_stateN: string val proof_state: int -> Markup.T
  val stateN: string val state: Markup.T
  val subgoalN: string val subgoal: Markup.T
  val sendbackN: string val sendback: Markup.T
  val hiliteN: string val hilite: Markup.T
  val taskN: string
  val acceptedN: string val accepted: Markup.T
  val forkedN: string val forked: Markup.T
  val joinedN: string val joined: Markup.T
  val failedN: string val failed: Markup.T
  val finishedN: string val finished: Markup.T
  val serialN: string
  val legacyN: string val legacy: Markup.T
  val promptN: string val prompt: Markup.T
  val reportN: string val report: Markup.T
  val no_reportN: string val no_report: Markup.T
  val badN: string val bad: Markup.T
  val functionN: string
  val assign_execs: Properties.T
  val removed_versions: Properties.T
  val invoke_scala: string -> string -> Properties.T
  val cancel_scala: string -> Properties.T
end;

structure Isabelle_Markup: ISABELLE_MARKUP =
struct

(** markup elements **)

fun markup_elem elem = (elem, (elem, []): Markup.T);
fun markup_string elem prop = (elem, fn s => (elem, [(prop, s)]): Markup.T);
fun markup_int elem prop = (elem, fn i => (elem, [(prop, Markup.print_int i)]): Markup.T);


(* formal entities *)

val (bindingN, binding) = markup_elem "binding";

val entityN = "entity";
fun entity kind name = (entityN, [(Markup.nameN, name), (Markup.kindN, kind)]);

fun get_entity_kind (name, props) =
  if name = entityN then AList.lookup (op =) props Markup.kindN
  else NONE;

val defN = "def";
val refN = "ref";


(* position *)

val lineN = "line";
val offsetN = "offset";
val end_offsetN = "end_offset";
val fileN = "file";
val idN = "id";

val position_properties' = [fileN, idN];
val position_properties = [lineN, offsetN, end_offsetN] @ position_properties';

val (positionN, position) = markup_elem "position";


(* path *)

val (pathN, path) = markup_string "path" Markup.nameN;


(* pretty printing *)

val indentN = "indent";
val (blockN, block) = markup_int "block" indentN;

val widthN = "width";
val (breakN, break) = markup_int "break" widthN;

val (fbreakN, fbreak) = markup_elem "fbreak";


(* hidden text *)

val (hiddenN, hidden) = markup_elem "hidden";


(* logical entities *)

val theoryN = "theory";
val classN = "class";
val type_nameN = "type name";
val constantN = "constant";

val (fixedN, fixed) = markup_string "fixed" Markup.nameN;
val (dynamic_factN, dynamic_fact) = markup_string "dynamic_fact" Markup.nameN;


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
val (inner_commentN, inner_comment) = markup_elem "inner_comment";

val (token_rangeN, token_range) = markup_elem "token_range";

val (sortN, sort) = markup_elem "sort";
val (typN, typ) = markup_elem "typ";
val (termN, term) = markup_elem "term";
val (propN, prop) = markup_elem "prop";

val (typingN, typing) = markup_elem "typing";


(* ML syntax *)

val (ML_keywordN, ML_keyword) = markup_elem "ML_keyword";
val (ML_delimiterN, ML_delimiter) = markup_elem "ML_delimiter";
val (ML_tvarN, ML_tvar) = markup_elem "ML_tvar";
val (ML_numeralN, ML_numeral) = markup_elem "ML_numeral";
val (ML_charN, ML_char) = markup_elem "ML_char";
val (ML_stringN, ML_string) = markup_elem "ML_string";
val (ML_commentN, ML_comment) = markup_elem "ML_comment";

val ML_defN = "ML_def";
val ML_openN = "ML_open";
val ML_structN = "ML_struct";
val (ML_typingN, ML_typing) = markup_elem "ML_typing";


(* embedded source text *)

val (ML_sourceN, ML_source) = markup_elem "ML_source";
val (doc_sourceN, doc_source) = markup_elem "doc_source";

val (antiqN, antiq) = markup_elem "antiq";
val ML_antiquotationN = "ML antiquotation";
val doc_antiquotationN = "document antiquotation";
val doc_antiquotation_optionN = "document antiquotation option";


(* outer syntax *)

val (keywordN, keyword) = markup_elem "keyword";
val (operatorN, operator) = markup_elem "operator";
val (commandN, command) = markup_elem "command";
val (stringN, string) = markup_elem "string";
val (altstringN, altstring) = markup_elem "altstring";
val (verbatimN, verbatim) = markup_elem "verbatim";
val (commentN, comment) = markup_elem "comment";
val (controlN, control) = markup_elem "control";

val tokenN = "token";
fun token props = (tokenN, props);


(* timing *)

val timingN = "timing";
val elapsedN = "elapsed";
val cpuN = "cpu";
val gcN = "gc";

fun timing {elapsed, cpu, gc} =
  (timingN,
   [(elapsedN, Time.toString elapsed),
    (cpuN, Time.toString cpu),
    (gcN, Time.toString gc)]);


(* toplevel *)

val subgoalsN = "subgoals";
val (proof_stateN, proof_state) = markup_int "proof_state" subgoalsN;

val (stateN, state) = markup_elem "state";
val (subgoalN, subgoal) = markup_elem "subgoal";
val (sendbackN, sendback) = markup_elem "sendback";
val (hiliteN, hilite) = markup_elem "hilite";


(* command status *)

val taskN = "task";

val (acceptedN, accepted) = markup_elem "accepted";
val (forkedN, forked) = markup_elem "forked";
val (joinedN, joined) = markup_elem "joined";

val (failedN, failed) = markup_elem "failed";
val (finishedN, finished) = markup_elem "finished";


(* messages *)

val serialN = "serial";

val (legacyN, legacy) = markup_elem "legacy";
val (promptN, prompt) = markup_elem "prompt";

val (reportN, report) = markup_elem "report";
val (no_reportN, no_report) = markup_elem "no_report";

val (badN, bad) = markup_elem "bad";


(* protocol message functions *)

val functionN = "function"

val assign_execs = [(functionN, "assign_execs")];
val removed_versions = [(functionN, "removed_versions")];

fun invoke_scala name id = [(functionN, "invoke_scala"), (Markup.nameN, name), (idN, id)];
fun cancel_scala id = [(functionN, "cancel_scala"), (idN, id)];

end;
