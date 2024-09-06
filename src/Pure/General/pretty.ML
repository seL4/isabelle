(*  Title:      Pure/General/pretty.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Markus Wenzel, TU Munich

Generic pretty printing module.

Loosely based on
  D. C. Oppen, "Pretty Printing",
  ACM Transactions on Programming Languages and Systems (1980), 465-483.

The object to be printed is given as a tree with indentation and line
breaking information.  A "break" inserts a newline if the text until
the next break is too long to fit on the current line.  After the newline,
text is indented to the level of the enclosing block.  Normally, if a block
is broken then all enclosing blocks will also be broken.

The stored length of a block is used in break_dist (to treat each inner block as
a unit for breaking).
*)

signature PRETTY =
sig
  val default_indent: string -> int -> Output.output
  val add_mode: string -> (string -> int -> Output.output) -> unit
  type T
  val to_ML: T -> ML_Pretty.pretty
  val from_ML: ML_Pretty.pretty -> T
  val make_block: {markup: Markup.output, consistent: bool, indent: int} ->
    T list -> T
  val markup_block: {markup: Markup.T, consistent: bool, indent: int} -> T list -> T
  val str: string -> T
  val dots: T
  val brk: int -> T
  val brk_indent: int -> int -> T
  val fbrk: T
  val breaks: T list -> T list
  val fbreaks: T list -> T list
  val blk: int * T list -> T
  val block0: T list -> T
  val block1: T list -> T
  val block: T list -> T
  val strs: string list -> T
  val markup: Markup.T -> T list -> T
  val mark: Markup.T -> T -> T
  val mark_str: Markup.T * string -> T
  val marks_str: Markup.T list * string -> T
  val item: T list -> T
  val text_fold: T list -> T
  val keyword1: string -> T
  val keyword2: string -> T
  val text: string -> T list
  val paragraph: T list -> T
  val para: string -> T
  val quote: T -> T
  val cartouche: T -> T
  val separate: string -> T list -> T list
  val commas: T list -> T list
  val enclose: string -> string -> T list -> T
  val enum: string -> string -> string -> T list -> T
  val position: Position.T -> T
  val here: Position.T -> T list
  val list: string -> string -> T list -> T
  val str_list: string -> string -> string list -> T
  val big_list: string -> T list -> T
  val indent: int -> T -> T
  val unbreakable: T -> T
  val margin_default: int Unsynchronized.ref
  val regularN: string
  val symbolicN: string
  val output_buffer: int option -> T -> Buffer.T
  val output: int option -> T -> Output.output list
  val string_of_margin: int -> T -> string
  val string_of: T -> string
  val writeln: T -> unit
  val symbolic_output: T -> Output.output list
  val symbolic_string_of: T -> string
  val unformatted_string_of: T -> string
  val markup_chunks: Markup.T -> T list -> T
  val chunks: T list -> T
  val chunks2: T list -> T
  val block_enclose: T * T -> T list -> T
  val writeln_chunks: T list -> unit
  val writeln_chunks2: T list -> unit
end;

structure Pretty: PRETTY =
struct

(** print mode operations **)

fun default_indent (_: string) = Symbol.spaces;

local
  val default = {indent = default_indent};
  val modes = Synchronized.var "Pretty.modes" (Symtab.make [("", default)]);
in
  fun add_mode name indent =
    Synchronized.change modes (fn tab =>
      (if not (Symtab.defined tab name) then ()
       else warning ("Redefining pretty mode " ^ quote name);
       Symtab.update (name, {indent = indent}) tab));
  fun get_mode () =
    the_default default
      (Library.get_first (Symtab.lookup (Synchronized.value modes)) (print_mode_value ()));
end;

fun mode_indent x y = #indent (get_mode ()) x y;

val output_spaces = Output.output_width o Symbol.spaces;
val buffer_output_spaces = Buffer.add o #1 o output_spaces;



(** printing items: compound phrases, strings, and breaks **)

val force_nat = Integer.max 0;
val short_nat = FixedInt.fromInt o force_nat;
val long_nat = force_nat o FixedInt.toInt;

datatype tree =
    Block of Markup.output * bool * int * tree list * int
      (*markup output, consistent, indentation, body, length*)
  | Break of bool * int * int  (*mandatory flag, width if not taken, extra indentation if taken*)
  | Str of Output.output * int;  (*string output, length*)

fun tree_length (Block (_, _, _, _, len)) = len
  | tree_length (Break (_, wd, _)) = wd
  | tree_length (Str (_, len)) = len;

abstype T = T of ML_Pretty.pretty
with

fun to_ML (T prt) = prt;
val from_ML = T;

fun make_block {markup = (bg, en), consistent, indent} body =
  let
    val context =
      (if bg = "" then [] else [ML_Pretty.ContextProperty ("begin", bg)]) @
      (if en = "" then [] else [ML_Pretty.ContextProperty ("end", en)]);
    val ind = short_nat indent;
  in T (ML_Pretty.PrettyBlock (ind, consistent, context, map to_ML body)) end;

fun markup_block {markup, consistent, indent} body =
  make_block {markup = Markup.output markup, consistent = consistent, indent = indent} body;



(** derived operations to create formatting expressions **)

val str = T o ML_Pretty.str;
val dots = T ML_Pretty.dots;

fun brk_indent wd ind = T (ML_Pretty.PrettyBreak (short_nat wd, short_nat ind));
fun brk wd = brk_indent wd 0;
val fbrk = T ML_Pretty.PrettyLineBreak;

fun breaks prts = Library.separate (brk 1) prts;
fun fbreaks prts = Library.separate fbrk prts;

fun blk (indent, es) =
  markup_block {markup = Markup.empty, consistent = false, indent = indent} es;

fun block0 prts = blk (0, prts);
fun block1 prts = blk (1, prts);
fun block prts = blk (2, prts);
val strs = block o breaks o map str;

fun markup m = markup_block {markup = m, consistent = false, indent = 0};
fun mark m prt = if m = Markup.empty then prt else markup m [prt];
fun mark_str (m, s) = mark m (str s);
fun marks_str (ms, s) = fold_rev mark ms (str s);

val item = markup Markup.item;
val text_fold = markup Markup.text_fold;

fun keyword1 name = mark_str (Markup.keyword1, name);
fun keyword2 name = mark_str (Markup.keyword2, name);

val text = breaks o map str o Symbol.explode_words;
val paragraph = markup Markup.paragraph;
val para = paragraph o text;

fun quote prt = block1 [str "\"", prt, str "\""];
fun cartouche prt = block1 [str Symbol.open_, prt, str Symbol.close];

fun separate sep prts =
  flat (Library.separate [str sep, brk 1] (map single prts));

val commas = separate ",";

fun enclose lpar rpar prts =
  block (str lpar :: (prts @ [str rpar]));

fun enum sep lpar rpar prts = enclose lpar rpar (separate sep prts);

val position =
  enum "," "{" "}" o map (str o Properties.print_eq) o Position.properties_of;

fun here pos =
  let
    val props = Position.properties_of pos;
    val (s1, s2) = Position.here_strs pos;
  in
    if s2 = "" then []
    else [str s1, mark_str (Markup.properties props Markup.position, s2)]
  end;

val list = enum ",";
fun str_list lpar rpar strs = list lpar rpar (map str strs);

fun big_list name prts = block (fbreaks (str name :: prts));

fun indent 0 prt = prt
  | indent n prt = block0 [str (Symbol.spaces n), prt];

val unbreakable =
  let
    fun unbreak (ML_Pretty.PrettyBlock (ind, consistent, context, body)) =
          ML_Pretty.PrettyBlock (ind, consistent, context, map unbreak body)
      | unbreak (ML_Pretty.PrettyBreak (wd, _)) =
          ML_Pretty.str (Symbol.spaces (long_nat wd))
      | unbreak prt = prt;
  in to_ML #> unbreak #> from_ML end;



(** formatting **)

(* formatted output *)

local

type text = {tx: Buffer.T, ind: Buffer.T, pos: int, nl: int};

val empty: text =
 {tx = Buffer.empty,
  ind = Buffer.empty,
  pos = 0,
  nl = 0};

fun newline {tx, ind = _, pos = _, nl} : text =
 {tx = Buffer.add (Output.output "\n") tx,
  ind = Buffer.empty,
  pos = 0,
  nl = nl + 1};

fun control s {tx, ind, pos: int, nl} : text =
 {tx = Buffer.add s tx,
  ind = ind,
  pos = pos,
  nl = nl};

fun string (s, len) {tx, ind, pos: int, nl} : text =
 {tx = Buffer.add s tx,
  ind = Buffer.add s ind,
  pos = pos + len,
  nl = nl};

val blanks = string o output_spaces;

fun indentation (buf, len) {tx, ind, pos, nl} : text =
  let val s = Buffer.content buf in
   {tx = Buffer.add (mode_indent s len) tx,
    ind = Buffer.add s ind,
    pos = pos + len,
    nl = nl}
  end;

(*Add the lengths of the expressions until the next Break; if no Break then
  include "after", to account for text following this block.*)
fun break_dist (Break _ :: _, _) = 0
  | break_dist (e :: es, after) = tree_length e + break_dist (es, after)
  | break_dist ([], after) = after;

val fbreak = Break (true, 1, 0);

val force_break = fn Break (false, wd, ind) => Break (true, wd, ind) | e => e;
val force_all = map force_break;

(*Search for the next break (at this or higher levels) and force it to occur.*)
fun force_next [] = []
  | force_next ((e as Break _) :: es) = force_break e :: es
  | force_next (e :: es) = e :: force_next es;

fun block_length indent =
  let
    fun block_len len prts =
      let
        val (line, rest) = chop_prefix (fn Break (true, _, _) => false | _ => true) prts;
        val len' = Int.max (fold (Integer.add o tree_length) line 0, len);
      in
        (case rest of
          Break (true, _, ind) :: rest' =>
            block_len len' (Break (false, indent + ind, 0) :: rest')
        | [] => len')
      end;
  in block_len 0 end;

fun property context name =
  let
    fun get (ML_Pretty.ContextProperty (a, b)) = if name = a then SOME b else NONE
      | get _ = NONE;
  in the_default "" (get_first get context) end;

in

fun output_tree make_length =
  let
    fun out (T (ML_Pretty.PrettyBlock (ind, consistent, context, body))) =
          let
            val bg = property context "begin";
            val en = property context "end";
            val indent = long_nat ind;
            val body' = map (out o T) body;
            val len = if make_length then block_length indent body' else ~1;
          in Block ((bg, en), consistent, indent, body', len) end
      | out (T (ML_Pretty.PrettyBreak (wd, ind))) = Break (false, long_nat wd, long_nat ind)
      | out (T ML_Pretty.PrettyLineBreak) = fbreak
      | out (T (ML_Pretty.PrettyString s)) = Str (Output.output_width s ||> force_nat)
      | out (T (ML_Pretty.PrettyStringWithWidth (s, n))) = Str (s, long_nat n);
  in out end;

fun format_tree margin input =
  let
    val breakgain = margin div 20;     (*minimum added space required of a break*)
    val emergencypos = margin div 2;   (*position too far to right*)

    (*es is list of expressions to print;
      blockin is the indentation of the current block;
      after is the width of the following context until next break.*)
    fun format ([], _, _) text = text
      | format (e :: es, block as (_, blockin), after) (text as {ind, pos, nl, ...}) =
          (case e of
            Block ((bg, en), consistent, indent, bes, blen) =>
              let
                val pos' = pos + indent;
                val pos'' = pos' mod emergencypos;
                val block' =
                  if pos' < emergencypos then (ind |> buffer_output_spaces indent, pos')
                  else (buffer_output_spaces pos'' Buffer.empty, pos'');
                val d = break_dist (es, after)
                val bes' = if consistent andalso pos + blen > margin - d then force_all bes else bes;
                val btext: text = text
                  |> control bg
                  |> format (bes', block', d)
                  |> control en;
                (*if this block was broken then force the next break*)
                val es' = if nl < #nl btext then force_next es else es;
              in format (es', block, after) btext end
          | Break (force, wd, ind) =>
              (*no break if text to next break fits on this line
                or if breaking would add only breakgain to space*)
              format (es, block, after)
                (if not force andalso
                    pos + wd <= Int.max (margin - break_dist (es, after), blockin + breakgain)
                 then text |> blanks wd  (*just insert wd blanks*)
                 else text |> newline |> indentation block |> blanks ind)
          | Str str => format (es, block, after) (string str text));
  in
    #tx (format ([output_tree true input], (Buffer.empty, 0), 0) empty)
  end;

end;


(* special output *)

(*symbolic markup -- no formatting*)
val symbolic =
  let
    fun out (Block ((bg, en), _, _, [], _)) = Buffer.add bg #> Buffer.add en
      | out (Block ((bg, en), consistent, indent, prts, _)) =
          Buffer.add bg #>
          Buffer.markup (Markup.block consistent indent) (fold out prts) #>
          Buffer.add en
      | out (Break (false, wd, ind)) = Buffer.markup (Markup.break wd ind) (buffer_output_spaces wd)
      | out (Break (true, _, _)) = Buffer.add (Output.output "\n")
      | out (Str (s, _)) = Buffer.add s;
  in Buffer.build o out o output_tree false end;

(*unformatted output*)
val unformatted =
  let
    fun out (Block ((bg, en), _, _, prts, _)) = Buffer.add bg #> fold out prts #> Buffer.add en
      | out (Break (_, wd, _)) = buffer_output_spaces wd
      | out (Str (s, _)) = Buffer.add s;
  in Buffer.build o out o output_tree false end;


(* output interfaces *)

val margin_default = Unsynchronized.ref ML_Pretty.default_margin;  (*right margin, or page width*)

val regularN = "pretty_regular";
val symbolicN = "pretty_symbolic";

fun output_buffer margin prt =
  if print_mode_active symbolicN andalso not (print_mode_active regularN)
  then symbolic prt
  else format_tree (the_default (! margin_default) margin) prt;

val output = Buffer.contents oo output_buffer;
fun string_of_margin margin = implode o Output.escape o output (SOME margin);
val string_of = implode o Output.escape o output NONE;
val writeln = Output.writelns o Output.escape o output NONE;

val symbolic_output = Buffer.contents o symbolic;
val symbolic_string_of = implode o Output.escape o symbolic_output;

val unformatted_string_of = implode o Output.escape o Buffer.contents o unformatted;


(* chunks *)

fun markup_chunks m prts = markup m (fbreaks (map (text_fold o single) prts));
val chunks = markup_chunks Markup.empty;

fun chunks2 prts =
  (case try split_last prts of
    NONE => block0 []
  | SOME (prefix, last) =>
      block0 (maps (fn prt => [text_fold [prt, fbrk], fbrk]) prefix @ [text_fold [last]]));

fun block_enclose (prt1, prt2) prts = chunks [block (fbreaks (prt1 :: prts)), prt2];

fun string_of_text_fold prt = string_of prt |> Markup.markup Markup.text_fold;

fun writeln_chunks prts =
  Output.writelns (Library.separate "\n" (map string_of_text_fold prts));

fun writeln_chunks2 prts =
  (case try split_last prts of
    NONE => ()
  | SOME (prefix, last) =>
      (map (fn prt => Markup.markup Markup.text_fold (string_of prt ^ "\n") ^ "\n") prefix @
        [string_of_text_fold last])
      |> Output.writelns);

end;

end;

structure ML_Pretty: ML_PRETTY =
struct
  open ML_Pretty;
  val string_of = Pretty.string_of o Pretty.from_ML;
end;



(** toplevel pretty printing **)

val _ = ML_system_pp (fn d => fn _ => ML_Pretty.prune (d + 1) o Pretty.to_ML o Pretty.quote);
val _ = ML_system_pp (fn _ => fn _ => Pretty.to_ML o Pretty.position);
val _ = ML_system_pp (fn _ => fn _ => Pretty.to_ML o Pretty.mark_str o Path.print_markup);

val _ =
  ML_system_pp (fn _ => fn _ => fn t =>
    ML_Pretty.str ("<thread " ^ quote (Isabelle_Thread.print t) ^
      (if Isabelle_Thread.is_active t then "" else " (inactive)") ^ ">"));

val _ =
  ML_system_pp (fn _ => fn _ => fn bytes =>
    ML_Pretty.str
     (if Bytes.is_empty bytes then "Bytes.empty"
      else "Bytes {size = " ^ string_of_int (Bytes.size bytes) ^ "}"));
