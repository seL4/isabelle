(*  Title:      Pure/General/pretty.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Makarius

Generic pretty printing.

The object to be printed is given as a tree with blocks and breaks. A block
causes alignment and may specify additional indentation and markup. A break
inserts a newline if the text until the next break is too long to fit on the
current line. After the newline, text is indented to the level of the
enclosing block. Normally, if a block is broken then all enclosing blocks will
also be broken.

References:

  * L. C. Paulson, "ML for the Working Programmer" (1996),
    2nd edition, Cambridge University Press.
    Section 8.10 "A pretty printer"
    https://www.cl.cam.ac.uk/~lp15/MLbook/PDF/chapter8.pdf

  * D. C. Oppen, "Pretty Printing",
    ACM Transactions on Programming Languages and Systems (1980), 465-483.
*)

signature PRETTY =
sig
  type T
  val to_ML: T -> ML_Pretty.pretty
  val from_ML: ML_Pretty.pretty -> T
  val blk: int * T list -> T
  val block0: T list -> T
  val block1: T list -> T
  val block: T list -> T
  type 'a block = {markup: 'a, open_block: bool, consistent: bool, indent: int}
  val make_block: Markup.output block -> T list -> T
  val markup_block: Markup.T block -> T list -> T
  val markup: Markup.T -> T list -> T
  val markup_open: Markup.T -> T list -> T
  val mark: Markup.T -> T -> T
  val mark_open: Markup.T -> T -> T
  val markup_blocks: Markup.T list block -> T list -> T
  val str: string -> T
  val dots: T
  val brk: int -> T
  val brk_indent: int -> int -> T
  val fbrk: T
  val breaks: T list -> T list
  val fbreaks: T list -> T list
  val strs: string list -> T
  val mark_str: Markup.T * string -> T
  val marks_str: Markup.T list * string -> T
  val mark_position: Position.T -> T -> T
  val mark_str_position: Position.T * string -> T
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
  type output_ops =
   {symbolic: bool,
    output: string -> Output.output * int,
    markup: Markup.output -> Markup.output,
    indent_markup: Markup.output,
    margin: int}
  val output_ops: int option -> output_ops
  val pure_output_ops: int option -> output_ops
  val markup_output_ops: int option -> output_ops
  val symbolic_output_ops: output_ops
  val symbolic_output: T -> Bytes.T
  val symbolic_string_of: T -> string
  val unformatted_string_of: T -> string
  val output: output_ops -> T -> Bytes.T
  val string_of_ops: output_ops -> T -> string
  val string_of: T -> string
  val pure_string_of: T -> string
  val writeln: T -> unit
  val markup_chunks: Markup.T -> T list -> T
  val chunks: T list -> T
  val chunks2: T list -> T
  val block_enclose: T * T -> T list -> T
  val writeln_chunks: T list -> unit
  val writeln_chunks2: T list -> unit
end;

structure Pretty: PRETTY =
struct

(** Pretty.T **)

(* abstype: ML_Pretty.pretty without (op =) *)

abstype T = T of ML_Pretty.pretty
with
  fun to_ML (T prt) = prt;
  val from_ML = T;
end;

val force_nat = Integer.max 0;
val short_nat = FixedInt.fromInt o force_nat;
val long_nat = force_nat o FixedInt.toInt;


(* blocks *)

fun blk (indent, body) =
  from_ML (ML_Pretty.PrettyBlock (short_nat indent, false, [], map to_ML body));

fun block0 body = blk (0, body);
fun block1 body = blk (1, body);
fun block body = blk (2, body);


(* blocks with markup *)

type 'a block = {markup: 'a, open_block: bool, consistent: bool, indent: int}

fun make_block ({markup, open_block, consistent, indent}: Markup.output block) body =
  let
    val context =
      ML_Pretty.markup_context markup @
      ML_Pretty.open_block_context open_block;
  in from_ML (ML_Pretty.PrettyBlock (short_nat indent, consistent, context, map to_ML body)) end;

fun markup_block ({markup, open_block, consistent, indent}: Markup.T block) body =
  make_block
   {markup = YXML.output_markup markup,
    open_block = open_block,
    consistent = consistent,
    indent = indent} body;

fun markup m = markup_block {markup = m, open_block = false, consistent = false, indent = 0};
fun markup_open m = markup_block {markup = m, open_block = true, consistent = false, indent = 0};

fun mark m prt = if m = Markup.empty then prt else markup m [prt];
fun mark_open m prt = if m = Markup.empty then prt else markup_open m [prt];

fun markup_blocks ({markup, open_block, consistent, indent}: Markup.T list block) body =
  if forall Markup.is_empty markup andalso not open_block andalso not consistent
  then blk (indent, body)
  else
    let
      val markups = filter_out Markup.is_empty markup;
      val (ms, m) = if null markups then ([], Markup.empty) else split_last markups;
    in
      fold_rev mark_open ms
        (markup_block
          {markup = m, open_block = open_block, consistent = consistent, indent = indent} body)
    end;


(* breaks *)

fun brk_indent wd ind = from_ML (ML_Pretty.PrettyBreak (short_nat wd, short_nat ind));
fun brk wd = brk_indent wd 0;
val fbrk = from_ML ML_Pretty.PrettyLineBreak;

fun breaks prts = Library.separate (brk 1) prts;
fun fbreaks prts = Library.separate fbrk prts;


(* derived operations to create formatting expressions *)

val str = from_ML o ML_Pretty.str;
val dots = from_ML ML_Pretty.dots;

val strs = block o breaks o map str;

fun mark_str (m, s) = mark_open m (str s);
fun marks_str (ms, s) = fold_rev mark_open ms (str s);

val mark_position = mark o Position.markup;
fun mark_str_position (pos, s) = mark_str (Position.markup pos, s);

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
  let val (s1, s2) = Position.here_strs pos
  in if s2 = "" then [] else [str s1, mark_str_position (pos, s2)] end;

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

(* output operations *)

type output_ops =
 {symbolic: bool,
  output: string -> Output.output * int,
  markup: Markup.output -> Markup.output,
  indent_markup: Markup.output,
  margin: int};

fun make_output_ops {symbolic, markup} opt_margin : output_ops =
 {symbolic = symbolic,
  output = fn s => (s, size s),
  markup = markup,
  indent_markup = Markup.no_output,
  margin = ML_Pretty.get_margin opt_margin};

val pure_output_ops = make_output_ops {symbolic = false, markup = K Markup.no_output};
val markup_output_ops = make_output_ops {symbolic = false, markup = I};
val symbolic_output_ops = make_output_ops {symbolic = true, markup = I} NONE;

fun output_ops opt_margin =
  if Print_Mode.PIDE_enabled () then symbolic_output_ops
  else pure_output_ops opt_margin;

fun output_newline (ops: output_ops) = #1 (#output ops "\n");

fun output_spaces (ops: output_ops) = #output ops o Symbol.spaces;
fun output_spaces_buffer ops = Buffer.add o #1 o output_spaces ops;
fun output_spaces_bytes ops = Bytes.add o #1 o output_spaces ops;


(* output tree *)

datatype tree =
    Block of
     {markup: Markup.output,
      open_block: bool,
      consistent: bool,
      indent: int,
      body: tree list,
      length: int}
  | Break of bool * int * int  (*mandatory flag, width if not taken, extra indentation if taken*)
  | Str of Output.output * int  (*string output, length*)
  | Raw of Output.output;  (*raw output: no length, no indent*)

fun tree_length (Block {length = len, ...}) = len
  | tree_length (Break (_, wd, _)) = wd
  | tree_length (Str (_, len)) = len
  | tree_length (Raw _) = 0;

local

fun block_length indent =
  let
    fun block_len len body =
      let
        val (line, rest) = chop_prefix (fn Break (true, _, _) => false | _ => true) body;
        val len' = Int.max (fold (Integer.add o tree_length) line 0, len);
      in
        (case rest of
          Break (true, _, ind) :: rest' =>
            block_len len' (Break (false, indent + ind, 0) :: rest')
        | [] => len')
      end;
  in block_len 0 end;

val fbreak = Break (true, 1, 0);

in

fun output_tree (ops: output_ops) make_length =
  let
    fun tree (ML_Pretty.PrettyBlock (ind, consistent, context, body)) =
          let
            val indent = long_nat ind;
            val body' = map tree body;
          in
            Block
             {markup = #markup ops (ML_Pretty.markup_get context),
              open_block = ML_Pretty.open_block_detect context,
              consistent = consistent,
              indent = indent,
              body = body',
              length = if make_length then block_length indent body' else ~1}
          end
      | tree (ML_Pretty.PrettyBreak (wd, ind)) = Break (false, long_nat wd, long_nat ind)
      | tree ML_Pretty.PrettyLineBreak = fbreak
      | tree (ML_Pretty.PrettyString s) = Str (#output ops s ||> force_nat)
      | tree (ML_Pretty.PrettyStringWithWidth (s, n)) = Str (s, long_nat n);
  in tree o to_ML end;

end;


(* formatted output *)

local

type text = {tx: Bytes.T, ind: Buffer.T, pos: int, nl: int};

val empty: text =
 {tx = Bytes.empty,
  ind = Buffer.empty,
  pos = 0,
  nl = 0};

fun string (s, len) {tx, ind, pos: int, nl} : text =
 {tx = Bytes.add s tx,
  ind = Buffer.add s ind,
  pos = pos + len,
  nl = nl};

fun raw s {tx, ind, pos: int, nl} : text =
 {tx = Bytes.add s tx,
  ind = ind,
  pos = pos,
  nl = nl};

(*Add the lengths of the expressions until the next Break; if no Break then
  include "after", to account for text following this block.*)
fun break_dist (Break _ :: _, _) = 0
  | break_dist (prt :: prts, after) = tree_length prt + break_dist (prts, after)
  | break_dist ([], after) = after;

val force_break = fn Break (false, wd, ind) => Break (true, wd, ind) | prt => prt;

(*Search for the next break (at this or higher levels) and force it to occur.*)
fun force_next [] = []
  | force_next ((prt as Break _) :: prts) = force_break prt :: prts
  | force_next (prt :: prts) = prt :: force_next prts;

in

fun format_tree (ops: output_ops) input =
  let
    val margin = #margin ops;
    val breakgain = margin div 20;     (*minimum added space required of a break*)
    val emergencypos = margin div 2;   (*position too far to right*)

    val newline = output_newline ops;
    val blanks = string o output_spaces ops;

    val indent_markup = #indent_markup ops;
    val no_indent_markup = indent_markup = Markup.no_output;
    val (indent_bg, indent_en) = apply2 Substring.full indent_markup;

    val add_indent = if no_indent_markup then K I else output_spaces_buffer ops;

    fun break_indent (buf, n) ({tx, nl, ...}: text) : text =
      let
        val s = Buffer.content buf;
        val indent =
          if no_indent_markup then Bytes.add (Symbol.spaces n)
          else if s = "" then I
          else Bytes.add_substring indent_bg #> Bytes.add s #> Bytes.add_substring indent_en;
        val tx' = tx |> Bytes.add newline |> indent;
        val ind' = Buffer.add s Buffer.empty;
      in {tx = tx', ind = ind', pos = n, nl = nl + 1} end;

    (*blockin is the indentation of the current block;
      after is the width of the following context until next break.*)
    fun format ([], _, _) text = text
      | format (prt :: prts, block as (_, blockin), after) (text as {ind, pos, nl, ...}) =
          (case prt of
            Block {markup = (bg, en), open_block = true, body, ...} =>
              text |> raw bg |> format (body @ Raw en :: prts, block, after)
          | Block {markup = (bg, en), consistent, indent, body, length = blen, ...} =>
              let
                val pos' = pos + indent;
                val pos'' = pos' mod emergencypos;
                val block' =
                  if pos' < emergencypos
                  then (add_indent indent ind, pos')
                  else (add_indent pos'' Buffer.empty, pos'');
                val after' = break_dist (prts, after)
                val body' = body
                  |> (consistent andalso pos + blen > margin - after') ? map force_break;
                val btext: text =
                  text |> raw bg |> format (body' @ [Raw en], block', after');
                (*if this block was broken then force the next break*)
                val prts' = if nl < #nl btext then force_next prts else prts;
              in format (prts', block, after) btext end
          | Break (force, wd, ind) =>
              (*no break if text to next break fits on this line
                or if breaking would add only breakgain to space*)
              format (prts, block, after)
                (if not force andalso
                    pos + wd <= Int.max (margin - break_dist (prts, after), blockin + breakgain)
                 then text |> blanks wd  (*just insert wd blanks*)
                 else text |> break_indent block |> blanks ind)
          | Str str => format (prts, block, after) (string str text)
          | Raw s => format (prts, block, after) (raw s text));
  in
    #tx (format ([output_tree ops true input], (Buffer.empty, 0), 0) empty)
  end;

end;



(** no formatting **)

(* symbolic output: XML markup for blocks/breaks + other markup *)

val symbolic_output =
  let
    val ops = symbolic_output_ops;

    fun markup_bytes m output_body =
      let val (bg, en) = #markup ops (YXML.output_markup m)
      in Bytes.add bg #> output_body #> Bytes.add en end;

    fun output (Block {markup = (bg, en), body = [], ...}) = Bytes.add bg #> Bytes.add en
      | output (Block {markup = (bg, en), open_block = true, body, ...}) =
          Bytes.add bg #> fold output body #> Bytes.add en
      | output (Block {markup = (bg, en), consistent, indent, body, ...}) =
          let val block_markup = Markup.block {consistent = consistent, indent = indent}
          in Bytes.add bg #> markup_bytes block_markup (fold output body) #> Bytes.add en end
      | output (Break (false, wd, ind)) =
          markup_bytes (Markup.break {width = wd, indent = ind}) (output_spaces_bytes ops wd)
      | output (Break (true, _, _)) = Bytes.add (output_newline ops)
      | output (Str (s, _)) = Bytes.add s
      | output (Raw s) = Bytes.add s;
  in Bytes.build o output o output_tree ops false end;

val symbolic_string_of = Bytes.content o symbolic_output;


(* unformatted output: other markup only *)

fun unformatted ops =
  let
    fun output (Block ({markup = (bg, en), body, ...})) =
          Bytes.add bg #> fold output body #> Bytes.add en
      | output (Break (_, wd, _)) = output_spaces_bytes ops wd
      | output (Str (s, _)) = Bytes.add s
      | output (Raw s) = Bytes.add s;
  in Bytes.build o output o output_tree ops false end;

fun unformatted_string_of prt =
  Bytes.content (unformatted (output_ops NONE) prt);


(* output interfaces *)

fun output ops = if #symbolic ops then symbolic_output else format_tree ops;

fun string_of_ops ops = Bytes.content o output ops;
fun string_of prt = string_of_ops (output_ops NONE) prt;

val pure_string_of = string_of_ops (pure_output_ops NONE);

fun writeln prt =
  Output.writelns (Bytes.contents (output (output_ops NONE) prt));


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



(** back-patching **)

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
