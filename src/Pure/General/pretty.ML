(*  Title:      Pure/General/pretty.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:	Markus Wenzel, TU Munich
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Generic pretty printing module.

Loosely based on
  D. C. Oppen, "Pretty Printing",
  ACM Transactions on Programming Languages and Systems (1980), 465-483.

The object to be printed is given as a tree with indentation and line
breaking information.  A "break" inserts a newline if the text until
the next break is too long to fit on the current line.  After the newline,
text is indented to the level of the enclosing block.  Normally, if a block
is broken then all enclosing blocks will also be broken.  Only "inconsistent
breaks" are provided.

The stored length of a block is used in breakdist (to treat each inner block as
a unit for breaking).
*)

type pprint_args = (string -> unit) * (int -> unit) * (int -> unit) *
  (unit -> unit) * (unit -> unit);

signature PRETTY =
  sig
  type T
  val raw_str: string * real -> T
  val str: string -> T
  val brk: int -> T
  val fbrk: T
  val blk: int * T list -> T
  val quote: T -> T
  val commas: T list -> T list
  val breaks: T list -> T list
  val fbreaks: T list -> T list
  val block: T list -> T
  val strs: string list -> T
  val enclose: string -> string -> T list -> T
  val list: string -> string -> T list -> T
  val str_list: string -> string -> string list -> T
  val big_list: string -> T list -> T
  val chunks: T list -> T
  val indent: int -> T -> T
  val string_of: T -> string
  val writeln: T -> unit
  val str_of: T -> string
  val pprint: T -> pprint_args -> unit
  val setdepth: int -> unit
  val setmargin: int -> unit
  val setmp_margin: int -> ('a -> 'b) -> 'a -> 'b
  end;

structure Pretty : PRETTY =
struct

(*printing items: compound phrases, strings, and breaks*)
datatype T =
  Block of T list * int * int |         (*body, indentation, length*)
  String of string * int |              (*text, length*)
  Break of bool * int;                  (*mandatory flag, width if not taken*);

(*Add the lengths of the expressions until the next Break; if no Break then
  include "after", to account for text following this block. *)
fun breakdist (Block(_,_,len)::es, after) = len + breakdist(es, after)
  | breakdist (String (s, len) :: es, after) = len + breakdist (es, after)
  | breakdist (Break _ :: es, after) = 0
  | breakdist ([], after) = after;

fun repstring a 0 = ""
  | repstring a 1 = a
  | repstring a k =
      if k mod 2 = 0 then repstring(a^a) (k div 2)
      else repstring(a^a) (k div 2) ^ a;

val spaces = repstring " ";


(*** Type for lines of text: string, # of lines, position on line ***)

type text = {tx: Buffer.T, nl: int, pos: int};

val emptytext = {tx = Buffer.empty, nl = 0, pos = 0};

fun blanks wd {tx, nl, pos} =
    {tx  = Buffer.add (Symbol.output (spaces wd)) tx,
     nl  = nl,
     pos = pos+wd};

fun newline {tx, nl, pos} =
    {tx  = Buffer.add (Symbol.output "\n") tx,
     nl  = nl + 1,
     pos = 0};

fun string s len {tx, nl, pos:int} =
    {tx  = Buffer.add s tx,
     nl  = nl,
     pos = pos + len};


(*** Formatting ***)

(* margin *)

fun make_margin_info m =
 {margin = m,                   (*right margin, or page width*)
  breakgain = m div 20,         (*minimum added space required of a break*)
  emergencypos = m div 2};      (*position too far to right*)

val margin_info = ref (make_margin_info 76);
fun setmargin m = margin_info := make_margin_info m;
fun setmp_margin m f = setmp margin_info (make_margin_info m) f;

(*Search for the next break (at this or higher levels) and force it to occur*)
fun forcenext [] = []
  | forcenext (Break(_,wd) :: es) = Break(true,0) :: es
  | forcenext (e :: es) = e :: forcenext es;

(*es is list of expressions to print;
  blockin is the indentation of the current block;
  after is the width of the following context until next break. *)
fun format ([], _, _) text = text
  | format (e::es, blockin, after) (text as {pos,nl,...}) =
    (case e of
       Block(bes,indent,wd) =>
         let val blockin' = (pos + indent) mod #emergencypos (! margin_info)
             val btext = format(bes, blockin', breakdist(es,after)) text
             (*If this block was broken then force the next break.*)
             val es2 = if nl < #nl(btext) then forcenext es else es
         in  format (es2,blockin,after) btext  end
     | String (s, len) => format (es,blockin,after) (string s len text)
     | Break(force,wd) => (*no break if text to next break fits on this line
                            or if breaking would add only breakgain to space *)
           format (es,blockin,after)
               (if not force andalso
                   pos+wd <= Int.max(#margin (! margin_info) - breakdist(es,after),
                                     blockin + #breakgain (! margin_info))
                then blanks wd text  (*just insert wd blanks*)
                else blanks blockin (newline text)));


(*** Exported functions to create formatting expressions ***)

fun length (Block (_, _, len)) = len
  | length (String (_, len)) = len
  | length (Break(_, wd)) = wd;

fun raw_str (s, len) = String (s, Real.round len);
val str = String o apsnd Real.round o Symbol.output_width;

fun brk wd = Break (false, wd);
val fbrk = Break (true, 2);

fun blk (indent, es) =
  let
    fun sum([], k) = k
      | sum(e :: es, k) = sum (es, length e + k);
  in Block (es, indent, sum (es, 0)) end;


(* utils *)

fun quote prt =
  blk (1, [str "\"", prt, str "\""]);

fun commas prts =
  flat (separate [str ",", brk 1] (map (fn x => [x]) prts));

fun breaks prts = separate (brk 1) prts;
fun fbreaks prts = separate fbrk prts;

fun block prts = blk (2, prts);

val strs = block o breaks o map str;

fun enclose lpar rpar prts =
  block (str lpar :: (prts @ [str rpar]));

fun list lpar rpar prts = enclose lpar rpar (commas prts);
fun str_list lpar rpar strs = list lpar rpar (map str strs);
fun big_list name prts = block (fbreaks (str name :: prts));
fun chunks prts = blk (0, fbreaks prts);

fun indent 0 prt = prt
  | indent n prt = blk (0, [str (spaces n), prt]);


(*** Pretty printing with depth limitation ***)

val depth       = ref 0;        (*maximum depth; 0 means no limit*)

fun setdepth dp = (depth := dp);

(*Recursively prune blocks, discarding all text exceeding depth dp*)
fun pruning dp (Block(bes,indent,wd)) =
      if dp>0 then blk(indent, map (pruning(dp-1)) bes)
              else str "..."
  | pruning dp e = e;

fun prune dp e = if dp>0 then pruning dp e else e;


fun string_of e = Buffer.content (#tx (format ([prune (! depth) e], 0, 0) emptytext));

val writeln = writeln o string_of;


(*Create a single flat string: no line breaking*)
fun str_of prt =
  let
    fun s_of (Block (prts, _, _)) = implode (map s_of prts)
      | s_of (String (s, _)) = s
      | s_of (Break (false, wd)) = Symbol.output (spaces wd)
      | s_of (Break (true, _)) = Symbol.output " ";
  in s_of (prune (! depth) prt) end;

(*part of the interface to the ML toplevel pretty printers*)
fun pprint prt (put_str, begin_blk, put_brk, put_fbrk, end_blk) =
  let
    fun pp (Block (prts, ind, _)) = (begin_blk ind; pp_lst prts; end_blk ())
      | pp (String (s, _)) = put_str s
      | pp (Break (false, wd)) = put_brk wd
      | pp (Break (true, _)) = put_fbrk ()
    and pp_lst [] = ()
      | pp_lst (prt :: prts) = (pp prt; pp_lst prts);
  in
    pp (prune (! depth) prt)
  end;


end;
