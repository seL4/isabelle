(*  Title:      Pure/Syntax/pretty
    ID:         $Id$
    Author:     Lawrence C Paulson
    Copyright   1991  University of Cambridge

Pretty printing module

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

(* FIXME improve? *)
type pprint_args = (string -> unit) * (int -> unit) * (int -> unit) * (unit -> unit);

signature PRETTY =
  sig
  type T
  val blk : int * T list -> T
  val brk : int -> T
  val fbrk : T
  val str : string -> T
  val lst : string * string -> T list -> T
  val quote : T -> T
  val string_of : T -> string
  val str_of : T -> string
  val pprint : T -> pprint_args -> unit
  val setdepth: int -> unit
  val setmargin: int -> unit
  end;

functor PrettyFun () : PRETTY =
struct

(*Printing items: compound phrases, strings, and breaks*)
datatype T = Block of T list * int * int (*indentation, length*)
           | String of string
           | Break of bool*int   (*mandatory flag; width if not taken*);

(*Add the lengths of the expressions until the next Break; if no Break then
  include "after", to account for text following this block. *)
fun breakdist (Block(_,_,len)::es, after) = len + breakdist(es, after)
  | breakdist (String s :: es, after) = size s + breakdist (es, after)
  | breakdist (Break _ :: es, after) = 0
  | breakdist ([], after) = after;

fun repstring a 0 = ""
  | repstring a 1 = a
  | repstring a k =
      if k mod 2 = 0 then repstring(a^a) (k div 2)
                     else repstring(a^a) (k div 2) ^ a;

(*** Type for lines of text: string, # of lines, position on line ***)

type text = {tx: string, nl: int, pos: int};

val emptytext = {tx="", nl=0, pos=0};

fun blanks wd {tx,nl,pos} =
    {tx  = tx ^ repstring" "wd,
     nl  = nl,
     pos = pos+wd};

fun newline {tx,nl,pos} =
    {tx  = tx ^ "\n",
     nl  = nl+1,
     pos = 0};

fun string s {tx,nl,pos} =
    {tx  = tx ^ s,
     nl  = nl,
     pos = pos + size(s)};

(*** Formatting ***)

val margin      = ref 80        (*right margin, or page width*)
and breakgain   = ref 4         (*minimum added space required of a break*)
and emergencypos = ref 40;      (*position too far to right*)

fun setmargin m =
    (margin     := m;
     breakgain  := !margin div 20;
     emergencypos := !margin div 2);

fun forcenext [] = []
  | forcenext (Break(_,wd) :: es) = Break(true,0) :: es
  | forcenext (e :: es) = e :: forcenext es;

fun format ([], _, _) text = text
  | format (e::es, blockin, after) (text as {pos,nl,...}) =
    (case e of
       Block(bes,indent,wd) =>
         let val blockin' = (pos + indent) mod !emergencypos
             val btext = format(bes, blockin', breakdist(es,after)) text
             val es2 = if nl < #nl(btext) then forcenext es
                       else es
         in  format (es2,blockin,after) btext  end
     | String s => format (es,blockin,after) (string s text)
     | Break(force,wd) => (* no break if text fits on this line
                      or if breaking would add only breakgain to space *)
           format (es,blockin,after)
               (if not force andalso
                   pos+wd <= max[!margin - breakdist(es,after),
                                 blockin + !breakgain]
                then blanks wd text
                else blanks blockin (newline text)));

(*** Exported functions to create formatting expressions ***)

fun length (Block(_,_,len)) = len
  | length (String s) = size s
  | length (Break(_,wd)) = wd;

val str = String
and fbrk = Break(true,0);

fun brk wd = Break(false,wd);

fun blk (indent,es) =
  let fun sum([], k) = k
        | sum(e::es, k) = sum(es, length e + k)
  in  Block(es,indent, sum(es,0))  end;

fun lst(lp,rp) es =
  let fun add(e,es) = str"," :: brk 1 :: e :: es;
      fun list(e :: (es as _::_)) = str lp :: e :: foldr add (es,[str rp])
        | list(e::[]) = [str lp, e, str rp]
        | list([]) = []
  in blk(size lp, list es) end;

fun quote prt = blk (1, [str "\"", prt, str "\""]);


(*** Pretty printing with depth limitation ***)

val depth       = ref 0;        (*maximum depth; 0 means no limit*)

fun setdepth dp = (depth := dp);


fun pruning dp (Block(bes,indent,wd)) =
      if dp>0 then blk(indent, map (pruning(dp-1)) bes)
              else String"..."
  | pruning dp e = e;

fun prune dp e = if dp>0 then pruning dp e else e;


fun string_of e = #tx (format ([prune (!depth) e],0,0) emptytext);


fun brk_width (force, wd) = if force andalso wd = 0 then 1 else wd;

fun str_of prt =
  let
    fun s_of (Block (prts, _, _)) = implode (map s_of prts)
      | s_of (String s) = s
      | s_of (Break f_w) = repstring " " (brk_width f_w);
  in
    s_of (prune (! depth) prt)
  end;


fun pprint prt (put_str, begin_blk, put_brk, end_blk) =
  let
    fun pp (Block (prts, ind, _)) = (begin_blk ind; pp_lst prts; end_blk ())
      | pp (String s) = put_str s
      | pp (Break f_w) = put_brk (brk_width f_w)
    and pp_lst [] = ()
      | pp_lst (prt :: prts) = (pp prt; pp_lst prts);
  in
    pp (prune (! depth) prt)
  end;


(*** Initialization ***)

val () = setmargin 80;

end;

