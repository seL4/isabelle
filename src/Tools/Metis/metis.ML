(******************************************************************)
(* GENERATED FILE -- DO NOT EDIT -- GENERATED FILE -- DO NOT EDIT *)
(* GENERATED FILE -- DO NOT EDIT -- GENERATED FILE -- DO NOT EDIT *)
(* GENERATED FILE -- DO NOT EDIT -- GENERATED FILE -- DO NOT EDIT *)
(******************************************************************)

print_depth 0;

structure Metis = struct structure Word = Word structure Array = Array end;

(**** Original file: Portable.sig ****)

(* ========================================================================= *)
(* ML SPECIFIC FUNCTIONS                                                     *)
(* Copyright (c) 2001-2007 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Portable =
sig

(* ------------------------------------------------------------------------- *)
(* The ML implementation.                                                    *)
(* ------------------------------------------------------------------------- *)

val ml : string

(* ------------------------------------------------------------------------- *)
(* Pointer equality using the run-time system.                               *)
(* ------------------------------------------------------------------------- *)

val pointerEqual : 'a * 'a -> bool

(* ------------------------------------------------------------------------- *)
(* Timing function applications.                                             *)
(* ------------------------------------------------------------------------- *)

val time : ('a -> 'b) -> 'a -> 'b

(* ------------------------------------------------------------------------- *)
(* Critical section markup (multiprocessing)                                 *)
(* ------------------------------------------------------------------------- *)

val CRITICAL: (unit -> 'a) -> 'a

(* ------------------------------------------------------------------------- *)
(* Generating random values.                                                 *)
(* ------------------------------------------------------------------------- *)

val randomBool : unit -> bool

val randomInt : int -> int  (* n |-> [0,n) *)

val randomReal : unit -> real  (* () |-> [0,1] *)

val randomWord : unit -> Metis.Word.word

end

(**** Original file: PortableIsabelle.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* Isabelle ML SPECIFIC FUNCTIONS                                            *)
(* ========================================================================= *)

structure Portable :> Portable =
struct

(* ------------------------------------------------------------------------- *)
(* The ML implementation.                                                    *)
(* ------------------------------------------------------------------------- *)

val ml = ml_system;

(* ------------------------------------------------------------------------- *)
(* Pointer equality using the run-time system.                               *)
(* ------------------------------------------------------------------------- *)

val pointerEqual = pointer_eq;

(* ------------------------------------------------------------------------- *)
(* Timing function applications a la Mosml.time.                             *)
(* ------------------------------------------------------------------------- *)

val time = timeap;

(* ------------------------------------------------------------------------- *)
(* Critical section markup (multiprocessing)                                 *)
(* ------------------------------------------------------------------------- *)

fun CRITICAL e = NAMED_CRITICAL "metis" e;

(* ------------------------------------------------------------------------- *)
(* Generating random values.                                                 *)
(* ------------------------------------------------------------------------- *)

val randomWord = Random_Word.next_word;
val randomBool = Random_Word.next_bool;
fun randomInt n = Random_Word.next_int 0 (n - 1);
val randomReal = Random_Word.next_real;

end;

(* ------------------------------------------------------------------------- *)
(* Quotations a la Moscow ML.                                                *)
(* ------------------------------------------------------------------------- *)

datatype 'a frag = QUOTE of string | ANTIQUOTE of 'a;
end;

(**** Original file: PP.sig ****)

(* ========================================================================= *)
(* PP -- pretty-printing -- from the SML/NJ library                          *)
(*                                                                           *)
(* Modified for Moscow ML from SML/NJ Library version 0.2                    *)
(*                                                                           *)
(* COPYRIGHT (c) 1992 by AT&T Bell Laboratories.                             *)
(*                                                                           *)
(* STANDARD ML OF NEW JERSEY COPYRIGHT NOTICE, LICENSE AND DISCLAIMER.       *)
(*                                                                           *)
(* Permission to use, copy, modify, and distribute this software and its     *)
(* documentation for any purpose and without fee is hereby granted,          *)
(* provided that the above copyright notice appear in all copies and that    *)
(* both the copyright notice and this permission notice and warranty         *)
(* disclaimer appear in supporting documentation, and that the name of       *)
(* AT&T Bell Laboratories or any AT&T entity not be used in advertising      *)
(* or publicity pertaining to distribution of the software without           *)
(* specific, written prior permission.                                       *)
(*                                                                           *)
(* AT&T disclaims all warranties with regard to this software, including     *)
(* all implied warranties of merchantability and fitness.  In no event       *)
(* shall AT&T be liable for any special, indirect or consequential           *)
(* damages or any damages whatsoever resulting from loss of use, data or     *)
(* profits, whether in an action of contract, negligence or other            *)
(* tortious action, arising out of or in connection with the use or          *)
(* performance of this software.                                             *)
(* ========================================================================= *)

signature PP =
sig

  type ppstream

  type ppconsumer =
       {consumer : string -> unit,
        linewidth : int,
        flush : unit -> unit}

  datatype break_style = 
      CONSISTENT
    | INCONSISTENT

  val mk_ppstream : ppconsumer -> ppstream

  val dest_ppstream : ppstream -> ppconsumer

  val add_break : ppstream -> int * int -> unit

  val add_newline : ppstream -> unit

  val add_string : ppstream -> string -> unit

  val begin_block : ppstream -> break_style -> int -> unit

  val end_block : ppstream -> unit

  val clear_ppstream : ppstream -> unit

  val flush_ppstream : ppstream -> unit

  val with_pp : ppconsumer -> (ppstream -> unit) -> unit

  val pp_to_string : int -> (ppstream -> 'a -> unit) -> 'a -> string

end

(* 
   This structure provides tools for creating customized Oppen-style
   pretty-printers, based on the type ppstream.  A ppstream is an
   output stream that contains prettyprinting commands.  The commands
   are placed in the stream by various function calls listed below.

   There following primitives add commands to the stream:
   begin_block, end_block, add_string, add_break, and add_newline.
   All calls to add_string, add_break, and add_newline must happen
   between a pair of calls to begin_block and end_block must be
   properly nested dynamically.  All calls to begin_block and
   end_block must be properly nested (dynamically).

   [ppconsumer] is the type of sinks for pretty-printing.  A value of 
   type ppconsumer is a record 
                 { consumer : string -> unit,
                   linewidth : int,
                   flush : unit -> unit }
   of a string consumer, a specified linewidth, and a flush function
   which is called whenever flush_ppstream is called.

   A prettyprinter can be called outright to print a value.  In
   addition, a prettyprinter for a base type or nullary datatype ty
   can be installed in the top-level system.  Then the installed
   prettyprinter will be invoked automatically whenever a value of
   type ty is to be printed.

   [break_style] is the type of line break styles for blocks:

   [CONSISTENT] specifies that if any line break occurs inside the
   block, then all indicated line breaks occur.

   [INCONSISTENT] specifies that breaks will be inserted to only to
   avoid overfull lines.

   [mk_ppstream {consumer, linewidth, flush}] creates a new ppstream
   which invokes the consumer to output text, putting at most
   linewidth characters on each line.

   [dest_ppstream ppstrm] extracts the linewidth, flush function, and
   consumer from a ppstream.

   [add_break ppstrm (size, offset)] notifies the pretty-printer that
   a line break is possible at this point.  
   * When the current block style is CONSISTENT:
      ** if the entire block fits on the remainder of the line, then
         output size spaces; else
      ** increase the current indentation by the block offset;
         further indent every item of the block by offset, and add
         one newline at every add_break in the block.
   * When the current block style is INCONSISTENT:
      ** if the next component of the block fits on the remainder of
         the line, then output size spaces; else
      ** issue a newline and indent to the current indentation level
         plus the block offset plus the offset.

   [add_newline ppstrm] issues a newline.

   [add_string ppstrm str] outputs the string str to the ppstream.

   [begin_block ppstrm style blockoffset] begins a new block and
   level of indentation, with the given style and block offset.

   [end_block ppstrm] closes the current block.  

   [clear_ppstream ppstrm] restarts the stream, without affecting the
   underlying consumer.

   [flush_ppstream ppstrm] executes any remaining commands in the
   ppstream (that is, flushes currently accumulated output to the
   consumer associated with ppstrm); executes the flush function
   associated with the consumer; and calls clear_ppstream.

   [with_pp consumer f] makes a new ppstream from the consumer and
   applies f (which can be thought of as a producer) to that
   ppstream, then flushed the ppstream and returns the value of f.

   [pp_to_string linewidth printit x] constructs a new ppstream
   ppstrm whose consumer accumulates the output in a string s.  Then
   evaluates (printit ppstrm x) and finally returns the string s.


   Example 1: A simple prettyprinter for Booleans:

       load "PP";
       fun ppbool pps d = 
           let open PP
           in
               begin_block pps INCONSISTENT 6; 
               add_string pps (if d then "right" else "wrong");
               end_block pps
           end;

   Now one may define a ppstream to print to, and exercise it:

       val ppstrm = Metis.PP.mk_ppstream {consumer  = 
                                    fn s => Metis.TextIO.output(Metis.TextIO.stdOut, s), 
                                    linewidth = 72,
                                    flush     = 
                                     fn () => Metis.TextIO.flushOut Metis.TextIO.stdOut};

       fun ppb b = (ppbool ppstrm b; Metis.PP.flush_ppstream ppstrm);

       - ppb false;
       wrong> val it = () : unit   

   The prettyprinter may also be installed in the toplevel system;
   then it will be used to print all expressions of type bool
   subsequently computed:

       - installPP ppbool;
       > val it = () : unit
       - 1=0;
       > val it = wrong : bool
       - 1=1;
       > val it = right : bool

   See library Meta for a description of installPP.


   Example 2: Prettyprinting simple expressions (examples/pretty/Metis.ppexpr.sml):

       datatype expr = 
           Cst of int 
         | Neg of expr
         | Plus of expr * expr

       fun ppexpr pps e0 = 
           let open PP
               fun ppe (Cst i)        = add_string pps (Metis.Int.toString i)
                 | ppe (Neg e)        = (add_string pps "~"; ppe e)
                 | ppe (Plus(e1, e2)) = (begin_block pps CONSISTENT 0;
                                         add_string pps "(";
                                         ppe e1; 
                                         add_string pps " + ";
                                         add_break pps (0, 1);
                                         ppe e2; 
                                         add_string pps ")";
                                         end_block pps)
           in
               begin_block pps INCONSISTENT 0; 
               ppe e0;
               end_block pps
           end

       val _ = installPP ppexpr;

       (* Some example values: *)

       val e1 = Cst 1;
       val e2 = Cst 2;
       val e3 = Plus(e1, Neg e2);
       val e4 = Plus(Neg e3, e3);
       val e5 = Plus(Neg e4, e4);
       val e6 = Plus(e5, e5);
       val e7 = Plus(e6, e6);
       val e8 = 
           Plus(e3, Plus(e3, Plus(e3, Plus(e3, Plus(e3, Plus(e3, e7))))));
*)

(**** Original file: PP.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* PP -- pretty-printing -- from the SML/NJ library                          *)
(*                                                                           *)
(* Modified for Moscow ML from SML/NJ Library version 0.2                    *)
(*                                                                           *)
(* COPYRIGHT (c) 1992 by AT&T Bell Laboratories.                             *)
(*                                                                           *)
(* STANDARD ML OF NEW JERSEY COPYRIGHT NOTICE, LICENSE AND DISCLAIMER.       *)
(*                                                                           *)
(* Permission to use, copy, modify, and distribute this software and its     *)
(* documentation for any purpose and without fee is hereby granted,          *)
(* provided that the above copyright notice appear in all copies and that    *)
(* both the copyright notice and this permission notice and warranty         *)
(* disclaimer appear in supporting documentation, and that the name of       *)
(* AT&T Bell Laboratories or any AT&T entity not be used in advertising      *)
(* or publicity pertaining to distribution of the software without           *)
(* specific, written prior permission.                                       *)
(*                                                                           *)
(* AT&T disclaims all warranties with regard to this software, including     *)
(* all implied warranties of merchantability and fitness.  In no event       *)
(* shall AT&T be liable for any special, indirect or consequential           *)
(* damages or any damages whatsoever resulting from loss of use, data or     *)
(* profits, whether in an action of contract, negligence or other            *)
(* tortious action, arising out of or in connection with the use or          *)
(* performance of this software.                                             *)
(* ========================================================================= *)

structure PP :> PP =
struct

open Array 
infix 9 sub

(* the queue library, formerly in unit Ppqueue *)

datatype Qend = Qback | Qfront

exception QUEUE_FULL
exception QUEUE_EMPTY
exception REQUESTED_QUEUE_SIZE_TOO_SMALL

local 
    fun ++ i n = (i + 1) mod n
    fun -- i n = (i - 1) mod n
in

abstype 'a queue = QUEUE of {elems: 'a array, (* the contents *)
                             front: int Unsynchronized.ref,
                             back: int Unsynchronized.ref,
                             size: int}  (* fixed size of element array *)
with

  fun is_empty (QUEUE{front=Unsynchronized.ref ~1, back=Unsynchronized.ref ~1,...}) = true
    | is_empty _ = false

  fun mk_queue n init_val =
      if (n < 2)
      then raise REQUESTED_QUEUE_SIZE_TOO_SMALL
      else QUEUE{elems=array(n, init_val), front=Unsynchronized.ref ~1, back=Unsynchronized.ref ~1, size=n}

  fun clear_queue (QUEUE{front,back,...}) = (front := ~1; back := ~1)

  fun queue_at Qfront (QUEUE{elems,front,...}) = elems sub !front
    | queue_at Qback (QUEUE{elems,back,...}) = elems sub !back

  fun en_queue Qfront item (Q as QUEUE{elems,front,back,size}) =
        if (is_empty Q)
        then (front := 0; back := 0;
              update(elems,0,item))
        else let val i = --(!front) size
             in  if (i = !back)
                 then raise QUEUE_FULL
                 else (update(elems,i,item); front := i)
             end
    | en_queue Qback item (Q as QUEUE{elems,front,back,size}) =
        if (is_empty Q)
        then (front := 0; back := 0;
              update(elems,0,item))
        else let val i = ++(!back) size
             in  if (i = !front)
                 then raise QUEUE_FULL
                 else (update(elems,i,item); back := i)
             end

  fun de_queue Qfront (Q as QUEUE{front,back,size,...}) =
        if (!front = !back) (* unitary queue *)
        then clear_queue Q
        else front := ++(!front) size
    | de_queue Qback (Q as QUEUE{front,back,size,...}) =
        if (!front = !back)
        then clear_queue Q
        else back := --(!back) size

end (* abstype queue *)
end (* local   *)


val magic: 'a -> 'a = fn x => x

(* exception PP_FAIL of string *)

datatype break_style = CONSISTENT | INCONSISTENT

datatype break_info
  = FITS
  | PACK_ONTO_LINE of int
  | ONE_PER_LINE of int

(* Some global values *)
val INFINITY = 999999

abstype indent_stack = Istack of break_info list Unsynchronized.ref
with
  fun mk_indent_stack() = Istack (Unsynchronized.ref([]:break_info list))
  fun clear_indent_stack (Istack stk) = (stk := ([]:break_info list))
  fun top (Istack stk) =
      case !stk
        of nil => raise Fail "PP-error: top: badly formed block"
	 | x::_ => x
  fun push (x,(Istack stk)) = stk := x::(!stk)
  fun pop (Istack stk) =
      case !stk
        of nil => raise Fail "PP-error: pop: badly formed block"
	 | _::rest => stk := rest
end

(* The delim_stack is used to compute the size of blocks. It is
   a stack of indices into the token buffer. The indices only point to
   BBs, Es, and BRs. We push BBs and Es onto the stack until a BR
   is encountered. Then we compute sizes and pop. When we encounter
   a BR in the middle of a block, we compute the Distance_to_next_break
   of the previous BR in the block, if there was one.

   We need to be able to delete from the bottom of the delim_stack, so
   we use a queue, treated with a stack discipline, i.e., we only add
   items at the head of the queue, but can delete from the front or
   back of the queue.
*)
abstype delim_stack = Dstack of int queue
with
  fun new_delim_stack i = Dstack(mk_queue i ~1)
  fun reset_delim_stack (Dstack q) = clear_queue q

  fun pop_delim_stack (Dstack d) = de_queue Qfront d
  fun pop_bottom_delim_stack (Dstack d) = de_queue Qback d

  fun push_delim_stack(i,Dstack d) = en_queue Qfront i d
  fun top_delim_stack (Dstack d) = queue_at Qfront d
  fun bottom_delim_stack (Dstack d) = queue_at Qback d
  fun delim_stack_is_empty (Dstack d) = is_empty d
end


type block_info = { Block_size : int Unsynchronized.ref,
                    Block_offset : int,
                    How_to_indent : break_style }


(* Distance_to_next_break includes Number_of_blanks. Break_offset is
   a local offset for the break. BB represents a sequence of contiguous
   Begins. E represents a sequence of contiguous Ends.
*)
datatype pp_token
  = S of  {String : string, Length : int}
  | BB of {Pblocks : block_info list Unsynchronized.ref,   (* Processed   *)
           Ublocks : block_info list Unsynchronized.ref}  (* Unprocessed *)
  | E of  {Pend : int Unsynchronized.ref, Uend : int Unsynchronized.ref}
  | BR of {Distance_to_next_break : int Unsynchronized.ref,
           Number_of_blanks : int,
           Break_offset : int}


(* The initial values in the token buffer *)
val initial_token_value = S{String = "", Length = 0}

(* type ppstream = General.ppstream; *)
datatype ppstream_ =
  PPS of
     {consumer : string -> unit,
      linewidth : int,
      flush : unit -> unit,
      the_token_buffer : pp_token array,
      the_delim_stack : delim_stack,
      the_indent_stack : indent_stack,
      ++ : int Unsynchronized.ref -> unit,    (* increment circular buffer index *)
      space_left : int Unsynchronized.ref,    (* remaining columns on page *)
      left_index : int Unsynchronized.ref,    (* insertion index *)
      right_index : int Unsynchronized.ref,   (* output index *)
      left_sum : int Unsynchronized.ref,      (* size of strings and spaces inserted *)
      right_sum : int Unsynchronized.ref}     (* size of strings and spaces printed *)

type ppstream = ppstream_

type ppconsumer = {consumer : string -> unit,
		   linewidth : int,
		   flush : unit -> unit}

fun mk_ppstream {consumer,linewidth,flush} =
    if (linewidth<5)
    then raise Fail "PP-error: linewidth too_small"
    else let val buf_size = 3*linewidth
          in magic(
             PPS{consumer = consumer,
		 linewidth = linewidth,
		 flush = flush,
		 the_token_buffer = array(buf_size, initial_token_value),
		 the_delim_stack = new_delim_stack buf_size,
		 the_indent_stack = mk_indent_stack (),
		 ++ = fn i => i := ((!i + 1) mod buf_size),
		 space_left = Unsynchronized.ref linewidth,
		 left_index = Unsynchronized.ref 0, right_index = Unsynchronized.ref 0,
		 left_sum = Unsynchronized.ref 0, right_sum = Unsynchronized.ref 0}
                 ) : ppstream
	 end

fun dest_ppstream(pps : ppstream) =
  let val PPS{consumer,linewidth,flush, ...} = magic pps
  in {consumer=consumer,linewidth=linewidth,flush=flush} end

local
  val space = " "
  fun mk_space (0,s) = String.concat s
    | mk_space (n,s) = mk_space((n-1), (space::s))
  val space_table = Vector.tabulate(100, fn i => mk_space(i,[]))
  fun nspaces n = Vector.sub(space_table, n)
      handle General.Subscript =>
	if n < 0
	then ""
	else let val n2 = n div 2
		 val n2_spaces = nspaces n2
		 val extra = if (n = (2*n2)) then "" else space
              in String.concat [n2_spaces, n2_spaces, extra]
	     end
in
  fun cr_indent (ofn, i) = ofn ("\n"^(nspaces i))
  fun indent (ofn,i) = ofn (nspaces i)
end


(* Print a the first member of a contiguous sequence of Begins. If there
   are "processed" Begins, then take the first off the list. If there are
   no processed Begins, take the last member off the "unprocessed" list.
   This works because the unprocessed list is treated as a stack, the
   processed list as a FIFO queue. How can an item on the unprocessed list
   be printable? Because of what goes on in add_string. See there for details.
*)

fun print_BB (_,{Pblocks = Unsynchronized.ref [], Ublocks = Unsynchronized.ref []}) =
             raise Fail "PP-error: print_BB"
  | print_BB (PPS{the_indent_stack,linewidth,space_left=Unsynchronized.ref sp_left,...},
             {Pblocks as Unsynchronized.ref({How_to_indent=CONSISTENT,Block_size,
                              Block_offset}::rst),
              Ublocks=Unsynchronized.ref[]}) =
       (push ((if (!Block_size > sp_left)
               then ONE_PER_LINE (linewidth - (sp_left - Block_offset))
               else FITS),
	      the_indent_stack);
        Pblocks := rst)
  | print_BB(PPS{the_indent_stack,linewidth,space_left=Unsynchronized.ref sp_left,...},
             {Pblocks as Unsynchronized.ref({Block_size,Block_offset,...}::rst),Ublocks=Unsynchronized.ref[]}) =
       (push ((if (!Block_size > sp_left)
               then PACK_ONTO_LINE (linewidth - (sp_left - Block_offset))
               else FITS),
	      the_indent_stack);
        Pblocks := rst)
  | print_BB (PPS{the_indent_stack, linewidth, space_left=Unsynchronized.ref sp_left,...},
              {Ublocks,...}) =
      let fun pr_end_Ublock [{How_to_indent=CONSISTENT,Block_size,Block_offset}] l =
		(push ((if (!Block_size > sp_left)
			then ONE_PER_LINE (linewidth - (sp_left - Block_offset))
			else FITS),
		       the_indent_stack);
                 List.rev l)
	    | pr_end_Ublock [{Block_size,Block_offset,...}] l =
		(push ((if (!Block_size > sp_left)
			then PACK_ONTO_LINE (linewidth - (sp_left - Block_offset))
			else FITS),
		       the_indent_stack);
                 List.rev l)
	    | pr_end_Ublock (a::rst) l = pr_end_Ublock rst (a::l)
            | pr_end_Ublock _ _ =
                raise Fail "PP-error: print_BB: internal error"
       in Ublocks := pr_end_Ublock(!Ublocks) []
      end


(* Uend should always be 0 when print_E is called. *)
fun print_E (_,{Pend = Unsynchronized.ref 0, Uend = Unsynchronized.ref 0}) =
      raise Fail "PP-error: print_E"
  | print_E (istack,{Pend, ...}) =
      let fun pop_n_times 0 = ()
	    | pop_n_times n = (pop istack; pop_n_times(n-1))
       in pop_n_times(!Pend); Pend := 0
      end


(* "cursor" is how many spaces across the page we are. *)

fun print_token(PPS{consumer,space_left,...}, S{String,Length}) =
      (consumer String;
       space_left := (!space_left) - Length)
  | print_token(ppstrm,BB b) = print_BB(ppstrm,b)
  | print_token(PPS{the_indent_stack,...},E e) =
      print_E (the_indent_stack,e)
  | print_token (PPS{the_indent_stack,space_left,consumer,linewidth,...},
                 BR{Distance_to_next_break,Number_of_blanks,Break_offset}) =
     (case (top the_indent_stack)
        of FITS =>
	     (space_left := (!space_left) - Number_of_blanks;
              indent (consumer,Number_of_blanks))
         | (ONE_PER_LINE cursor) =>
             let val new_cursor = cursor + Break_offset
              in space_left := linewidth - new_cursor;
                 cr_indent (consumer,new_cursor)
	     end
         | (PACK_ONTO_LINE cursor) =>
	     if (!Distance_to_next_break > (!space_left))
	     then let val new_cursor = cursor + Break_offset
		   in space_left := linewidth - new_cursor;
		      cr_indent(consumer,new_cursor)
		  end
	     else (space_left := !space_left - Number_of_blanks;
		   indent (consumer,Number_of_blanks)))


fun clear_ppstream(pps : ppstream) =
    let val PPS{the_token_buffer, the_delim_stack,
                the_indent_stack,left_sum, right_sum,
                left_index, right_index,space_left,linewidth,...}
              = magic pps
        val buf_size = 3*linewidth
	fun set i =
	    if (i = buf_size)
	    then ()
	    else (update(the_token_buffer,i,initial_token_value);
		  set (i+1))
     in set 0;
	clear_indent_stack the_indent_stack;
	reset_delim_stack the_delim_stack;
	left_sum := 0; right_sum := 0;
	left_index := 0; right_index := 0;
	space_left := linewidth
    end


(* Move insertion head to right unless adding a BB and already at a BB,
   or unless adding an E and already at an E.
*)
fun BB_inc_right_index(PPS{the_token_buffer, right_index, ++,...})=
    case (the_token_buffer sub (!right_index))
      of (BB _) => ()
       | _ => ++right_index

fun E_inc_right_index(PPS{the_token_buffer,right_index, ++,...})=
    case (the_token_buffer sub (!right_index))
      of (E _) => ()
       | _ => ++right_index


fun pointers_coincide(PPS{left_index,right_index,the_token_buffer,...}) =
    (!left_index = !right_index) andalso
    (case (the_token_buffer sub (!left_index))
       of (BB {Pblocks = Unsynchronized.ref [], Ublocks = Unsynchronized.ref []}) => true
	| (BB _) => false
	| (E {Pend = Unsynchronized.ref 0, Uend = Unsynchronized.ref 0}) => true
	| (E _) => false
	| _ => true)

fun advance_left (ppstrm as PPS{consumer,left_index,left_sum,
                                the_token_buffer,++,...},
                  instr) =
    let val NEG = ~1
	val POS = 0
	fun inc_left_sum (BR{Number_of_blanks, ...}) =
		 left_sum := (!left_sum) + Number_of_blanks
	  | inc_left_sum (S{Length, ...}) = left_sum := (!left_sum) + Length
	  | inc_left_sum _ = ()

	fun last_size [{Block_size, ...}:block_info] = !Block_size
	  | last_size (_::rst) = last_size rst
          | last_size _ = raise Fail "PP-error: last_size: internal error"
	fun token_size (S{Length, ...}) = Length
	  | token_size (BB b) =
	     (case b
                of {Pblocks = Unsynchronized.ref [], Ublocks = Unsynchronized.ref []} =>
                     raise Fail "PP-error: BB_size"
	         | {Pblocks as Unsynchronized.ref(_::_),Ublocks=Unsynchronized.ref[]} => POS
		 | {Ublocks, ...} => last_size (!Ublocks))
	  | token_size (E{Pend = Unsynchronized.ref 0, Uend = Unsynchronized.ref 0}) =
              raise Fail "PP-error: token_size.E"
	  | token_size (E{Pend = Unsynchronized.ref 0, ...}) = NEG
	  | token_size (E _) = POS
	  | token_size (BR {Distance_to_next_break, ...}) = !Distance_to_next_break
	fun loop (instr) =
	    if (token_size instr < 0)  (* synchronization point; cannot advance *)
	    then ()
	    else (print_token(ppstrm,instr);
		  inc_left_sum instr;
		  if (pointers_coincide ppstrm)
		  then ()
		  else (* increment left index *)

    (* When this is evaluated, we know that the left_index has not yet
       caught up to the right_index. If we are at a BB or an E, we can
       increment left_index if there is no work to be done, i.e., all Begins
       or Ends have been dealt with. Also, we should do some housekeeping and
       clear the buffer at left_index, otherwise we can get errors when
       left_index catches up to right_index and we reset the indices to 0.
       (We might find ourselves adding a BB to an "old" BB, with the result
       that the index is not pushed onto the delim_stack. This can lead to
       mangled output.)
    *)
		       (case (the_token_buffer sub (!left_index))
			  of (BB {Pblocks = Unsynchronized.ref [], Ublocks = Unsynchronized.ref []}) =>
			       (update(the_token_buffer,!left_index,
				       initial_token_value);
				++left_index)
			   | (BB _) => ()
			   | (E {Pend = Unsynchronized.ref 0, Uend = Unsynchronized.ref 0}) =>
			       (update(the_token_buffer,!left_index,
				       initial_token_value);
				++left_index)
			   | (E _) => ()
			   | _ => ++left_index;
			loop (the_token_buffer sub (!left_index))))
     in loop instr
    end


fun begin_block (pps : ppstream) style offset =
  let val ppstrm = magic pps : ppstream_
      val PPS{the_token_buffer, the_delim_stack,left_index,
              left_sum, right_index, right_sum,...}
            = ppstrm
  in
   (if (delim_stack_is_empty the_delim_stack)
    then (left_index := 0;
	  left_sum := 1;
	  right_index := 0;
	  right_sum := 1)
    else BB_inc_right_index ppstrm;
    case (the_token_buffer sub (!right_index))
      of (BB {Ublocks, ...}) =>
	   Ublocks := {Block_size = Unsynchronized.ref (~(!right_sum)),
		       Block_offset = offset,
		       How_to_indent = style}::(!Ublocks)
       | _ => (update(the_token_buffer, !right_index,
		      BB{Pblocks = Unsynchronized.ref [],
			 Ublocks = Unsynchronized.ref [{Block_size = Unsynchronized.ref (~(!right_sum)),
					 Block_offset = offset,
					 How_to_indent = style}]});
	       push_delim_stack (!right_index, the_delim_stack)))
  end

fun end_block(pps : ppstream) =
  let val ppstrm = magic pps : ppstream_
      val PPS{the_token_buffer,the_delim_stack,right_index,...}
            = ppstrm
  in
    if (delim_stack_is_empty the_delim_stack)
    then print_token(ppstrm,(E{Pend = Unsynchronized.ref 1, Uend = Unsynchronized.ref 0}))
    else (E_inc_right_index ppstrm;
	  case (the_token_buffer sub (!right_index))
            of (E{Uend, ...}) => Uend := !Uend + 1
	     | _ => (update(the_token_buffer,!right_index,
			    E{Uend = Unsynchronized.ref 1, Pend = Unsynchronized.ref 0});
		     push_delim_stack (!right_index, the_delim_stack)))
  end

local
  fun check_delim_stack(PPS{the_token_buffer,the_delim_stack,right_sum,...}) =
      let fun check k =
	      if (delim_stack_is_empty the_delim_stack)
	      then ()
	      else case(the_token_buffer sub (top_delim_stack the_delim_stack))
		     of (BB{Ublocks as Unsynchronized.ref ((b as {Block_size, ...})::rst),
			    Pblocks}) =>
			   if (k>0)
			   then (Block_size := !right_sum + !Block_size;
				 Pblocks := b :: (!Pblocks);
				 Ublocks := rst;
				 if (List.length rst = 0)
				 then pop_delim_stack the_delim_stack
				 else ();
				 check(k-1))
			   else ()
		      | (E{Pend,Uend}) =>
			   (Pend := (!Pend) + (!Uend);
			    Uend := 0;
			    pop_delim_stack the_delim_stack;
			    check(k + !Pend))
		      | (BR{Distance_to_next_break, ...}) =>
			   (Distance_to_next_break :=
			      !right_sum + !Distance_to_next_break;
			    pop_delim_stack the_delim_stack;
			    if (k>0)
			    then check k
			    else ())
                      | _ => raise Fail "PP-error: check_delim_stack.catchall"
       in check 0
      end
in

  fun add_break (pps : ppstream) (n, break_offset) =
    let val ppstrm = magic pps : ppstream_
        val PPS{the_token_buffer,the_delim_stack,left_index,
                right_index,left_sum,right_sum, ++, ...}
              = ppstrm
    in
      (if (delim_stack_is_empty the_delim_stack)
       then (left_index := 0; right_index := 0;
	     left_sum := 1;   right_sum := 1)
       else ++right_index;
       update(the_token_buffer, !right_index,
	      BR{Distance_to_next_break = Unsynchronized.ref (~(!right_sum)),
		 Number_of_blanks = n,
		 Break_offset = break_offset});
       check_delim_stack ppstrm;
       right_sum := (!right_sum) + n;
       push_delim_stack (!right_index,the_delim_stack))
    end

  fun flush_ppstream0(pps : ppstream) =
    let val ppstrm = magic pps : ppstream_
        val PPS{the_delim_stack,the_token_buffer, flush, left_index,...}
              = ppstrm
    in
      (if (delim_stack_is_empty the_delim_stack)
       then ()
       else (check_delim_stack ppstrm;
	     advance_left(ppstrm, the_token_buffer sub (!left_index)));
       flush())
    end

end (* local *)


fun flush_ppstream ppstrm =
    (flush_ppstream0 ppstrm;
     clear_ppstream ppstrm)

fun add_string (pps : ppstream) s =
    let val ppstrm = magic pps : ppstream_
        val PPS{the_token_buffer,the_delim_stack,consumer,
                right_index,right_sum,left_sum,
                left_index,space_left,++,...}
              = ppstrm
        fun fnl [{Block_size, ...}:block_info] = Block_size := INFINITY
	  | fnl (_::rst) = fnl rst
          | fnl _ = raise Fail "PP-error: fnl: internal error"

	fun set(dstack,BB{Ublocks as Unsynchronized.ref[{Block_size,...}:block_info],...}) =
	      (pop_bottom_delim_stack dstack;
	       Block_size := INFINITY)
	  | set (_,BB {Ublocks = Unsynchronized.ref(_::rst), ...}) = fnl rst
	  | set (dstack, E{Pend,Uend}) =
	      (Pend := (!Pend) + (!Uend);
	       Uend := 0;
	       pop_bottom_delim_stack dstack)
	  | set (dstack,BR{Distance_to_next_break,...}) =
	      (pop_bottom_delim_stack dstack;
	       Distance_to_next_break := INFINITY)
          | set _ = raise (Fail "PP-error: add_string.set")

	fun check_stream () =
	    if ((!right_sum - !left_sum) > !space_left)
	    then if (delim_stack_is_empty the_delim_stack)
		 then ()
		 else let val i = bottom_delim_stack the_delim_stack
		       in if (!left_index = i)
			  then set (the_delim_stack, the_token_buffer sub i)
			  else ();
			  advance_left(ppstrm,
                                       the_token_buffer sub (!left_index));
		          if (pointers_coincide ppstrm)
		          then ()
		          else check_stream ()
		      end
	    else ()

	val slen = String.size s
	val S_token = S{String = s, Length = slen}

    in if (delim_stack_is_empty the_delim_stack)
       then print_token(ppstrm,S_token)
       else (++right_index;
             update(the_token_buffer, !right_index, S_token);
             right_sum := (!right_sum)+slen;
             check_stream ())
   end


(* Derived form. The +2 is for peace of mind *)
fun add_newline (pps : ppstream) =
  let val PPS{linewidth, ...} = magic pps
  in add_break pps (linewidth+2,0) end

(* Derived form. Builds a ppstream, sends pretty printing commands called in
   f to the ppstream, then flushes ppstream.
*)

fun with_pp ppconsumer ppfn =
   let val ppstrm = mk_ppstream ppconsumer
    in ppfn ppstrm;
       flush_ppstream0 ppstrm
   end
   handle Fail msg =>
     (TextIO.print (">>>> Pretty-printer failure: " ^ msg ^ "\n"))

fun pp_to_string linewidth ppfn ob =
    let val l = Unsynchronized.ref ([]:string list)
	fun attach s = l := (s::(!l))
     in with_pp {consumer = attach, linewidth=linewidth, flush = fn()=>()}
		(fn ppstrm =>  ppfn ppstrm ob);
	String.concat(List.rev(!l))
    end
end
end;

(**** Original file: Useful.sig ****)

(* ========================================================================= *)
(* ML UTILITY FUNCTIONS                                                      *)
(* Copyright (c) 2001-2005 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Useful =
sig

(* ------------------------------------------------------------------------- *)
(* Exceptions.                                                               *)
(* ------------------------------------------------------------------------- *)

exception Error of string

exception Bug of string

val partial : exn -> ('a -> 'b option) -> 'a -> 'b

val total : ('a -> 'b) -> 'a -> 'b option

val can : ('a -> 'b) -> 'a -> bool

(* ------------------------------------------------------------------------- *)
(* Tracing.                                                                  *)
(* ------------------------------------------------------------------------- *)

val tracePrint : (string -> unit) Unsynchronized.ref

val trace : string -> unit

(* ------------------------------------------------------------------------- *)
(* Combinators.                                                              *)
(* ------------------------------------------------------------------------- *)

val C : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c

val I : 'a -> 'a

val K : 'a -> 'b -> 'a

val S : ('a -> 'b -> 'c) -> ('a -> 'b) -> 'a -> 'c

val W : ('a -> 'a -> 'b) -> 'a -> 'b

val funpow : int -> ('a -> 'a) -> 'a -> 'a

val exp : ('a * 'a -> 'a) -> 'a -> int -> 'a -> 'a

val equal : ''a -> ''a -> bool

val notEqual : ''a -> ''a -> bool

(* ------------------------------------------------------------------------- *)
(* Pairs.                                                                    *)
(* ------------------------------------------------------------------------- *)

val fst : 'a * 'b -> 'a

val snd : 'a * 'b -> 'b

val pair : 'a -> 'b -> 'a * 'b

val swap : 'a * 'b -> 'b * 'a

val curry : ('a * 'b -> 'c) -> 'a -> 'b -> 'c

val uncurry : ('a -> 'b -> 'c) -> 'a * 'b -> 'c

val ## : ('a -> 'c) * ('b -> 'd) -> 'a * 'b -> 'c * 'd

(* ------------------------------------------------------------------------- *)
(* State transformers.                                                       *)
(* ------------------------------------------------------------------------- *)

val unit : 'a -> 's -> 'a * 's

val bind : ('s -> 'a * 's) -> ('a -> 's -> 'b * 's) -> 's -> 'b * 's

val mmap : ('a -> 'b) -> ('s -> 'a * 's) -> 's -> 'b * 's

val mjoin : ('s -> ('s -> 'a * 's) * 's) -> 's -> 'a * 's

val mwhile : ('a -> bool) -> ('a -> 's -> 'a * 's) -> 'a -> 's -> 'a * 's

(* ------------------------------------------------------------------------- *)
(* Lists: note we count elements from 0.                                     *)
(* ------------------------------------------------------------------------- *)

val cons : 'a -> 'a list -> 'a list

val hdTl : 'a list -> 'a * 'a list

val append : 'a list -> 'a list -> 'a list

val singleton : 'a -> 'a list

val first : ('a -> 'b option) -> 'a list -> 'b option

val index : ('a -> bool) -> 'a list -> int option

val maps : ('a -> 's -> 'b * 's) -> 'a list -> 's -> 'b list * 's

val mapsPartial : ('a -> 's -> 'b option * 's) -> 'a list -> 's -> 'b list * 's

val enumerate : 'a list -> (int * 'a) list

val zipwith : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list

val zip : 'a list -> 'b list -> ('a * 'b) list

val unzip : ('a * 'b) list -> 'a list * 'b list

val cartwith : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list

val cart : 'a list -> 'b list -> ('a * 'b) list

val divide : 'a list -> int -> 'a list * 'a list  (* Subscript *)

val revDivide : 'a list -> int -> 'a list * 'a list  (* Subscript *)

val updateNth : int * 'a -> 'a list -> 'a list  (* Subscript *)

val deleteNth : int -> 'a list -> 'a list  (* Subscript *)

(* ------------------------------------------------------------------------- *)
(* Sets implemented with lists.                                              *)
(* ------------------------------------------------------------------------- *)

val mem : ''a -> ''a list -> bool

val insert : ''a -> ''a list -> ''a list

val delete : ''a -> ''a list -> ''a list

val setify : ''a list -> ''a list  (* removes duplicates *)

val union : ''a list -> ''a list -> ''a list

val intersect : ''a list -> ''a list -> ''a list

val difference : ''a list -> ''a list -> ''a list

val subset : ''a list -> ''a list -> bool

val distinct : ''a list -> bool

(* ------------------------------------------------------------------------- *)
(* Comparisons.                                                              *)
(* ------------------------------------------------------------------------- *)

val mapCompare : ('a -> 'b) -> ('b * 'b -> order) -> 'a * 'a -> order

val revCompare : ('a * 'a -> order) -> 'a * 'a -> order

val prodCompare :
    ('a * 'a -> order) -> ('b * 'b -> order) -> ('a * 'b) * ('a * 'b) -> order

val lexCompare : ('a * 'a -> order) -> 'a list * 'a list -> order

val optionCompare : ('a * 'a -> order) -> 'a option * 'a option -> order

val boolCompare : bool * bool -> order  (* true < false *)

(* ------------------------------------------------------------------------- *)
(* Sorting and searching.                                                    *)
(* ------------------------------------------------------------------------- *)

val minimum : ('a * 'a -> order) -> 'a list -> 'a * 'a list  (* Empty *)

val maximum : ('a * 'a -> order) -> 'a list -> 'a * 'a list  (* Empty *)

val merge : ('a * 'a -> order) -> 'a list -> 'a list -> 'a list

val sort : ('a * 'a -> order) -> 'a list -> 'a list

val sortMap : ('a -> 'b) -> ('b * 'b -> order) -> 'a list -> 'a list

(* ------------------------------------------------------------------------- *)
(* Integers.                                                                 *)
(* ------------------------------------------------------------------------- *)

val interval : int -> int -> int list

val divides : int -> int -> bool

val gcd : int -> int -> int

val primes : int -> int list

val primesUpTo : int -> int list

(* ------------------------------------------------------------------------- *)
(* Strings.                                                                  *)
(* ------------------------------------------------------------------------- *)

val rot : int -> char -> char

val charToInt : char -> int option

val charFromInt : int -> char option

val nChars : char -> int -> string

val chomp : string -> string

val trim : string -> string

val join : string -> string list -> string

val split : string -> string -> string list

val mkPrefix : string -> string -> string

val destPrefix : string -> string -> string

val isPrefix : string -> string -> bool

(* ------------------------------------------------------------------------- *)
(* Tables.                                                                   *)
(* ------------------------------------------------------------------------- *)

type columnAlignment = {leftAlign : bool, padChar : char}

val alignColumn : columnAlignment -> string list -> string list -> string list

val alignTable : columnAlignment list -> string list list -> string list

(* ------------------------------------------------------------------------- *)
(* Reals.                                                                    *)
(* ------------------------------------------------------------------------- *)

val percentToString : real -> string

val pos : real -> real

val log2 : real -> real  (* Domain *)

(* ------------------------------------------------------------------------- *)
(* Sum datatype.                                                             *)
(* ------------------------------------------------------------------------- *)

datatype ('a,'b) sum = Left of 'a | Right of 'b

val destLeft : ('a,'b) sum -> 'a

val isLeft : ('a,'b) sum -> bool

val destRight : ('a,'b) sum -> 'b

val isRight : ('a,'b) sum -> bool

(* ------------------------------------------------------------------------- *)
(* Useful impure features.                                                   *)
(* ------------------------------------------------------------------------- *)

val newInt : unit -> int

val newInts : int -> int list

val withRef : 'r Unsynchronized.ref * 'r -> ('a -> 'b) -> 'a -> 'b

val cloneArray : 'a Metis.Array.array -> 'a Metis.Array.array

(* ------------------------------------------------------------------------- *)
(* The environment.                                                          *)
(* ------------------------------------------------------------------------- *)

val host : unit -> string

val time : unit -> string

val date : unit -> string

val readTextFile : {filename : string} -> string

val writeTextFile : {filename : string, contents : string} -> unit

(* ------------------------------------------------------------------------- *)
(* Profiling and error reporting.                                            *)
(* ------------------------------------------------------------------------- *)

val try : ('a -> 'b) -> 'a -> 'b

val warn : string -> unit

val die : string -> 'exit

val timed : ('a -> 'b) -> 'a -> real * 'b

val timedMany : ('a -> 'b) -> 'a -> real * 'b

val executionTime : unit -> real  (* Wall clock execution time *)

end

(**** Original file: Useful.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* ML UTILITY FUNCTIONS                                                      *)
(* Copyright (c) 2001-2004 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Useful :> Useful =
struct

(* ------------------------------------------------------------------------- *)
(* Exceptions                                                                *)
(* ------------------------------------------------------------------------- *)

exception Error of string;

exception Bug of string;

fun errorToString (Error message) = "\nError: " ^ message ^ "\n"
  | errorToString _ = raise Bug "errorToString: not an Error exception";

fun bugToString (Bug message) = "\nBug: " ^ message ^ "\n"
  | bugToString _ = raise Bug "bugToString: not a Bug exception";

fun total f x = SOME (f x) handle Error _ => NONE;

fun can f = Option.isSome o total f;

fun partial (e as Error _) f x = (case f x of SOME y => y | NONE => raise e)
  | partial _ _ _ = raise Bug "partial: must take an Error exception";

(* ------------------------------------------------------------------------- *)
(* Tracing                                                                   *)
(* ------------------------------------------------------------------------- *)

val tracePrint = Unsynchronized.ref print;

fun trace message = !tracePrint message;

(* ------------------------------------------------------------------------- *)
(* Combinators                                                               *)
(* ------------------------------------------------------------------------- *)

fun C f x y = f y x;

fun I x = x;

fun K x y = x;

fun S f g x = f x (g x);

fun W f x = f x x;

fun funpow 0 _ x = x
  | funpow n f x = funpow (n - 1) f (f x);

fun exp m =
    let
      fun f _ 0 z = z
        | f x y z = f (m (x,x)) (y div 2) (if y mod 2 = 0 then z else m (z,x))
    in
      f
    end;

val equal = fn x => fn y => x = y;

val notEqual = fn x => fn y => x <> y;

(* ------------------------------------------------------------------------- *)
(* Pairs                                                                     *)
(* ------------------------------------------------------------------------- *)

fun fst (x,_) = x;

fun snd (_,y) = y;

fun pair x y = (x,y);

fun swap (x,y) = (y,x);

fun curry f x y = f (x,y);

fun uncurry f (x,y) = f x y;

val op## = fn (f,g) => fn (x,y) => (f x, g y);

(* ------------------------------------------------------------------------- *)
(* State transformers                                                        *)
(* ------------------------------------------------------------------------- *)

val unit : 'a -> 's -> 'a * 's = pair;

fun bind f (g : 'a -> 's -> 'b * 's) = uncurry g o f;

fun mmap f (m : 's -> 'a * 's) = bind m (unit o f);

fun mjoin (f : 's -> ('s -> 'a * 's) * 's) = bind f I;

fun mwhile c b = let fun f a = if c a then bind (b a) f else unit a in f end;

(* ------------------------------------------------------------------------- *)
(* Lists                                                                     *)
(* ------------------------------------------------------------------------- *)

fun cons x y = x :: y;

fun hdTl l = (hd l, tl l);

fun append xs ys = xs @ ys;

fun singleton a = [a];

fun first f [] = NONE
  | first f (x :: xs) = (case f x of NONE => first f xs | s => s);

fun index p =
  let
    fun idx _ [] = NONE
      | idx n (x :: xs) = if p x then SOME n else idx (n + 1) xs
  in
    idx 0
  end;

fun maps (_ : 'a -> 's -> 'b * 's) [] = unit []
  | maps f (x :: xs) =
    bind (f x) (fn y => bind (maps f xs) (fn ys => unit (y :: ys)));

fun mapsPartial (_ : 'a -> 's -> 'b option * 's) [] = unit []
  | mapsPartial f (x :: xs) =
    bind
      (f x)
      (fn yo =>
          bind
            (mapsPartial f xs)
            (fn ys => unit (case yo of NONE => ys | SOME y => y :: ys)));

fun enumerate l = fst (maps (fn x => fn m => ((m, x), m + 1)) l 0);

fun zipwith f =
    let
      fun z l [] [] = l
        | z l (x :: xs) (y :: ys) = z (f x y :: l) xs ys
        | z _ _ _ = raise Error "zipwith: lists different lengths";
    in
      fn xs => fn ys => rev (z [] xs ys)
    end;

fun zip xs ys = zipwith pair xs ys;

fun unzip ab =
    foldl (fn ((x, y), (xs, ys)) => (x :: xs, y :: ys)) ([], []) (rev ab);

fun cartwith f =
  let
    fun aux _ res _ [] = res
      | aux xsCopy res [] (y :: yt) = aux xsCopy res xsCopy yt
      | aux xsCopy res (x :: xt) (ys as y :: _) =
        aux xsCopy (f x y :: res) xt ys
  in
    fn xs => fn ys =>
    let val xs' = rev xs in aux xs' [] xs' (rev ys) end
  end;

fun cart xs ys = cartwith pair xs ys;

local
  fun revDiv acc l 0 = (acc,l)
    | revDiv _ [] _ = raise Subscript
    | revDiv acc (h :: t) n = revDiv (h :: acc) t (n - 1);
in
  fun revDivide l = revDiv [] l;
end;

fun divide l n = let val (a,b) = revDivide l n in (rev a, b) end;

fun updateNth (n,x) l =
    let
      val (a,b) = revDivide l n
    in
      case b of [] => raise Subscript | _ :: t => List.revAppend (a, x :: t)
    end;

fun deleteNth n l =
    let
      val (a,b) = revDivide l n
    in
      case b of [] => raise Subscript | _ :: t => List.revAppend (a,t)
    end;

(* ------------------------------------------------------------------------- *)
(* Sets implemented with lists                                               *)
(* ------------------------------------------------------------------------- *)

fun mem x = List.exists (equal x);

fun insert x s = if mem x s then s else x :: s;

fun delete x s = List.filter (not o equal x) s;

fun setify s = rev (foldl (fn (v,x) => if mem v x then x else v :: x) [] s);

fun union s t = foldl (fn (v,x) => if mem v t then x else v :: x) t (rev s);

fun intersect s t =
    foldl (fn (v,x) => if mem v t then v :: x else x) [] (rev s);

fun difference s t =
    foldl (fn (v,x) => if mem v t then x else v :: x) [] (rev s);

fun subset s t = List.all (fn x => mem x t) s;

fun distinct [] = true
  | distinct (x :: rest) = not (mem x rest) andalso distinct rest;

(* ------------------------------------------------------------------------- *)
(* Comparisons.                                                              *)
(* ------------------------------------------------------------------------- *)

fun mapCompare f cmp (a,b) = cmp (f a, f b);

fun revCompare cmp x_y =
    case cmp x_y of LESS => GREATER | EQUAL => EQUAL | GREATER => LESS;

fun prodCompare xCmp yCmp ((x1,y1),(x2,y2)) =
    case xCmp (x1,x2) of
      LESS => LESS
    | EQUAL => yCmp (y1,y2)
    | GREATER => GREATER;

fun lexCompare cmp =
    let
      fun lex ([],[]) = EQUAL
        | lex ([], _ :: _) = LESS
        | lex (_ :: _, []) = GREATER
        | lex (x :: xs, y :: ys) =
          case cmp (x,y) of
            LESS => LESS
          | EQUAL => lex (xs,ys)
          | GREATER => GREATER
    in
      lex
    end;

fun optionCompare _ (NONE,NONE) = EQUAL
  | optionCompare _ (NONE,_) = LESS
  | optionCompare _ (_,NONE) = GREATER
  | optionCompare cmp (SOME x, SOME y) = cmp (x,y);

fun boolCompare (true,false) = LESS
  | boolCompare (false,true) = GREATER
  | boolCompare _ = EQUAL;

(* ------------------------------------------------------------------------- *)
(* Sorting and searching.                                                    *)
(* ------------------------------------------------------------------------- *)

(* Finding the minimum and maximum element of a list, wrt some order. *)

fun minimum cmp =
    let
      fun min (l,m,r) _ [] = (m, List.revAppend (l,r))
        | min (best as (_,m,_)) l (x :: r) =
          min (case cmp (x,m) of LESS => (l,x,r) | _ => best) (x :: l) r
    in
      fn [] => raise Empty
       | h :: t => min ([],h,t) [h] t
    end;

fun maximum cmp = minimum (revCompare cmp);

(* Merge (for the following merge-sort, but generally useful too). *)

fun merge cmp =
    let
      fun mrg acc [] ys = List.revAppend (acc,ys)
        | mrg acc xs [] = List.revAppend (acc,xs)
        | mrg acc (xs as x :: xt) (ys as y :: yt) =
          (case cmp (x,y) of
             GREATER => mrg (y :: acc) xs yt
           | _ => mrg (x :: acc) xt ys)
    in
      mrg []
    end;

(* Merge sort (stable). *)

fun sort cmp =
    let
      fun findRuns acc r rs [] = rev (rev (r :: rs) :: acc)
        | findRuns acc r rs (x :: xs) =
          case cmp (r,x) of
            GREATER => findRuns (rev (r :: rs) :: acc) x [] xs
          | _ => findRuns acc x (r :: rs) xs

      fun mergeAdj acc [] = rev acc
        | mergeAdj acc (xs as [_]) = List.revAppend (acc,xs)
        | mergeAdj acc (x :: y :: xs) = mergeAdj (merge cmp x y :: acc) xs

      fun mergePairs [xs] = xs
        | mergePairs l = mergePairs (mergeAdj [] l)
    in
      fn [] => []
       | l as [_] => l
       | h :: t => mergePairs (findRuns [] h [] t)
    end;
    
fun sortMap _ _ [] = []
  | sortMap _ _ (l as [_]) = l
  | sortMap f cmp xs =
    let
      fun ncmp ((m,_),(n,_)) = cmp (m,n)
      val nxs = map (fn x => (f x, x)) xs
      val nys = sort ncmp nxs
    in
      map snd nys
    end;

(* ------------------------------------------------------------------------- *)
(* Integers.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun interval m 0 = []
  | interval m len = m :: interval (m + 1) (len - 1);

fun divides _ 0 = true
  | divides 0 _ = false
  | divides a b = b mod (Int.abs a) = 0;

local
  fun hcf 0 n = n
    | hcf 1 _ = 1
    | hcf m n = hcf (n mod m) m;
in
  fun gcd m n =
      let
        val m = Int.abs m
        and n = Int.abs n
      in
        if m < n then hcf m n else hcf n m
      end;
end;

local
  fun both f g n = f n andalso g n;

  fun next f = let fun nx x = if f x then x else nx (x + 1) in nx end;

  fun looking res 0 _ _ = rev res
    | looking res n f x =
      let
        val p = next f x
        val res' = p :: res
        val f' = both f (not o divides p)
      in
        looking res' (n - 1) f' (p + 1)
      end;

  fun calcPrimes n = looking [] n (K true) 2

  val primesList = Unsynchronized.ref (calcPrimes 10);
in
  fun primes n = CRITICAL (fn () =>
      if length (!primesList) <= n then List.take (!primesList,n)
      else
        let
          val l = calcPrimes n
          val () = primesList := l
        in
          l
        end);

  fun primesUpTo n = CRITICAL (fn () =>
      let
        fun f k [] =
            let
              val l = calcPrimes (2 * k)
              val () = primesList := l
            in
              f k (List.drop (l,k))
            end
          | f k (p :: ps) =
            if p <= n then f (k + 1) ps else List.take (!primesList, k)
      in
        f 0 (!primesList)
      end);
end;

(* ------------------------------------------------------------------------- *)
(* Strings.                                                                  *)
(* ------------------------------------------------------------------------- *)

local
  fun len l = (length l, l)

  val upper = len (explode "ABCDEFGHIJKLMNOPQRSTUVWXYZ");

  val lower = len (explode "abcdefghijklmnopqrstuvwxyz");

  fun rotate (n,l) c k =
      List.nth (l, (k + Option.valOf (index (equal c) l)) mod n);
in
  fun rot k c =
      if Char.isLower c then rotate lower c k
      else if Char.isUpper c then rotate upper c k
      else c;
end;

fun charToInt #"0" = SOME 0
  | charToInt #"1" = SOME 1
  | charToInt #"2" = SOME 2
  | charToInt #"3" = SOME 3
  | charToInt #"4" = SOME 4
  | charToInt #"5" = SOME 5
  | charToInt #"6" = SOME 6
  | charToInt #"7" = SOME 7
  | charToInt #"8" = SOME 8
  | charToInt #"9" = SOME 9
  | charToInt _ = NONE;

fun charFromInt 0 = SOME #"0"
  | charFromInt 1 = SOME #"1"
  | charFromInt 2 = SOME #"2"
  | charFromInt 3 = SOME #"3"
  | charFromInt 4 = SOME #"4"
  | charFromInt 5 = SOME #"5"
  | charFromInt 6 = SOME #"6"
  | charFromInt 7 = SOME #"7"
  | charFromInt 8 = SOME #"8"
  | charFromInt 9 = SOME #"9"
  | charFromInt _ = NONE;

fun nChars x =
    let
      fun dup 0 l = l | dup n l = dup (n - 1) (x :: l)
    in
      fn n => implode (dup n [])
    end;

fun chomp s =
    let
      val n = size s
    in
      if n = 0 orelse String.sub (s, n - 1) <> #"\n" then s
      else String.substring (s, 0, n - 1)
    end;

local
  fun chop [] = []
    | chop (l as (h :: t)) = if Char.isSpace h then chop t else l;
in
  val trim = implode o chop o rev o chop o rev o explode;
end;

fun join _ [] = "" | join s (h :: t) = foldl (fn (x,y) => y ^ s ^ x) h t;

local
  fun match [] l = SOME l
    | match _ [] = NONE
    | match (x :: xs) (y :: ys) = if x = y then match xs ys else NONE;

  fun stringify acc [] = acc
    | stringify acc (h :: t) = stringify (implode h :: acc) t;
in
  fun split sep =
      let
        val pat = String.explode sep
        fun div1 prev recent [] = stringify [] (rev recent :: prev)
          | div1 prev recent (l as h :: t) =
            case match pat l of
              NONE => div1 prev (h :: recent) t
            | SOME rest => div1 (rev recent :: prev) [] rest
      in
        fn s => div1 [] [] (explode s)
      end;
end;

(***
fun pluralize {singular,plural} = fn 1 => singular | _ => plural;
***)

fun mkPrefix p s = p ^ s;

fun destPrefix p =
    let
      fun check s = String.isPrefix p s orelse raise Error "destPrefix"

      val sizeP = size p
    in
      fn s => (check s; String.extract (s,sizeP,NONE))
    end;

fun isPrefix p = can (destPrefix p);

(* ------------------------------------------------------------------------- *)
(* Tables.                                                                   *)
(* ------------------------------------------------------------------------- *)

type columnAlignment = {leftAlign : bool, padChar : char}

fun alignColumn {leftAlign,padChar} column =
    let
      val (n,_) = maximum Int.compare (map size column)

      fun pad entry row =
          let
            val padding = nChars padChar (n - size entry)
          in
            if leftAlign then entry ^ padding ^ row
            else padding ^ entry ^ row
          end
    in
      zipwith pad column
    end;

fun alignTable [] rows = map (K "") rows
  | alignTable [{leftAlign = true, padChar = #" "}] rows = map hd rows
  | alignTable (align :: aligns) rows =
    alignColumn align (map hd rows) (alignTable aligns (map tl rows));

(* ------------------------------------------------------------------------- *)
(* Reals.                                                                    *)
(* ------------------------------------------------------------------------- *)

val realToString = Real.toString;

fun percentToString x = Int.toString (Real.round (100.0 * x)) ^ "%";

fun pos r = Real.max (r,0.0);

local
  val invLn2 = 1.0 / Math.ln 2.0;
in
  fun log2 x = invLn2 * Math.ln x;
end;

(* ------------------------------------------------------------------------- *)
(* Sums.                                                                     *)
(* ------------------------------------------------------------------------- *)

datatype ('a,'b) sum = Left of 'a | Right of 'b

fun destLeft (Left l) = l
  | destLeft _ = raise Error "destLeft";

fun isLeft (Left _) = true
  | isLeft (Right _) = false;

fun destRight (Right r) = r
  | destRight _ = raise Error "destRight";

fun isRight (Left _) = false
  | isRight (Right _) = true;

(* ------------------------------------------------------------------------- *)
(* Useful impure features.                                                   *)
(* ------------------------------------------------------------------------- *)

local
  val generator = Unsynchronized.ref 0
in
  fun newInt () = CRITICAL (fn () =>
      let
        val n = !generator
        val () = generator := n + 1
      in
        n
      end);

  fun newInts 0 = []
    | newInts k = CRITICAL (fn () =>
      let
        val n = !generator
        val () = generator := n + k
      in
        interval n k
      end);
end;

fun withRef (r,new) f x =
  let
    val old = !r
    val () = r := new
    val y = f x handle e => (r := old; raise e)
    val () = r := old
  in
    y
  end;

fun cloneArray a =
    let
      fun index i = Array.sub (a,i)
    in
      Array.tabulate (Array.length a, index)
    end;

(* ------------------------------------------------------------------------- *)
(* Environment.                                                              *)
(* ------------------------------------------------------------------------- *)

fun host () = Option.getOpt (OS.Process.getEnv "HOSTNAME", "unknown");

fun time () = Date.fmt "%H:%M:%S" (Date.fromTimeLocal (Time.now ()));

fun date () = Date.fmt "%d/%m/%Y" (Date.fromTimeLocal (Time.now ()));

fun readTextFile {filename} =
  let
    open TextIO
    val h = openIn filename
    val contents = inputAll h
    val () = closeIn h
  in
    contents
  end;

fun writeTextFile {filename,contents} =
  let
    open TextIO
    val h = openOut filename
    val () = output (h,contents)
    val () = closeOut h
  in
    ()
  end;

(* ------------------------------------------------------------------------- *)
(* Profiling                                                                 *)
(* ------------------------------------------------------------------------- *)

local
  fun err x s = TextIO.output (TextIO.stdErr, x ^ ": " ^ s ^ "\n");
in
  fun try f x = f x
      handle e as Error _ => (err "try" (errorToString e); raise e)
           | e as Bug _ => (err "try" (bugToString e); raise e)
           | e => (err "try" "strange exception raised"; raise e);

  val warn = err "WARNING";

  fun die s = (err "\nFATAL ERROR" s; OS.Process.exit OS.Process.failure);
end;

fun timed f a =
  let
    val tmr = Timer.startCPUTimer ()
    val res = f a
    val {usr,sys,...} = Timer.checkCPUTimer tmr
  in
    (Time.toReal usr + Time.toReal sys, res)
  end;

local
  val MIN = 1.0;

  fun several n t f a =
    let
      val (t',res) = timed f a
      val t = t + t'
      val n = n + 1
    in
      if t > MIN then (t / Real.fromInt n, res) else several n t f a
    end;
in
  fun timedMany f a = several 0 0.0 f a
end;

val executionTime =
    let
      val startTime = Time.toReal (Time.now ())
    in
      fn () => Time.toReal (Time.now ()) - startTime
    end;

end
end;

(**** Original file: Lazy.sig ****)

(* ========================================================================= *)
(* SUPPORT FOR LAZY EVALUATION                                               *)
(* Copyright (c) 2007 Joe Hurd, distributed under the BSD License      *)
(* ========================================================================= *)

signature Lazy =
sig

type 'a lazy

val delay : (unit -> 'a) -> 'a lazy

val force : 'a lazy -> 'a

val memoize : (unit -> 'a) -> unit -> 'a

end

(**** Original file: Lazy.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* SUPPORT FOR LAZY EVALUATION                                               *)
(* Copyright (c) 2007 Joe Hurd, distributed under the BSD License      *)
(* ========================================================================= *)

structure Lazy :> Lazy =
struct

datatype 'a thunk =
    Value of 'a
  | Thunk of unit -> 'a;

datatype 'a lazy = Lazy of 'a thunk Unsynchronized.ref;

fun delay f = Lazy (Unsynchronized.ref (Thunk f));

fun force (Lazy (Unsynchronized.ref (Value v))) = v
  | force (Lazy (s as Unsynchronized.ref (Thunk f))) =
    let
      val v = f ()
      val () = s := Value v
    in
      v
    end;

fun memoize f =
    let
      val t = delay f
    in
      fn () => force t
    end;

end
end;

(**** Original file: Ordered.sig ****)

(* ========================================================================= *)
(* ORDERED TYPES                                                             *)
(* Copyright (c) 2004-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Ordered =
sig

type t

val compare : t * t -> order

(*
  PROVIDES

  !x : t. compare (x,x) = EQUAL

  !x y : t. compare (x,y) = LESS <=> compare (y,x) = GREATER

  !x y : t. compare (x,y) = EQUAL ==> compare (y,x) = EQUAL

  !x y z : t. compare (x,y) = EQUAL ==> compare (x,z) = compare (y,z)

  !x y z : t.
    compare (x,y) = LESS andalso compare (y,z) = LESS ==>
    compare (x,z) = LESS

  !x y z : t.
    compare (x,y) = GREATER andalso compare (y,z) = GREATER ==>
    compare (x,z) = GREATER
*)

end

(**** Original file: Ordered.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* ORDERED TYPES                                                             *)
(* Copyright (c) 2004-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure IntOrdered =
struct type t = int val compare = Int.compare end;

structure StringOrdered =
struct type t = string val compare = String.compare end;
end;

(**** Original file: Set.sig ****)

(* ========================================================================= *)
(* FINITE SETS                                                               *)
(* Copyright (c) 2004-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Set =
sig

(* ------------------------------------------------------------------------- *)
(* Finite sets                                                               *)
(* ------------------------------------------------------------------------- *)

type 'elt set

val comparison : 'elt set -> ('elt * 'elt -> order)

val empty : ('elt * 'elt -> order) -> 'elt set

val singleton : ('elt * 'elt -> order) -> 'elt -> 'elt set

val null : 'elt set -> bool

val size : 'elt set -> int

val member : 'elt -> 'elt set -> bool

val add : 'elt set -> 'elt -> 'elt set

val addList : 'elt set -> 'elt list -> 'elt set

val delete : 'elt set -> 'elt -> 'elt set  (* raises Error *)

(* Union and intersect prefer elements in the second set *)

val union : 'elt set -> 'elt set -> 'elt set

val unionList : 'elt set list -> 'elt set

val intersect : 'elt set -> 'elt set -> 'elt set

val intersectList : 'elt set list -> 'elt set

val difference : 'elt set -> 'elt set -> 'elt set

val symmetricDifference : 'elt set -> 'elt set -> 'elt set

val disjoint : 'elt set -> 'elt set -> bool

val subset : 'elt set -> 'elt set -> bool

val equal : 'elt set -> 'elt set -> bool

val filter : ('elt -> bool) -> 'elt set -> 'elt set

val partition : ('elt -> bool) -> 'elt set -> 'elt set * 'elt set

val count : ('elt -> bool) -> 'elt set -> int

val foldl : ('elt * 's -> 's) -> 's -> 'elt set -> 's

val foldr : ('elt * 's -> 's) -> 's -> 'elt set -> 's

val findl : ('elt -> bool) -> 'elt set -> 'elt option

val findr : ('elt -> bool) -> 'elt set -> 'elt option

val firstl : ('elt -> 'a option) -> 'elt set -> 'a option

val firstr : ('elt -> 'a option) -> 'elt set -> 'a option

val exists : ('elt -> bool) -> 'elt set -> bool

val all : ('elt -> bool) -> 'elt set -> bool

val map : ('elt -> 'a) -> 'elt set -> ('elt * 'a) list

val transform : ('elt -> 'a) -> 'elt set -> 'a list

val app : ('elt -> unit) -> 'elt set -> unit

val toList : 'elt set -> 'elt list

val fromList : ('elt * 'elt -> order) -> 'elt list -> 'elt set

val pick : 'elt set -> 'elt  (* raises Empty *)

val random : 'elt set -> 'elt  (* raises Empty *)

val deletePick : 'elt set -> 'elt * 'elt set  (* raises Empty *)

val deleteRandom : 'elt set -> 'elt * 'elt set  (* raises Empty *)

val compare : 'elt set * 'elt set -> order

val close : ('elt set -> 'elt set) -> 'elt set -> 'elt set

val toString : 'elt set -> string

(* ------------------------------------------------------------------------- *)
(* Iterators over sets                                                       *)
(* ------------------------------------------------------------------------- *)

type 'elt iterator

val mkIterator : 'elt set -> 'elt iterator option

val mkRevIterator : 'elt set -> 'elt iterator option

val readIterator : 'elt iterator -> 'elt

val advanceIterator : 'elt iterator -> 'elt iterator option

end

(**** Original file: RandomSet.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* FINITE SETS IMPLEMENTED WITH RANDOMLY BALANCED TREES                      *)
(* Copyright (c) 2004-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure RandomSet :> Set =
struct

exception Bug = Useful.Bug;

exception Error = Useful.Error;

val pointerEqual = Portable.pointerEqual;

val K = Useful.K;

val snd = Useful.snd;

val randomInt = Portable.randomInt;

val randomWord = Portable.randomWord;

(* ------------------------------------------------------------------------- *)
(* Random search trees.                                                      *)
(* ------------------------------------------------------------------------- *)

type priority = Word.word;

datatype 'a tree =
    E
  | T of
    {size : int,
     priority : priority,
     left : 'a tree,
     key : 'a,
     right : 'a tree};
    
type 'a node =
     {size : int,
      priority : priority,
      left : 'a tree,
      key : 'a,
      right : 'a tree};

datatype 'a set = Set of ('a * 'a -> order) * 'a tree;

(* ------------------------------------------------------------------------- *)
(* Random priorities.                                                        *)
(* ------------------------------------------------------------------------- *)

local
  val randomPriority = randomWord;

  val priorityOrder = Word.compare;
in
  fun treeSingleton key =
      T {size = 1, priority = randomPriority (),
         left = E, key = key, right = E};

  fun nodePriorityOrder cmp (x1 : 'a node, x2 : 'a node) =
      let
        val {priority = p1, key = k1, ...} = x1
        and {priority = p2, key = k2, ...} = x2
      in
        case priorityOrder (p1,p2) of
          LESS => LESS
        | EQUAL => cmp (k1,k2)
        | GREATER => GREATER
      end;
end;

(* ------------------------------------------------------------------------- *)
(* Debugging functions.                                                      *)
(* ------------------------------------------------------------------------- *)

local
  fun checkSizes E = 0
    | checkSizes (T {size,left,right,...}) =
      let
        val l = checkSizes left
        and r = checkSizes right
        val () = if l + 1 + r = size then () else raise Error "wrong size"
      in
        size
      end

  fun checkSorted _ x E = x
    | checkSorted cmp x (T {left,key,right,...}) =
      let
        val x = checkSorted cmp x left
        val () =
            case x of
              NONE => ()
            | SOME k =>
              case cmp (k,key) of
                LESS => ()
              | EQUAL => raise Error "duplicate keys"
              | GREATER => raise Error "unsorted"
      in
        checkSorted cmp (SOME key) right
      end;

  fun checkPriorities _ E = NONE
    | checkPriorities cmp (T (x as {left,right,...})) =
      let
        val () =
            case checkPriorities cmp left of
              NONE => ()
            | SOME l =>
              case nodePriorityOrder cmp (l,x) of
                LESS => ()
              | EQUAL => raise Error "left child has equal key"
              | GREATER => raise Error "left child has greater priority"
        val () =
            case checkPriorities cmp right of
              NONE => ()
            | SOME r =>
              case nodePriorityOrder cmp (r,x) of
                LESS => ()
              | EQUAL => raise Error "right child has equal key"
              | GREATER => raise Error "right child has greater priority"
      in
        SOME x
      end;
in
  fun checkWellformed s (set as Set (cmp,tree)) =
      (let
         val _ = checkSizes tree
         val _ = checkSorted cmp NONE tree
         val _ = checkPriorities cmp tree
       in
         set
       end
       handle Error err => raise Bug err)
      handle Bug bug => raise Bug (s ^ "\nRandomSet.checkWellformed: " ^ bug);
end;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

fun comparison (Set (cmp,_)) = cmp;

fun empty cmp = Set (cmp,E);

fun treeSize E = 0
  | treeSize (T {size = s, ...}) = s;

fun size (Set (_,tree)) = treeSize tree;

fun mkT p l k r =
    T {size = treeSize l + 1 + treeSize r, priority = p,
       left = l, key = k, right = r};

fun singleton cmp key = Set (cmp, treeSingleton key);

local
  fun treePeek cmp E pkey = NONE
    | treePeek cmp (T {left,key,right,...}) pkey =
      case cmp (pkey,key) of
        LESS => treePeek cmp left pkey
      | EQUAL => SOME key
      | GREATER => treePeek cmp right pkey
in
  fun peek (Set (cmp,tree)) key = treePeek cmp tree key;
end;

(* treeAppend assumes that every element of the first tree is less than *)
(* every element of the second tree. *)

fun treeAppend _ t1 E = t1
  | treeAppend _ E t2 = t2
  | treeAppend cmp (t1 as T x1) (t2 as T x2) =
    case nodePriorityOrder cmp (x1,x2) of
      LESS =>
      let
        val {priority = p2, left = l2, key = k2, right = r2, ...} = x2
      in
        mkT p2 (treeAppend cmp t1 l2) k2 r2
      end
    | EQUAL => raise Bug "RandomSet.treeAppend: equal keys"
    | GREATER =>
      let
        val {priority = p1, left = l1, key = k1, right = r1, ...} = x1
      in
        mkT p1 l1 k1 (treeAppend cmp r1 t2)
      end;

(* nodePartition splits the node into three parts: the keys comparing less *)
(* than the supplied key, an optional equal key, and the keys comparing *)
(* greater. *)

local
  fun mkLeft [] t = t
    | mkLeft (({priority,left,key,...} : 'a node) :: xs) t =
      mkLeft xs (mkT priority left key t);

  fun mkRight [] t = t
    | mkRight (({priority,key,right,...} : 'a node) :: xs) t =
      mkRight xs (mkT priority t key right);

  fun treePart _ _ lefts rights E = (mkLeft lefts E, NONE, mkRight rights E)
    | treePart cmp pkey lefts rights (T x) = nodePart cmp pkey lefts rights x
  and nodePart cmp pkey lefts rights (x as {left,key,right,...}) =
      case cmp (pkey,key) of
        LESS => treePart cmp pkey lefts (x :: rights) left
      | EQUAL => (mkLeft lefts left, SOME key, mkRight rights right)
      | GREATER => treePart cmp pkey (x :: lefts) rights right;
in
  fun nodePartition cmp x pkey = nodePart cmp pkey [] [] x;
end;

(* union first calls treeCombineRemove, to combine the values *)
(* for equal keys into the first map and remove them from the second map. *)
(* Note that the combined key is always the one from the second map. *)

local
  fun treeCombineRemove _ t1 E = (t1,E)
    | treeCombineRemove _ E t2 = (E,t2)
    | treeCombineRemove cmp (t1 as T x1) (t2 as T x2) =
      let
        val {priority = p1, left = l1, key = k1, right = r1, ...} = x1
        val (l2,k2,r2) = nodePartition cmp x2 k1
        val (l1,l2) = treeCombineRemove cmp l1 l2
        and (r1,r2) = treeCombineRemove cmp r1 r2
      in
        case k2 of
          NONE => if treeSize l2 + treeSize r2 = #size x2 then (t1,t2)
                  else (mkT p1 l1 k1 r1, treeAppend cmp l2 r2)
        | SOME k2 => (mkT p1 l1 k2 r1, treeAppend cmp l2 r2)
      end;

  fun treeUnionDisjoint _ t1 E = t1
    | treeUnionDisjoint _ E t2 = t2
    | treeUnionDisjoint cmp (T x1) (T x2) =
      case nodePriorityOrder cmp (x1,x2) of
        LESS => nodeUnionDisjoint cmp x2 x1
      | EQUAL => raise Bug "RandomSet.unionDisjoint: equal keys"
      | GREATER => nodeUnionDisjoint cmp x1 x2

  and nodeUnionDisjoint cmp x1 x2 =
      let
        val {priority = p1, left = l1, key = k1, right = r1, ...} = x1
        val (l2,_,r2) = nodePartition cmp x2 k1
        val l = treeUnionDisjoint cmp l1 l2
        and r = treeUnionDisjoint cmp r1 r2
      in
        mkT p1 l k1 r
      end;
in
  fun union (s1 as Set (cmp,t1)) (Set (_,t2)) =
      if pointerEqual (t1,t2) then s1
      else
        let
          val (t1,t2) = treeCombineRemove cmp t1 t2
        in
          Set (cmp, treeUnionDisjoint cmp t1 t2)
        end;
end;

(*DEBUG
val union = fn t1 => fn t2 =>
    checkWellformed "RandomSet.union: result"
      (union (checkWellformed "RandomSet.union: input 1" t1)
             (checkWellformed "RandomSet.union: input 2" t2));
*)

(* intersect is a simple case of the union algorithm. *)

local
  fun treeIntersect _ _ E = E
    | treeIntersect _ E _ = E
    | treeIntersect cmp (t1 as T x1) (t2 as T x2) =
      let
        val {priority = p1, left = l1, key = k1, right = r1, ...} = x1
        val (l2,k2,r2) = nodePartition cmp x2 k1
        val l = treeIntersect cmp l1 l2
        and r = treeIntersect cmp r1 r2
      in
        case k2 of
          NONE => treeAppend cmp l r
        | SOME k2 => mkT p1 l k2 r
      end;
in
  fun intersect (s1 as Set (cmp,t1)) (Set (_,t2)) =
      if pointerEqual (t1,t2) then s1
      else Set (cmp, treeIntersect cmp t1 t2);
end;

(*DEBUG
val intersect = fn t1 => fn t2 =>
    checkWellformed "RandomSet.intersect: result"
      (intersect (checkWellformed "RandomSet.intersect: input 1" t1)
                 (checkWellformed "RandomSet.intersect: input 2" t2));
*)

(* delete raises an exception if the supplied key is not found, which *)
(* makes it simpler to maximize sharing. *)

local
  fun treeDelete _ E _ = raise Error "RandomSet.delete: element not found"
    | treeDelete cmp (T {priority,left,key,right,...}) dkey =
      case cmp (dkey,key) of
        LESS => mkT priority (treeDelete cmp left dkey) key right
      | EQUAL => treeAppend cmp left right
      | GREATER => mkT priority left key (treeDelete cmp right dkey);
in
  fun delete (Set (cmp,tree)) key = Set (cmp, treeDelete cmp tree key);
end;
 
(*DEBUG
val delete = fn t => fn x =>
    checkWellformed "RandomSet.delete: result"
      (delete (checkWellformed "RandomSet.delete: input" t) x);
*)

(* Set difference *)

local
  fun treeDifference _ t1 E = t1
    | treeDifference _ E _ = E
    | treeDifference cmp (t1 as T x1) (T x2) =
      let
        val {size = s1, priority = p1, left = l1, key = k1, right = r1} = x1
        val (l2,k2,r2) = nodePartition cmp x2 k1
        val l = treeDifference cmp l1 l2
        and r = treeDifference cmp r1 r2
      in
        if Option.isSome k2 then treeAppend cmp l r
        else if treeSize l + treeSize r + 1 = s1 then t1
        else mkT p1 l k1 r
      end;
in
  fun difference (Set (cmp,tree1)) (Set (_,tree2)) =
      if pointerEqual (tree1,tree2) then Set (cmp,E)
      else Set (cmp, treeDifference cmp tree1 tree2);
end;

(*DEBUG
val difference = fn t1 => fn t2 =>
    checkWellformed "RandomSet.difference: result"
      (difference (checkWellformed "RandomSet.difference: input 1" t1)
                  (checkWellformed "RandomSet.difference: input 2" t2));
*)

(* Subsets *)

local
  fun treeSubset _ E _ = true
    | treeSubset _ _ E = false
    | treeSubset cmp (t1 as T x1) (T x2) =
      let
        val {size = s1, left = l1, key = k1, right = r1, ...} = x1
        and {size = s2, ...} = x2
      in
        s1 <= s2 andalso
        let
          val (l2,k2,r2) = nodePartition cmp x2 k1
        in
          Option.isSome k2 andalso
          treeSubset cmp l1 l2 andalso
          treeSubset cmp r1 r2
        end
      end;
in
  fun subset (Set (cmp,tree1)) (Set (_,tree2)) =
      pointerEqual (tree1,tree2) orelse
      treeSubset cmp tree1 tree2;
end;

(* Set equality *)

local
  fun treeEqual _ E E = true
    | treeEqual _ E _ = false
    | treeEqual _ _ E = false
    | treeEqual cmp (t1 as T x1) (T x2) =
      let
        val {size = s1, left = l1, key = k1, right = r1, ...} = x1
        and {size = s2, ...} = x2
      in
        s1 = s2 andalso
        let
          val (l2,k2,r2) = nodePartition cmp x2 k1
        in
          Option.isSome k2 andalso
          treeEqual cmp l1 l2 andalso
          treeEqual cmp r1 r2
        end
      end;
in
  fun equal (Set (cmp,tree1)) (Set (_,tree2)) =
      pointerEqual (tree1,tree2) orelse
      treeEqual cmp tree1 tree2;
end;

(* filter is the basic function for preserving the tree structure. *)

local
  fun treeFilter _ _ E = E
    | treeFilter cmp pred (T {priority,left,key,right,...}) =
      let
        val left = treeFilter cmp pred left
        and right = treeFilter cmp pred right
      in
        if pred key then mkT priority left key right
        else treeAppend cmp left right
      end;
in
  fun filter pred (Set (cmp,tree)) = Set (cmp, treeFilter cmp pred tree);
end;

(* nth picks the nth smallest key (counting from 0). *)

local
  fun treeNth E _ = raise Subscript
    | treeNth (T {left,key,right,...}) n =
      let
        val k = treeSize left
      in
        if n = k then key
        else if n < k then treeNth left n
        else treeNth right (n - (k + 1))
      end;
in
  fun nth (Set (_,tree)) n = treeNth tree n;
end;

(* ------------------------------------------------------------------------- *)
(* Iterators.                                                                *)
(* ------------------------------------------------------------------------- *)

fun leftSpine E acc = acc
  | leftSpine (t as T {left,...}) acc = leftSpine left (t :: acc);

fun rightSpine E acc = acc
  | rightSpine (t as T {right,...}) acc = rightSpine right (t :: acc);

datatype 'a iterator =
    LR of 'a * 'a tree * 'a tree list
  | RL of 'a * 'a tree * 'a tree list;

fun mkLR [] = NONE
  | mkLR (T {key,right,...} :: l) = SOME (LR (key,right,l))
  | mkLR (E :: _) = raise Bug "RandomSet.mkLR";

fun mkRL [] = NONE
  | mkRL (T {key,left,...} :: l) = SOME (RL (key,left,l))
  | mkRL (E :: _) = raise Bug "RandomSet.mkRL";

fun mkIterator (Set (_,tree)) = mkLR (leftSpine tree []);

fun mkRevIterator (Set (_,tree)) = mkRL (rightSpine tree []);

fun readIterator (LR (key,_,_)) = key
  | readIterator (RL (key,_,_)) = key;

fun advanceIterator (LR (_,next,l)) = mkLR (leftSpine next l)
  | advanceIterator (RL (_,next,l)) = mkRL (rightSpine next l);

(* ------------------------------------------------------------------------- *)
(* Derived operations.                                                       *)
(* ------------------------------------------------------------------------- *)

fun null s = size s = 0;

fun member x s = Option.isSome (peek s x);

fun add s x = union s (singleton (comparison s) x);

(*DEBUG
val add = fn s => fn x =>
    checkWellformed "RandomSet.add: result"
      (add (checkWellformed "RandomSet.add: input" s) x);
*)

local
  fun unionPairs ys [] = rev ys
    | unionPairs ys (xs as [_]) = List.revAppend (ys,xs)
    | unionPairs ys (x1 :: x2 :: xs) = unionPairs (union x1 x2 :: ys) xs;
in
  fun unionList [] = raise Error "RandomSet.unionList: no sets"
    | unionList [s] = s
    | unionList l = unionList (unionPairs [] l);
end;

local
  fun intersectPairs ys [] = rev ys
    | intersectPairs ys (xs as [_]) = List.revAppend (ys,xs)
    | intersectPairs ys (x1 :: x2 :: xs) =
      intersectPairs (intersect x1 x2 :: ys) xs;
in
  fun intersectList [] = raise Error "RandomSet.intersectList: no sets"
    | intersectList [s] = s
    | intersectList l = intersectList (intersectPairs [] l);
end;

fun symmetricDifference s1 s2 = union (difference s1 s2) (difference s2 s1);

fun disjoint s1 s2 = null (intersect s1 s2);

fun partition pred set = (filter pred set, filter (not o pred) set);

local
  fun fold _ NONE acc = acc
    | fold f (SOME iter) acc =
      let
        val key = readIterator iter
      in
        fold f (advanceIterator iter) (f (key,acc))
      end;
in
  fun foldl f b m = fold f (mkIterator m) b;

  fun foldr f b m = fold f (mkRevIterator m) b;
end;

local
  fun find _ NONE = NONE
    | find pred (SOME iter) =
      let
        val key = readIterator iter
      in
        if pred key then SOME key
        else find pred (advanceIterator iter)
      end;
in
  fun findl p m = find p (mkIterator m);

  fun findr p m = find p (mkRevIterator m);
end;

local
  fun first _ NONE = NONE
    | first f (SOME iter) =
      let
        val key = readIterator iter
      in
        case f key of
          NONE => first f (advanceIterator iter)
        | s => s
      end;
in
  fun firstl f m = first f (mkIterator m);

  fun firstr f m = first f (mkRevIterator m);
end;

fun count p = foldl (fn (x,n) => if p x then n + 1 else n) 0;

fun fromList cmp l = List.foldl (fn (k,s) => add s k) (empty cmp) l;

fun addList s l = union s (fromList (comparison s) l);

fun toList s = foldr op:: [] s;

fun map f s = rev (foldl (fn (x,l) => (x, f x) :: l) [] s);

fun transform f s = rev (foldl (fn (x,l) => f x :: l) [] s);

fun app f s = foldl (fn (x,()) => f x) () s;

fun exists p s = Option.isSome (findl p s);

fun all p s = not (exists (not o p) s);

local
  fun iterCompare _ NONE NONE = EQUAL
    | iterCompare _ NONE (SOME _) = LESS
    | iterCompare _ (SOME _) NONE = GREATER
    | iterCompare cmp (SOME i1) (SOME i2) =
      keyIterCompare cmp (readIterator i1) (readIterator i2) i1 i2

  and keyIterCompare cmp k1 k2 i1 i2 =
      case cmp (k1,k2) of
        LESS => LESS
      | EQUAL => iterCompare cmp (advanceIterator i1) (advanceIterator i2)
      | GREATER => GREATER;
in
  fun compare (s1,s2) =
      if pointerEqual (s1,s2) then EQUAL
      else
        case Int.compare (size s1, size s2) of
          LESS => LESS
        | EQUAL => iterCompare (comparison s1) (mkIterator s1) (mkIterator s2)
        | GREATER => GREATER;
end;

fun pick s =
    case findl (K true) s of
      SOME p => p
    | NONE => raise Error "RandomSet.pick: empty";

fun random s =
    case size s of
      0 => raise Error "RandomSet.random: empty"
    | n => nth s (randomInt n);

fun deletePick s = let val x = pick s in (x, delete s x) end;

fun deleteRandom s = let val x = random s in (x, delete s x) end;

fun close f s = let val s' = f s in if equal s s' then s else close f s' end;

fun toString s = "{" ^ (if null s then "" else Int.toString (size s)) ^ "}";

end
end;

(**** Original file: Set.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* FINITE SETS                                                               *)
(* Copyright (c) 2004-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Set = RandomSet;
end;

(**** Original file: ElementSet.sig ****)

(* ========================================================================= *)
(* FINITE SETS WITH A FIXED ELEMENT TYPE                                     *)
(* Copyright (c) 2004-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature ElementSet =
sig

type element

(* ------------------------------------------------------------------------- *)
(* Finite sets                                                               *)
(* ------------------------------------------------------------------------- *)

type set

val empty : set

val singleton : element -> set

val null : set -> bool

val size : set -> int

val member : element -> set -> bool

val add : set -> element -> set

val addList : set -> element list -> set

val delete : set -> element -> set  (* raises Error *)

(* Union and intersect prefer elements in the second set *)

val union : set -> set -> set

val unionList : set list -> set

val intersect : set -> set -> set

val intersectList : set list -> set

val difference : set -> set -> set

val symmetricDifference : set -> set -> set

val disjoint : set -> set -> bool

val subset : set -> set -> bool

val equal : set -> set -> bool

val filter : (element -> bool) -> set -> set

val partition : (element -> bool) -> set -> set * set

val count : (element -> bool) -> set -> int

val foldl : (element * 's -> 's) -> 's -> set -> 's

val foldr : (element * 's -> 's) -> 's -> set -> 's

val findl : (element -> bool) -> set -> element option

val findr : (element -> bool) -> set -> element option

val firstl : (element -> 'a option) -> set -> 'a option

val firstr : (element -> 'a option) -> set -> 'a option

val exists : (element -> bool) -> set -> bool

val all : (element -> bool) -> set -> bool

val map : (element -> 'a) -> set -> (element * 'a) list

val transform : (element -> 'a) -> set -> 'a list

val app : (element -> unit) -> set -> unit

val toList : set -> element list

val fromList : element list -> set

val pick : set -> element  (* raises Empty *)

val random : set -> element  (* raises Empty *)

val deletePick : set -> element * set  (* raises Empty *)

val deleteRandom : set -> element * set  (* raises Empty *)

val compare : set * set -> order

val close : (set -> set) -> set -> set

val toString : set -> string

(* ------------------------------------------------------------------------- *)
(* Iterators over sets                                                       *)
(* ------------------------------------------------------------------------- *)

type iterator

val mkIterator : set -> iterator option

val mkRevIterator : set -> iterator option

val readIterator : iterator -> element

val advanceIterator : iterator -> iterator option

end

(**** Original file: ElementSet.sml ****)

(* ========================================================================= *)
(* FINITE SETS WITH A FIXED ELEMENT TYPE                                     *)
(* Copyright (c) 2004-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

functor ElementSet (Key : Ordered) :> ElementSet where type element = Key.t =
struct

 open Metis;

type element = Key.t;

(* ------------------------------------------------------------------------- *)
(* Finite sets                                                               *)
(* ------------------------------------------------------------------------- *)

type set = Key.t Set.set;

val empty = Set.empty Key.compare;

fun singleton key = Set.singleton Key.compare key;

val null = Set.null;

val size = Set.size;

val member = Set.member;

val add = Set.add;

val addList = Set.addList;

val delete = Set.delete;

val op union = Set.union;

val unionList = Set.unionList;

val intersect = Set.intersect;

val intersectList = Set.intersectList;

val difference = Set.difference;

val symmetricDifference = Set.symmetricDifference;

val disjoint = Set.disjoint;

val op subset = Set.subset;

val equal = Set.equal;

val filter = Set.filter;

val partition = Set.partition;

val count = Set.count;

val foldl = Set.foldl;

val foldr = Set.foldr;

val findl = Set.findl;

val findr = Set.findr;

val firstl = Set.firstl;

val firstr = Set.firstr;

val exists = Set.exists;

val all = Set.all;

val map = Set.map;

val transform = Set.transform;

val app = Set.app;

val toList = Set.toList;

fun fromList l = Set.fromList Key.compare l;

val pick = Set.pick;

val random = Set.random;

val deletePick = Set.deletePick;

val deleteRandom = Set.deleteRandom;

val compare = Set.compare;

val close = Set.close;

val toString = Set.toString;

(* ------------------------------------------------------------------------- *)
(* Iterators over sets                                                       *)
(* ------------------------------------------------------------------------- *)

type iterator = Key.t Set.iterator;

val mkIterator = Set.mkIterator;

val mkRevIterator = Set.mkRevIterator;

val readIterator = Set.readIterator;

val advanceIterator = Set.advanceIterator;

end

 structure Metis = struct open Metis;

structure IntSet =
ElementSet (IntOrdered);

structure StringSet =
ElementSet (StringOrdered);

 end;

(**** Original file: Map.sig ****)

(* ========================================================================= *)
(* FINITE MAPS                                                               *)
(* Copyright (c) 2004-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Map =
sig

(* ------------------------------------------------------------------------- *)
(* Finite maps                                                               *)
(* ------------------------------------------------------------------------- *)

type ('key,'a) map

val new : ('key * 'key -> order) -> ('key,'a) map

val null : ('key,'a) map -> bool

val size : ('key,'a) map -> int

val singleton : ('key * 'key -> order) -> 'key * 'a -> ('key,'a) map

val inDomain : 'key -> ('key,'a) map -> bool

val peek : ('key,'a) map -> 'key -> 'a option

val insert : ('key,'a) map -> 'key * 'a -> ('key,'a) map

val insertList : ('key,'a) map -> ('key * 'a) list -> ('key,'a) map

val get : ('key,'a) map -> 'key -> 'a  (* raises Error *)

(* Union and intersect prefer keys in the second map *)

val union :
    ('a * 'a -> 'a option) -> ('key,'a) map -> ('key,'a) map -> ('key,'a) map

val intersect :
    ('a * 'a -> 'a option) -> ('key,'a) map -> ('key,'a) map -> ('key,'a) map

val delete : ('key,'a) map -> 'key -> ('key,'a) map  (* raises Error *)

val difference : ('key,'a) map -> ('key,'b) map -> ('key,'a) map

val subsetDomain : ('key,'a) map -> ('key,'a) map -> bool

val equalDomain : ('key,'a) map -> ('key,'a) map -> bool

val mapPartial : ('key * 'a -> 'b option) -> ('key,'a) map -> ('key,'b) map

val filter : ('key * 'a -> bool) -> ('key,'a) map -> ('key,'a) map

val map : ('key * 'a -> 'b) -> ('key,'a) map -> ('key,'b) map

val app : ('key * 'a -> unit) -> ('key,'a) map -> unit

val transform : ('a -> 'b) -> ('key,'a) map -> ('key,'b) map

val foldl : ('key * 'a * 's -> 's) -> 's -> ('key,'a) map -> 's

val foldr : ('key * 'a * 's -> 's) -> 's -> ('key,'a) map -> 's

val findl : ('key * 'a -> bool) -> ('key,'a) map -> ('key * 'a) option

val findr : ('key * 'a -> bool) -> ('key,'a) map -> ('key * 'a) option

val firstl : ('key * 'a -> 'b option) -> ('key,'a) map -> 'b option

val firstr : ('key * 'a -> 'b option) -> ('key,'a) map -> 'b option

val exists : ('key * 'a -> bool) -> ('key,'a) map -> bool

val all : ('key * 'a -> bool) -> ('key,'a) map -> bool

val domain : ('key,'a) map -> 'key list

val toList : ('key,'a) map -> ('key * 'a) list

val fromList : ('key * 'key -> order) -> ('key * 'a) list -> ('key,'a) map

val random : ('key,'a) map -> 'key * 'a  (* raises Empty *)

val compare : ('a * 'a -> order) -> ('key,'a) map * ('key,'a) map -> order

val equal : ('a -> 'a -> bool) -> ('key,'a) map -> ('key,'a) map -> bool

val toString : ('key,'a) map -> string

(* ------------------------------------------------------------------------- *)
(* Iterators over maps                                                       *)
(* ------------------------------------------------------------------------- *)

type ('key,'a) iterator

val mkIterator : ('key,'a) map -> ('key,'a) iterator option

val mkRevIterator : ('key,'a) map -> ('key,'a) iterator option

val readIterator : ('key,'a) iterator -> 'key * 'a

val advanceIterator : ('key,'a) iterator -> ('key,'a) iterator option

end

(**** Original file: RandomMap.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* FINITE MAPS IMPLEMENTED WITH RANDOMLY BALANCED TREES                      *)
(* Copyright (c) 2004-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure RandomMap :> Map =
struct

exception Bug = Useful.Bug;

exception Error = Useful.Error;

val pointerEqual = Portable.pointerEqual;

val K = Useful.K;

val snd = Useful.snd;

val randomInt = Portable.randomInt;

val randomWord = Portable.randomWord;

(* ------------------------------------------------------------------------- *)
(* Random search trees.                                                      *)
(* ------------------------------------------------------------------------- *)

type priority = Word.word;

datatype ('a,'b) tree =
    E
  | T of
    {size : int,
     priority : priority,
     left : ('a,'b) tree,
     key : 'a,
     value : 'b,
     right : ('a,'b) tree};

type ('a,'b) node =
     {size : int,
      priority : priority,
      left : ('a,'b) tree,
      key : 'a,
      value : 'b,
      right : ('a,'b) tree};

datatype ('a,'b) map = Map of ('a * 'a -> order) * ('a,'b) tree;

(* ------------------------------------------------------------------------- *)
(* Random priorities.                                                        *)
(* ------------------------------------------------------------------------- *)

local
  val randomPriority = randomWord;

  val priorityOrder = Word.compare;
in
  fun treeSingleton (key,value) =
      T {size = 1, priority = randomPriority (),
         left = E, key = key, value = value, right = E};

  fun nodePriorityOrder cmp (x1 : ('a,'b) node, x2 : ('a,'b) node) =
      let
        val {priority = p1, key = k1, ...} = x1
        and {priority = p2, key = k2, ...} = x2
      in
        case priorityOrder (p1,p2) of
          LESS => LESS
        | EQUAL => cmp (k1,k2)
        | GREATER => GREATER
      end;
end;

(* ------------------------------------------------------------------------- *)
(* Debugging functions.                                                      *)
(* ------------------------------------------------------------------------- *)

local
  fun checkSizes E = 0
    | checkSizes (T {size,left,right,...}) =
      let
        val l = checkSizes left
        and r = checkSizes right
        val () = if l + 1 + r = size then () else raise Error "wrong size"
      in
        size
      end;

  fun checkSorted _ x E = x
    | checkSorted cmp x (T {left,key,right,...}) =
      let
        val x = checkSorted cmp x left
        val () =
            case x of
              NONE => ()
            | SOME k =>
              case cmp (k,key) of
                LESS => ()
              | EQUAL => raise Error "duplicate keys"
              | GREATER => raise Error "unsorted"
      in
        checkSorted cmp (SOME key) right
      end;

  fun checkPriorities _ E = NONE
    | checkPriorities cmp (T (x as {left,right,...})) =
      let
        val () =
            case checkPriorities cmp left of
              NONE => ()
            | SOME l =>
              case nodePriorityOrder cmp (l,x) of
                LESS => ()
              | EQUAL => raise Error "left child has equal key"
              | GREATER => raise Error "left child has greater priority"
        val () =
            case checkPriorities cmp right of
              NONE => ()
            | SOME r =>
              case nodePriorityOrder cmp (r,x) of
                LESS => ()
              | EQUAL => raise Error "right child has equal key"
              | GREATER => raise Error "right child has greater priority"
      in
        SOME x
      end;
in
  fun checkWellformed s (m as Map (cmp,tree)) =
      (let
         val _ = checkSizes tree
         val _ = checkSorted cmp NONE tree
         val _ = checkPriorities cmp tree
       in
         m
       end
       handle Error err => raise Bug err)
      handle Bug bug => raise Bug (s ^ "\nRandomMap.checkWellformed: " ^ bug);
end;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

fun comparison (Map (cmp,_)) = cmp;

fun new cmp = Map (cmp,E);

fun treeSize E = 0
  | treeSize (T {size = s, ...}) = s;

fun size (Map (_,tree)) = treeSize tree;

fun mkT p l k v r =
    T {size = treeSize l + 1 + treeSize r, priority = p,
       left = l, key = k, value = v, right = r};

fun singleton cmp key_value = Map (cmp, treeSingleton key_value);

local
  fun treePeek cmp E pkey = NONE
    | treePeek cmp (T {left,key,value,right,...}) pkey =
      case cmp (pkey,key) of
        LESS => treePeek cmp left pkey
      | EQUAL => SOME value
      | GREATER => treePeek cmp right pkey
in
  fun peek (Map (cmp,tree)) key = treePeek cmp tree key;
end;

(* treeAppend assumes that every element of the first tree is less than *)
(* every element of the second tree. *)

fun treeAppend _ t1 E = t1
  | treeAppend _ E t2 = t2
  | treeAppend cmp (t1 as T x1) (t2 as T x2) =
    case nodePriorityOrder cmp (x1,x2) of
      LESS =>
      let
        val {priority = p2,
             left = l2, key = k2, value = v2, right = r2, ...} = x2
      in
        mkT p2 (treeAppend cmp t1 l2) k2 v2 r2
      end
    | EQUAL => raise Bug "RandomSet.treeAppend: equal keys"
    | GREATER =>
      let
        val {priority = p1,
             left = l1, key = k1, value = v1, right = r1, ...} = x1
      in
        mkT p1 l1 k1 v1 (treeAppend cmp r1 t2)
      end;

(* nodePartition splits the node into three parts: the keys comparing less *)
(* than the supplied key, an optional equal key, and the keys comparing *)
(* greater. *)

local
  fun mkLeft [] t = t
    | mkLeft (({priority,left,key,value,...} : ('a,'b) node) :: xs) t =
      mkLeft xs (mkT priority left key value t);

  fun mkRight [] t = t
    | mkRight (({priority,key,value,right,...} : ('a,'b) node) :: xs) t =
      mkRight xs (mkT priority t key value right);

  fun treePart _ _ lefts rights E = (mkLeft lefts E, NONE, mkRight rights E)
    | treePart cmp pkey lefts rights (T x) = nodePart cmp pkey lefts rights x
  and nodePart cmp pkey lefts rights (x as {left,key,value,right,...}) =
      case cmp (pkey,key) of
        LESS => treePart cmp pkey lefts (x :: rights) left
      | EQUAL => (mkLeft lefts left, SOME (key,value), mkRight rights right)
      | GREATER => treePart cmp pkey (x :: lefts) rights right;
in
  fun nodePartition cmp x pkey = nodePart cmp pkey [] [] x;
end;

(* union first calls treeCombineRemove, to combine the values *)
(* for equal keys into the first map and remove them from the second map. *)
(* Note that the combined key is always the one from the second map. *)

local
  fun treeCombineRemove _ _ t1 E = (t1,E)
    | treeCombineRemove _ _ E t2 = (E,t2)
    | treeCombineRemove cmp f (t1 as T x1) (t2 as T x2) =
      let
        val {priority = p1,
             left = l1, key = k1, value = v1, right = r1, ...} = x1
        val (l2,k2_v2,r2) = nodePartition cmp x2 k1
        val (l1,l2) = treeCombineRemove cmp f l1 l2
        and (r1,r2) = treeCombineRemove cmp f r1 r2
      in
        case k2_v2 of
          NONE =>
          if treeSize l2 + treeSize r2 = #size x2 then (t1,t2)
          else (mkT p1 l1 k1 v1 r1, treeAppend cmp l2 r2)
        | SOME (k2,v2) =>
          case f (v1,v2) of
            NONE => (treeAppend cmp l1 r1, treeAppend cmp l2 r2)
          | SOME v => (mkT p1 l1 k2 v r1, treeAppend cmp l2 r2)
      end;

  fun treeUnionDisjoint _ t1 E = t1
    | treeUnionDisjoint _ E t2 = t2
    | treeUnionDisjoint cmp (T x1) (T x2) =
      case nodePriorityOrder cmp (x1,x2) of
        LESS => nodeUnionDisjoint cmp x2 x1
      | EQUAL => raise Bug "RandomSet.unionDisjoint: equal keys"
      | GREATER => nodeUnionDisjoint cmp x1 x2
  and nodeUnionDisjoint cmp x1 x2 =
      let
        val {priority = p1,
             left = l1, key = k1, value = v1, right = r1, ...} = x1
        val (l2,_,r2) = nodePartition cmp x2 k1
        val l = treeUnionDisjoint cmp l1 l2
        and r = treeUnionDisjoint cmp r1 r2
      in
        mkT p1 l k1 v1 r
      end;
in
  fun union f (m1 as Map (cmp,t1)) (Map (_,t2)) =
      if pointerEqual (t1,t2) then m1
      else
        let
          val (t1,t2) = treeCombineRemove cmp f t1 t2
        in
          Map (cmp, treeUnionDisjoint cmp t1 t2)
        end;
end;

(*DEBUG
val union = fn f => fn t1 => fn t2 =>
    checkWellformed "RandomMap.union: result"
      (union f (checkWellformed "RandomMap.union: input 1" t1)
               (checkWellformed "RandomMap.union: input 2" t2));
*)

(* intersect is a simple case of the union algorithm. *)

local
  fun treeIntersect _ _ _ E = E
    | treeIntersect _ _ E _ = E
    | treeIntersect cmp f (t1 as T x1) (t2 as T x2) =
      let
        val {priority = p1,
             left = l1, key = k1, value = v1, right = r1, ...} = x1
        val (l2,k2_v2,r2) = nodePartition cmp x2 k1
        val l = treeIntersect cmp f l1 l2
        and r = treeIntersect cmp f r1 r2
      in
        case k2_v2 of
          NONE => treeAppend cmp l r
        | SOME (k2,v2) =>
          case f (v1,v2) of
            NONE => treeAppend cmp l r
          | SOME v => mkT p1 l k2 v r
      end;
in
  fun intersect f (m1 as Map (cmp,t1)) (Map (_,t2)) =
      if pointerEqual (t1,t2) then m1
      else Map (cmp, treeIntersect cmp f t1 t2);
end;

(*DEBUG
val intersect = fn f => fn t1 => fn t2 =>
    checkWellformed "RandomMap.intersect: result"
      (intersect f (checkWellformed "RandomMap.intersect: input 1" t1)
                   (checkWellformed "RandomMap.intersect: input 2" t2));
*)

(* delete raises an exception if the supplied key is not found, which *)
(* makes it simpler to maximize sharing. *)

local
  fun treeDelete _ E _ = raise Error "RandomMap.delete: element not found"
    | treeDelete cmp (T {priority,left,key,value,right,...}) dkey =
      case cmp (dkey,key) of
        LESS => mkT priority (treeDelete cmp left dkey) key value right
      | EQUAL => treeAppend cmp left right
      | GREATER => mkT priority left key value (treeDelete cmp right dkey);
in
  fun delete (Map (cmp,tree)) key = Map (cmp, treeDelete cmp tree key);
end;
 
(*DEBUG
val delete = fn t => fn x =>
    checkWellformed "RandomMap.delete: result"
      (delete (checkWellformed "RandomMap.delete: input" t) x);
*)

(* Set difference on domains *)

local
  fun treeDifference _ t1 E = t1
    | treeDifference _ E _ = E
    | treeDifference cmp (t1 as T x1) (T x2) =
      let
        val {size = s1, priority = p1,
             left = l1, key = k1, value = v1, right = r1} = x1
        val (l2,k2_v2,r2) = nodePartition cmp x2 k1
        val l = treeDifference cmp l1 l2
        and r = treeDifference cmp r1 r2
      in
        if Option.isSome k2_v2 then treeAppend cmp l r
        else if treeSize l + treeSize r + 1 = s1 then t1
        else mkT p1 l k1 v1 r
      end;
in
  fun difference (Map (cmp,tree1)) (Map (_,tree2)) =
      Map (cmp, treeDifference cmp tree1 tree2);
end;

(*DEBUG
val difference = fn t1 => fn t2 =>
    checkWellformed "RandomMap.difference: result"
      (difference (checkWellformed "RandomMap.difference: input 1" t1)
                  (checkWellformed "RandomMap.difference: input 2" t2));
*)

(* subsetDomain is mainly used when using maps as sets. *)

local
  fun treeSubsetDomain _ E _ = true
    | treeSubsetDomain _ _ E = false
    | treeSubsetDomain cmp (t1 as T x1) (T x2) =
      let
        val {size = s1, left = l1, key = k1, right = r1, ...} = x1
        and {size = s2, ...} = x2
      in
        s1 <= s2 andalso
        let
          val (l2,k2_v2,r2) = nodePartition cmp x2 k1
        in
          Option.isSome k2_v2 andalso
          treeSubsetDomain cmp l1 l2 andalso
          treeSubsetDomain cmp r1 r2
        end
      end;
in
  fun subsetDomain (Map (cmp,tree1)) (Map (_,tree2)) =
      pointerEqual (tree1,tree2) orelse
      treeSubsetDomain cmp tree1 tree2;
end;

(* Map equality *)

local
  fun treeEqual _ _ E E = true
    | treeEqual _ _ E _ = false
    | treeEqual _ _ _ E = false
    | treeEqual cmp veq (t1 as T x1) (T x2) =
      let
        val {size = s1, left = l1, key = k1, value = v1, right = r1, ...} = x1
        and {size = s2, ...} = x2
      in
        s1 = s2 andalso
        let
          val (l2,k2_v2,r2) = nodePartition cmp x2 k1
        in
          (case k2_v2 of NONE => false | SOME (_,v2) => veq v1 v2) andalso
          treeEqual cmp veq l1 l2 andalso
          treeEqual cmp veq r1 r2
        end
      end;
in
  fun equal veq (Map (cmp,tree1)) (Map (_,tree2)) =
      pointerEqual (tree1,tree2) orelse
      treeEqual cmp veq tree1 tree2;
end;

(* mapPartial is the basic function for preserving the tree structure. *)
(* It applies the argument function to the elements *in order*. *)

local
  fun treeMapPartial cmp _ E = E
    | treeMapPartial cmp f (T {priority,left,key,value,right,...}) =
      let
        val left = treeMapPartial cmp f left
        and value' = f (key,value)
        and right = treeMapPartial cmp f right
      in
        case value' of
          NONE => treeAppend cmp left right
        | SOME value => mkT priority left key value right
      end;
in
  fun mapPartial f (Map (cmp,tree)) = Map (cmp, treeMapPartial cmp f tree);
end;

(* map is a primitive function for efficiency reasons. *)
(* It also applies the argument function to the elements *in order*. *)

local
  fun treeMap _ E = E
    | treeMap f (T {size,priority,left,key,value,right}) =
      let
        val left = treeMap f left
        and value = f (key,value)
        and right = treeMap f right
      in
        T {size = size, priority = priority, left = left,
           key = key, value = value, right = right}
      end;
in
  fun map f (Map (cmp,tree)) = Map (cmp, treeMap f tree);
end;

(* nth picks the nth smallest key/value (counting from 0). *)

local
  fun treeNth E _ = raise Subscript
    | treeNth (T {left,key,value,right,...}) n =
      let
        val k = treeSize left
      in
        if n = k then (key,value)
        else if n < k then treeNth left n
        else treeNth right (n - (k + 1))
      end;
in
  fun nth (Map (_,tree)) n = treeNth tree n;
end;

(* ------------------------------------------------------------------------- *)
(* Iterators.                                                                *)
(* ------------------------------------------------------------------------- *)

fun leftSpine E acc = acc
  | leftSpine (t as T {left,...}) acc = leftSpine left (t :: acc);

fun rightSpine E acc = acc
  | rightSpine (t as T {right,...}) acc = rightSpine right (t :: acc);

datatype ('key,'a) iterator =
    LR of ('key * 'a) * ('key,'a) tree * ('key,'a) tree list
  | RL of ('key * 'a) * ('key,'a) tree * ('key,'a) tree list;

fun mkLR [] = NONE
  | mkLR (T {key,value,right,...} :: l) = SOME (LR ((key,value),right,l))
  | mkLR (E :: _) = raise Bug "RandomMap.mkLR";

fun mkRL [] = NONE
  | mkRL (T {key,value,left,...} :: l) = SOME (RL ((key,value),left,l))
  | mkRL (E :: _) = raise Bug "RandomMap.mkRL";

fun mkIterator (Map (_,tree)) = mkLR (leftSpine tree []);

fun mkRevIterator (Map (_,tree)) = mkRL (rightSpine tree []);

fun readIterator (LR (key_value,_,_)) = key_value
  | readIterator (RL (key_value,_,_)) = key_value;

fun advanceIterator (LR (_,next,l)) = mkLR (leftSpine next l)
  | advanceIterator (RL (_,next,l)) = mkRL (rightSpine next l);

(* ------------------------------------------------------------------------- *)
(* Derived operations.                                                       *)
(* ------------------------------------------------------------------------- *)

fun null m = size m = 0;

fun get m key =
    case peek m key of
      NONE => raise Error "RandomMap.get: element not found"
    | SOME value => value;

fun inDomain key m = Option.isSome (peek m key);

fun insert m key_value =
    union (SOME o snd) m (singleton (comparison m) key_value);

(*DEBUG
val insert = fn m => fn x =>
    checkWellformed "RandomMap.insert: result"
      (insert (checkWellformed "RandomMap.insert: input" m) x);
*)

local
  fun fold _ NONE acc = acc
    | fold f (SOME iter) acc =
      let
        val (key,value) = readIterator iter
      in
        fold f (advanceIterator iter) (f (key,value,acc))
      end;
in
  fun foldl f b m = fold f (mkIterator m) b;

  fun foldr f b m = fold f (mkRevIterator m) b;
end;

local
  fun find _ NONE = NONE
    | find pred (SOME iter) =
      let
        val key_value = readIterator iter
      in
        if pred key_value then SOME key_value
        else find pred (advanceIterator iter)
      end;
in
  fun findl p m = find p (mkIterator m);

  fun findr p m = find p (mkRevIterator m);
end;

local
  fun first _ NONE = NONE
    | first f (SOME iter) =
      let
        val key_value = readIterator iter
      in
        case f key_value of
          NONE => first f (advanceIterator iter)
        | s => s
      end;
in
  fun firstl f m = first f (mkIterator m);

  fun firstr f m = first f (mkRevIterator m);
end;

fun fromList cmp l = List.foldl (fn (k_v,m) => insert m k_v) (new cmp) l;

fun insertList m l = union (SOME o snd) m (fromList (comparison m) l);

fun filter p =
    let
      fun f (key_value as (_,value)) =
          if p key_value then SOME value else NONE
    in
      mapPartial f
    end;

fun app f m = foldl (fn (key,value,()) => f (key,value)) () m;

fun transform f = map (fn (_,value) => f value);

fun toList m = foldr (fn (key,value,l) => (key,value) :: l) [] m;

fun domain m = foldr (fn (key,_,l) => key :: l) [] m;

fun exists p m = Option.isSome (findl p m);

fun all p m = not (exists (not o p) m);

fun random m =
    case size m of
      0 => raise Error "RandomMap.random: empty"
    | n => nth m (randomInt n);

local
  fun iterCompare _ _ NONE NONE = EQUAL
    | iterCompare _ _ NONE (SOME _) = LESS
    | iterCompare _ _ (SOME _) NONE = GREATER
    | iterCompare kcmp vcmp (SOME i1) (SOME i2) =
      keyIterCompare kcmp vcmp (readIterator i1) (readIterator i2) i1 i2

  and keyIterCompare kcmp vcmp (k1,v1) (k2,v2) i1 i2 =
      case kcmp (k1,k2) of
        LESS => LESS
      | EQUAL =>
        (case vcmp (v1,v2) of
           LESS => LESS
         | EQUAL =>
           iterCompare kcmp vcmp (advanceIterator i1) (advanceIterator i2)
         | GREATER => GREATER)
      | GREATER => GREATER;
in
  fun compare vcmp (m1,m2) =
      if pointerEqual (m1,m2) then EQUAL
      else
        case Int.compare (size m1, size m2) of
          LESS => LESS
        | EQUAL =>
          iterCompare (comparison m1) vcmp (mkIterator m1) (mkIterator m2)
        | GREATER => GREATER;
end;

fun equalDomain m1 m2 = equal (K (K true)) m1 m2;

fun toString m = "<" ^ (if null m then "" else Int.toString (size m)) ^ ">";

end
end;

(**** Original file: Map.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* FINITE MAPS                                                               *)
(* Copyright (c) 2004-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Map = RandomMap;
end;

(**** Original file: KeyMap.sig ****)

(* ========================================================================= *)
(* FINITE MAPS WITH A FIXED KEY TYPE                                         *)
(* Copyright (c) 2004-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature KeyMap =
sig

type key

(* ------------------------------------------------------------------------- *)
(* Finite maps                                                               *)
(* ------------------------------------------------------------------------- *)

type 'a map

val new : unit -> 'a map

val null : 'a map -> bool

val size : 'a map -> int

val singleton : key * 'a -> 'a map

val inDomain : key -> 'a map -> bool

val peek : 'a map -> key -> 'a option

val insert : 'a map -> key * 'a -> 'a map

val insertList : 'a map -> (key * 'a) list -> 'a map

val get : 'a map -> key -> 'a  (* raises Error *)

(* Union and intersect prefer keys in the second map *)

val union : ('a * 'a -> 'a option) -> 'a map -> 'a map -> 'a map

val intersect : ('a * 'a -> 'a option) -> 'a map -> 'a map -> 'a map

val delete : 'a map -> key -> 'a map  (* raises Error *)

val difference : 'a map -> 'a map -> 'a map

val subsetDomain : 'a map -> 'a map -> bool

val equalDomain : 'a map -> 'a map -> bool

val mapPartial : (key * 'a -> 'b option) -> 'a map -> 'b map

val filter : (key * 'a -> bool) -> 'a map -> 'a map

val map : (key * 'a -> 'b) -> 'a map -> 'b map

val app : (key * 'a -> unit) -> 'a map -> unit

val transform : ('a -> 'b) -> 'a map -> 'b map

val foldl : (key * 'a * 's -> 's) -> 's -> 'a map -> 's

val foldr : (key * 'a * 's -> 's) -> 's -> 'a map -> 's

val findl : (key * 'a -> bool) -> 'a map -> (key * 'a) option

val findr : (key * 'a -> bool) -> 'a map -> (key * 'a) option

val firstl : (key * 'a -> 'b option) -> 'a map -> 'b option

val firstr : (key * 'a -> 'b option) -> 'a map -> 'b option

val exists : (key * 'a -> bool) -> 'a map -> bool

val all : (key * 'a -> bool) -> 'a map -> bool

val domain : 'a map -> key list

val toList : 'a map -> (key * 'a) list

val fromList : (key * 'a) list -> 'a map

val compare : ('a * 'a -> order) -> 'a map * 'a map -> order

val equal : ('a -> 'a -> bool) -> 'a map -> 'a map -> bool

val random : 'a map -> key * 'a  (* raises Empty *)

val toString : 'a map -> string

(* ------------------------------------------------------------------------- *)
(* Iterators over maps                                                       *)
(* ------------------------------------------------------------------------- *)

type 'a iterator

val mkIterator : 'a map -> 'a iterator option

val mkRevIterator : 'a map -> 'a iterator option

val readIterator : 'a iterator -> key * 'a

val advanceIterator : 'a iterator -> 'a iterator option

end

(**** Original file: KeyMap.sml ****)

(* ========================================================================= *)
(* FINITE MAPS WITH A FIXED KEY TYPE                                         *)
(* Copyright (c) 2004-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

functor KeyMap (Key : Ordered) :> KeyMap where type key = Key.t =
struct

 open Metis;

type key = Key.t;

(* ------------------------------------------------------------------------- *)
(* Finite maps                                                               *)
(* ------------------------------------------------------------------------- *)

type 'a map = (Key.t,'a) Map.map;

fun new () = Map.new Key.compare;

val null = Map.null;

val size = Map.size;

fun singleton key_value = Map.singleton Key.compare key_value;

val inDomain = Map.inDomain;

val peek = Map.peek;

val insert = Map.insert;

val insertList = Map.insertList;

val get = Map.get;

(* Both op union and intersect prefer keys in the second map *)

val op union = Map.union;

val intersect = Map.intersect;

val delete = Map.delete;

val difference = Map.difference;

val subsetDomain = Map.subsetDomain;

val equalDomain = Map.equalDomain;

val mapPartial = Map.mapPartial;

val filter = Map.filter;

val map = Map.map;

val app = Map.app;

val transform = Map.transform;

val foldl = Map.foldl;

val foldr = Map.foldr;

val findl = Map.findl;

val findr = Map.findr;

val firstl = Map.firstl;

val firstr = Map.firstr;

val exists = Map.exists;

val all = Map.all;

val domain = Map.domain;

val toList = Map.toList;

fun fromList l = Map.fromList Key.compare l;

val compare = Map.compare;

val equal = Map.equal;

val random = Map.random;

val toString = Map.toString;

(* ------------------------------------------------------------------------- *)
(* Iterators over maps                                                       *)
(* ------------------------------------------------------------------------- *)

type 'a iterator = (Key.t,'a) Map.iterator;

val mkIterator = Map.mkIterator;

val mkRevIterator = Map.mkRevIterator;

val readIterator = Map.readIterator;

val advanceIterator = Map.advanceIterator;

end

 structure Metis = struct open Metis

structure IntMap =
KeyMap (IntOrdered);

structure StringMap =
KeyMap (StringOrdered);

 end;

(**** Original file: Sharing.sig ****)

(* ========================================================================= *)
(* PRESERVING SHARING OF ML VALUES                                           *)
(* Copyright (c) 2005-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Sharing =
sig

(* ------------------------------------------------------------------------- *)
(* Pointer equality.                                                         *)
(* ------------------------------------------------------------------------- *)

val pointerEqual : 'a * 'a -> bool

(* ------------------------------------------------------------------------- *)
(* List operations.                                                          *)
(* ------------------------------------------------------------------------- *)

val map : ('a -> 'a) -> 'a list -> 'a list

val updateNth : int * 'a -> 'a list -> 'a list

val setify : ''a list -> ''a list

(* ------------------------------------------------------------------------- *)
(* Function caching.                                                         *)
(* ------------------------------------------------------------------------- *)

val cache : ('a * 'a -> order) -> ('a -> 'b) -> 'a -> 'b

(* ------------------------------------------------------------------------- *)
(* Hash consing.                                                             *)
(* ------------------------------------------------------------------------- *)

val hashCons : ('a * 'a -> order) -> 'a -> 'a

end

(**** Original file: Sharing.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* PRESERVING SHARING OF ML VALUES                                           *)
(* Copyright (c) 2005-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Sharing :> Sharing =
struct

infix ==

(* ------------------------------------------------------------------------- *)
(* Pointer equality.                                                         *)
(* ------------------------------------------------------------------------- *)

val pointerEqual = Portable.pointerEqual;

val op== = pointerEqual;

(* ------------------------------------------------------------------------- *)
(* List operations.                                                          *)
(* ------------------------------------------------------------------------- *)

fun map f =
    let
      fun m _ a_b [] = List.revAppend a_b
        | m ys a_b (x :: xs) =
          let
            val y = f x
            val ys = y :: ys
          in
            m ys (if x == y then a_b else (ys,xs)) xs
          end
    in
      fn l => m [] ([],l) l
    end;

fun updateNth (n,x) l =
    let
      val (a,b) = Useful.revDivide l n
    in
      case b of
        [] => raise Subscript
      | h :: t => if x == h then l else List.revAppend (a, x :: t)
    end;

fun setify l =
    let
      val l' = Useful.setify l
    in
      if length l' = length l then l else l'
    end;

(* ------------------------------------------------------------------------- *)
(* Function caching.                                                         *)
(* ------------------------------------------------------------------------- *)

fun cache cmp f =
    let
      val cache = Unsynchronized.ref (Map.new cmp)
    in
      fn a =>
         case Map.peek (!cache) a of
           SOME b => b
         | NONE =>
           let
             val b = f a
             val () = cache := Map.insert (!cache) (a,b)
           in
             b
           end
    end;

(* ------------------------------------------------------------------------- *)
(* Hash consing.                                                             *)
(* ------------------------------------------------------------------------- *)

fun hashCons cmp = cache cmp Useful.I;

end
end;

(**** Original file: Stream.sig ****)

(* ========================================================================= *)
(* A POSSIBLY-INFINITE STREAM DATATYPE FOR ML                                *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Stream =
sig

(* ------------------------------------------------------------------------- *)
(* The stream type                                                           *)
(* ------------------------------------------------------------------------- *)

datatype 'a stream = NIL | CONS of 'a * (unit -> 'a stream)

(* If you're wondering how to create an infinite stream: *)
(* val stream4 = let fun s4 () = Metis.Stream.CONS (4,s4) in s4 () end; *)

(* ------------------------------------------------------------------------- *)
(* Stream constructors                                                       *)
(* ------------------------------------------------------------------------- *)

val repeat : 'a -> 'a stream

val count : int -> int stream

val funpows : ('a -> 'a) -> 'a -> 'a stream

(* ------------------------------------------------------------------------- *)
(* Stream versions of standard list operations: these should all terminate   *)
(* ------------------------------------------------------------------------- *)

val cons : 'a -> (unit -> 'a stream) -> 'a stream

val null : 'a stream -> bool

val hd : 'a stream -> 'a  (* raises Empty *)

val tl : 'a stream -> 'a stream  (* raises Empty *)

val hdTl : 'a stream -> 'a * 'a stream  (* raises Empty *)

val singleton : 'a -> 'a stream

val append : 'a stream -> (unit -> 'a stream) -> 'a stream

val map : ('a -> 'b) -> 'a stream -> 'b stream

val maps : ('a -> 's -> 'b * 's) -> 's -> 'a stream -> 'b stream

val zipwith : ('a -> 'b -> 'c) -> 'a stream -> 'b stream -> 'c stream

val zip : 'a stream -> 'b stream -> ('a * 'b) stream

val take : int -> 'a stream -> 'a stream  (* raises Subscript *)

val drop : int -> 'a stream -> 'a stream  (* raises Subscript *)

(* ------------------------------------------------------------------------- *)
(* Stream versions of standard list operations: these might not terminate    *)
(* ------------------------------------------------------------------------- *)

val length : 'a stream -> int

val exists : ('a -> bool) -> 'a stream -> bool

val all : ('a -> bool) -> 'a stream -> bool

val filter : ('a -> bool) -> 'a stream -> 'a stream

val foldl : ('a * 's -> 's) -> 's -> 'a stream -> 's

val concat : 'a stream stream -> 'a stream

val mapPartial : ('a -> 'b option) -> 'a stream -> 'b stream

val mapsPartial : ('a -> 's -> 'b option * 's) -> 's -> 'a stream -> 'b stream

(* ------------------------------------------------------------------------- *)
(* Stream operations                                                         *)
(* ------------------------------------------------------------------------- *)

val memoize : 'a stream -> 'a stream

val toList : 'a stream -> 'a list

val fromList : 'a list -> 'a stream

val toString : char stream -> string

val fromString : string -> char stream

val toTextFile : {filename : string} -> string stream -> unit

val fromTextFile : {filename : string} -> string stream  (* line by line *)

end

(**** Original file: Stream.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* A POSSIBLY-INFINITE STREAM DATATYPE FOR ML                                *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Stream :> Stream =
struct

val K = Useful.K;

val pair = Useful.pair;

val funpow = Useful.funpow;

(* ------------------------------------------------------------------------- *)
(* The datatype declaration encapsulates all the primitive operations        *)
(* ------------------------------------------------------------------------- *)

datatype 'a stream =
    NIL
  | CONS of 'a * (unit -> 'a stream);

(* ------------------------------------------------------------------------- *)
(* Stream constructors                                                       *)
(* ------------------------------------------------------------------------- *)

fun repeat x = let fun rep () = CONS (x,rep) in rep () end;

fun count n = CONS (n, fn () => count (n + 1));

fun funpows f x = CONS (x, fn () => funpows f (f x));

(* ------------------------------------------------------------------------- *)
(* Stream versions of standard list operations: these should all terminate   *)
(* ------------------------------------------------------------------------- *)

fun cons h t = CONS (h,t);

fun null NIL = true | null (CONS _) = false;

fun hd NIL = raise Empty
  | hd (CONS (h,_)) = h;

fun tl NIL = raise Empty
  | tl (CONS (_,t)) = t ();

fun hdTl s = (hd s, tl s);

fun singleton s = CONS (s, K NIL);

fun append NIL s = s ()
  | append (CONS (h,t)) s = CONS (h, fn () => append (t ()) s);

fun map f =
    let
      fun m NIL = NIL
        | m (CONS (h, t)) = CONS (f h, fn () => m (t ()))
    in
      m
    end;

fun maps f =
    let
      fun mm _ NIL = NIL
        | mm s (CONS (x, xs)) =
          let
            val (y, s') = f x s
          in
            CONS (y, fn () => mm s' (xs ()))
          end
    in
      mm
    end;

fun zipwith f =
    let
      fun z NIL _ = NIL
        | z _ NIL = NIL
        | z (CONS (x,xs)) (CONS (y,ys)) =
          CONS (f x y, fn () => z (xs ()) (ys ()))
    in
      z
    end;

fun zip s t = zipwith pair s t;

fun take 0 _ = NIL
  | take n NIL = raise Subscript
  | take 1 (CONS (x,_)) = CONS (x, K NIL)
  | take n (CONS (x,xs)) = CONS (x, fn () => take (n - 1) (xs ()));

fun drop n s = funpow n tl s handle Empty => raise Subscript;

(* ------------------------------------------------------------------------- *)
(* Stream versions of standard list operations: these might not terminate    *)
(* ------------------------------------------------------------------------- *)

local
  fun len n NIL = n
    | len n (CONS (_,t)) = len (n + 1) (t ());
in
  fun length s = len 0 s;
end;

fun exists pred =
    let
      fun f NIL = false
        | f (CONS (h,t)) = pred h orelse f (t ())
    in
      f
    end;

fun all pred = not o exists (not o pred);

fun filter p NIL = NIL
  | filter p (CONS (x,xs)) =
    if p x then CONS (x, fn () => filter p (xs ())) else filter p (xs ());

fun foldl f =
    let
      fun fold b NIL = b
        | fold b (CONS (h,t)) = fold (f (h,b)) (t ())
    in
      fold
    end;

fun concat NIL = NIL
  | concat (CONS (NIL, ss)) = concat (ss ())
  | concat (CONS (CONS (x, xs), ss)) =
    CONS (x, fn () => concat (CONS (xs (), ss)));

fun mapPartial f =
    let
      fun mp NIL = NIL
        | mp (CONS (h,t)) =
          case f h of
            NONE => mp (t ())
          | SOME h' => CONS (h', fn () => mp (t ()))
    in
      mp
    end;

fun mapsPartial f =
    let
      fun mm _ NIL = NIL
        | mm s (CONS (x, xs)) =
          let
            val (yo, s') = f x s
            val t = mm s' o xs
          in
            case yo of NONE => t () | SOME y => CONS (y, t)
          end
    in
      mm
    end;

(* ------------------------------------------------------------------------- *)
(* Stream operations                                                         *)
(* ------------------------------------------------------------------------- *)

fun memoize NIL = NIL
  | memoize (CONS (h,t)) = CONS (h, Lazy.memoize (fn () => memoize (t ())));

local
  fun toLst res NIL = rev res
    | toLst res (CONS (x, xs)) = toLst (x :: res) (xs ());
in
  fun toList s = toLst [] s;
end;

fun fromList [] = NIL
  | fromList (x :: xs) = CONS (x, fn () => fromList xs);

fun toString s = implode (toList s);

fun fromString s = fromList (explode s);

fun toTextFile {filename = f} s =
    let
      val (h,close) =
          if f = "-" then (TextIO.stdOut, K ())
          else (TextIO.openOut f, TextIO.closeOut)

      fun toFile NIL = ()
        | toFile (CONS (x,y)) = (TextIO.output (h,x); toFile (y ()))

      val () = toFile s
    in
      close h
    end;

fun fromTextFile {filename = f} =
    let
      val (h,close) =
          if f = "-" then (TextIO.stdIn, K ())
          else (TextIO.openIn f, TextIO.closeIn)

      fun strm () =
          case TextIO.inputLine h of
            NONE => (close h; NIL)
          | SOME s => CONS (s,strm)
    in
      memoize (strm ())
    end;

end
end;

(**** Original file: Heap.sig ****)

(* ========================================================================= *)
(* A HEAP DATATYPE FOR ML                                                    *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Heap =
sig

type 'a heap

val new : ('a * 'a -> order) -> 'a heap

val add : 'a heap -> 'a -> 'a heap

val null : 'a heap -> bool

val top : 'a heap -> 'a  (* raises Empty *)

val remove : 'a heap -> 'a * 'a heap  (* raises Empty *)

val size : 'a heap -> int

val app : ('a -> unit) -> 'a heap -> unit

val toList : 'a heap -> 'a list

val toStream : 'a heap -> 'a Metis.Stream.stream

val toString : 'a heap -> string

end

(**** Original file: Heap.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* A HEAP DATATYPE FOR ML                                                    *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Heap :> Heap =
struct

(* Leftist heaps as in Purely Functional Data Structures, by Chris Okasaki *)

datatype 'a node = E | T of int * 'a * 'a node * 'a node;

datatype 'a heap = Heap of ('a * 'a -> order) * int * 'a node;

fun rank E = 0
  | rank (T (r,_,_,_)) = r;

fun makeT (x,a,b) =
  if rank a >= rank b then T (rank b + 1, x, a, b) else T (rank a + 1, x, b, a);

fun merge cmp =
    let
      fun mrg (h,E) = h
        | mrg (E,h) = h
        | mrg (h1 as T (_,x,a1,b1), h2 as T (_,y,a2,b2)) =
          case cmp (x,y) of
            GREATER => makeT (y, a2, mrg (h1,b2))
          | _ => makeT (x, a1, mrg (b1,h2))
    in
      mrg
    end;

fun new cmp = Heap (cmp,0,E);

fun add (Heap (f,n,a)) x = Heap (f, n + 1, merge f (T (1,x,E,E), a));

fun size (Heap (_, n, _)) = n;

fun null h = size h = 0;

fun top (Heap (_,_,E)) = raise Empty
  | top (Heap (_, _, T (_,x,_,_))) = x;

fun remove (Heap (_,_,E)) = raise Empty
  | remove (Heap (f, n, T (_,x,a,b))) = (x, Heap (f, n - 1, merge f (a,b)));

fun app f =
    let
      fun ap [] = ()
        | ap (E :: rest) = ap rest
        | ap (T (_,d,a,b) :: rest) = (f d; ap (a :: b :: rest))
    in
      fn Heap (_,_,a) => ap [a]
    end;

fun toList h =
    if null h then []
    else
      let
        val (x,h) = remove h
      in
        x :: toList h
      end;

fun toStream h =
    if null h then Stream.NIL
    else
      let
        val (x,h) = remove h
      in
        Stream.CONS (x, fn () => toStream h)
      end;

fun toString h =
    "Heap[" ^ (if null h then "" else Int.toString (size h)) ^ "]";

end
end;

(**** Original file: Parser.sig ****)

(* ========================================================================= *)
(* PARSING AND PRETTY PRINTING                                               *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Parser =
sig

(* ------------------------------------------------------------------------- *)
(* Pretty printing for built-in types                                        *)
(* ------------------------------------------------------------------------- *)

type ppstream = Metis.PP.ppstream

datatype breakStyle = Consistent | Inconsistent

type 'a pp = ppstream -> 'a -> unit

val lineLength : int Unsynchronized.ref

val beginBlock : ppstream -> breakStyle -> int -> unit

val endBlock : ppstream -> unit

val addString : ppstream -> string -> unit

val addBreak : ppstream -> int * int -> unit

val addNewline : ppstream -> unit

val ppMap : ('a -> 'b) -> 'b pp -> 'a pp

val ppBracket : string -> string -> 'a pp -> 'a pp

val ppSequence : string -> 'a pp -> 'a list pp

val ppBinop : string -> 'a pp -> 'b pp -> ('a * 'b) pp

val ppChar : char pp

val ppString : string pp

val ppUnit : unit pp

val ppBool : bool pp

val ppInt : int pp

val ppReal : real pp

val ppOrder : order pp

val ppList : 'a pp -> 'a list pp

val ppOption : 'a pp -> 'a option pp

val ppPair : 'a pp -> 'b pp -> ('a * 'b) pp

val ppTriple : 'a pp -> 'b pp -> 'c pp -> ('a * 'b * 'c) pp

val toString : 'a pp -> 'a -> string  (* Uses !lineLength *)

val fromString : ('a -> string) -> 'a pp

val ppTrace : 'a pp -> string -> 'a -> unit

(* ------------------------------------------------------------------------- *)
(* Recursive descent parsing combinators                                     *)
(* ------------------------------------------------------------------------- *)

(* Generic parsers

Recommended fixities:
  infixr 9 >>++
  infixr 8 ++
  infixr 7 >>
  infixr 6 ||
*)

exception NoParse

val error : 'a -> 'b * 'a

val ++ : ('a -> 'b * 'a) * ('a -> 'c * 'a) -> 'a -> ('b * 'c) * 'a

val >> : ('a -> 'b * 'a) * ('b -> 'c) -> 'a -> 'c * 'a

val >>++ : ('a -> 'b * 'a) * ('b -> 'a -> 'c * 'a) -> 'a -> 'c * 'a

val || : ('a -> 'b * 'a) * ('a -> 'b * 'a) -> 'a -> 'b * 'a

val first : ('a -> 'b * 'a) list -> 'a -> 'b * 'a

val mmany : ('s -> 'a -> 's * 'a) -> 's -> 'a -> 's * 'a

val many : ('a -> 'b * 'a) -> 'a -> 'b list * 'a

val atLeastOne : ('a -> 'b * 'a) -> 'a -> 'b list * 'a

val nothing : 'a -> unit * 'a

val optional : ('a -> 'b * 'a) -> 'a -> 'b option * 'a

(* Stream based parsers *)

type ('a,'b) parser = 'a Metis.Stream.stream -> 'b * 'a Metis.Stream.stream

val everything : ('a, 'b list) parser -> 'a Metis.Stream.stream -> 'b Metis.Stream.stream

val maybe : ('a -> 'b option) -> ('a,'b) parser

val finished : ('a,unit) parser

val some : ('a -> bool) -> ('a,'a) parser

val any : ('a,'a) parser

val exact : ''a -> (''a,''a) parser

(* ------------------------------------------------------------------------- *)
(* Infix operators                                                           *)
(* ------------------------------------------------------------------------- *)

type infixities = {token : string, precedence : int, leftAssoc : bool} list

val infixTokens : infixities -> string list

val parseInfixes :
    infixities -> (string * 'a * 'a -> 'a) -> (string,'a) parser ->
    (string,'a) parser

val ppInfixes :
    infixities -> ('a -> (string * 'a * 'a) option) -> ('a * bool) pp ->
    ('a * bool) pp

(* ------------------------------------------------------------------------- *)
(* Quotations                                                                *)
(* ------------------------------------------------------------------------- *)

type 'a quotation = 'a Metis.frag list

val parseQuotation : ('a -> string) -> (string -> 'b) -> 'a quotation -> 'b

end

(**** Original file: Parser.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* PARSER COMBINATORS                                                        *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Parser :> Parser =
struct

infixr 9 >>++
infixr 8 ++
infixr 7 >>
infixr 6 ||

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

exception Bug = Useful.Bug;

val trace = Useful.trace
and equal = Useful.equal
and I = Useful.I
and K = Useful.K
and C = Useful.C
and fst = Useful.fst
and snd = Useful.snd
and pair = Useful.pair
and curry = Useful.curry
and funpow = Useful.funpow
and mem = Useful.mem
and sortMap = Useful.sortMap;

(* ------------------------------------------------------------------------- *)
(* Pretty printing for built-in types                                        *)
(* ------------------------------------------------------------------------- *)

type ppstream = PP.ppstream

datatype breakStyle = Consistent | Inconsistent

type 'a pp = PP.ppstream -> 'a -> unit;

val lineLength = Unsynchronized.ref 75;

fun beginBlock pp Consistent = PP.begin_block pp PP.CONSISTENT
  | beginBlock pp Inconsistent = PP.begin_block pp PP.INCONSISTENT;

val endBlock = PP.end_block
and addString = PP.add_string
and addBreak = PP.add_break
and addNewline = PP.add_newline;

fun ppMap f ppA (ppstrm : PP.ppstream) x : unit = ppA ppstrm (f x);

fun ppBracket l r ppA pp a =
    let
      val ln = size l
    in
      beginBlock pp Inconsistent ln;
      if ln = 0 then () else addString pp l;
      ppA pp a;
      if r = "" then () else addString pp r;
      endBlock pp
    end;

fun ppSequence sep ppA pp =
    let
      fun ppX x = (addString pp sep; addBreak pp (1,0); ppA pp x)
    in
      fn [] => ()
       | h :: t =>
         (beginBlock pp Inconsistent 0;
          ppA pp h;
          app ppX t;
          endBlock pp)
    end;

fun ppBinop s ppA ppB pp (a,b) =
    (beginBlock pp Inconsistent 0;
      ppA pp a;
      if s = "" then () else addString pp s;
      addBreak pp (1,0);
      ppB pp b;
      endBlock pp);

fun ppTrinop ab bc ppA ppB ppC pp (a,b,c) =
    (beginBlock pp Inconsistent 0;
     ppA pp a;
     if ab = "" then () else addString pp ab;
     addBreak pp (1,0);
     ppB pp b;
     if bc = "" then () else addString pp bc;
     addBreak pp (1,0);
     ppC pp c;
     endBlock pp);

(* Pretty-printers for common types *)

fun ppString pp s =
    (beginBlock pp Inconsistent 0;
     addString pp s;
     endBlock pp);

val ppUnit = ppMap (fn () => "()") ppString;

val ppChar = ppMap str ppString;

val ppBool = ppMap (fn true => "true" | false => "false") ppString;

val ppInt = ppMap Int.toString ppString;

val ppReal = ppMap Real.toString ppString;

val ppOrder =
    let
      fun f LESS = "Less"
        | f EQUAL = "Equal"
        | f GREATER = "Greater"
    in
      ppMap f ppString
    end;

fun ppList ppA = ppBracket "[" "]" (ppSequence "," ppA);

fun ppOption _ pp NONE = ppString pp "-"
  | ppOption ppA pp (SOME a) = ppA pp a;

fun ppPair ppA ppB = ppBracket "(" ")" (ppBinop "," ppA ppB);

fun ppTriple ppA ppB ppC = ppBracket "(" ")" (ppTrinop "," "," ppA ppB ppC);

(* Keep eta expanded to evaluate lineLength when supplied with a *)
fun toString ppA a = PP.pp_to_string (!lineLength) ppA a;

fun fromString toS = ppMap toS ppString;

fun ppTrace ppX nameX x =
    trace (toString (ppBinop " =" ppString ppX) (nameX,x) ^ "\n");

(* ------------------------------------------------------------------------- *)
(* Generic.                                                                  *)
(* ------------------------------------------------------------------------- *)

exception NoParse;

val error : 'a -> 'b * 'a = fn _ => raise NoParse;

fun op ++ (parser1,parser2) input =
    let
      val (result1,input) = parser1 input
      val (result2,input) = parser2 input
    in
      ((result1,result2),input)
    end;

fun op >> (parser : 'a -> 'b * 'a, treatment) input =
    let
      val (result,input) = parser input
    in
      (treatment result, input)
    end;

fun op >>++ (parser,treatment) input =
    let
      val (result,input) = parser input
    in
      treatment result input
    end;

fun op || (parser1,parser2) input =
    parser1 input handle NoParse => parser2 input;

fun first [] _ = raise NoParse
  | first (parser :: parsers) input = (parser || first parsers) input;

fun mmany parser state input =
    let
      val (state,input) = parser state input
    in
      mmany parser state input
    end
    handle NoParse => (state,input);

fun many parser =
    let
      fun sparser l = parser >> (fn x => x :: l)
    in
      mmany sparser [] >> rev      
    end;

fun atLeastOne p = (p ++ many p) >> op::;

fun nothing input = ((),input);

fun optional p = (p >> SOME) || (nothing >> K NONE);

(* ------------------------------------------------------------------------- *)
(* Stream-based.                                                             *)
(* ------------------------------------------------------------------------- *)

type ('a,'b) parser = 'a Stream.stream -> 'b * 'a Stream.stream

fun everything parser =
    let
      fun f input =
          let
            val (result,input) = parser input
          in
            Stream.append (Stream.fromList result) (fn () => f input)
          end
          handle NoParse =>
            if Stream.null input then Stream.NIL else raise NoParse
    in
      f
    end;

fun maybe p Stream.NIL = raise NoParse
  | maybe p (Stream.CONS (h,t)) =
    case p h of SOME r => (r, t ()) | NONE => raise NoParse;

fun finished Stream.NIL = ((), Stream.NIL)
  | finished (Stream.CONS _) = raise NoParse;

fun some p = maybe (fn x => if p x then SOME x else NONE);

fun any input = some (K true) input;

fun exact tok = some (fn item => item = tok);

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty-printing for infix operators.                          *)
(* ------------------------------------------------------------------------- *)

type infixities = {token : string, precedence : int, leftAssoc : bool} list;

local
  fun unflatten ({token,precedence,leftAssoc}, ([],_)) =
      ([(leftAssoc, [token])], precedence)
    | unflatten ({token,precedence,leftAssoc}, ((a,l) :: dealt, p)) =
      if p = precedence then
        let
          val _ = leftAssoc = a orelse
                  raise Bug "infix parser/printer: mixed assocs"
        in
          ((a, token :: l) :: dealt, p)
        end
      else
        ((leftAssoc,[token]) :: (a,l) :: dealt, precedence);
in
  fun layerOps infixes =
      let
        val infixes = sortMap #precedence Int.compare infixes
        val (parsers,_) = foldl unflatten ([],0) infixes
      in
        parsers
      end;
end;

local
  fun chop (#" " :: chs) = let val (n,l) = chop chs in (n + 1, l) end
    | chop chs = (0,chs);

  fun nspaces n = funpow n (curry op^ " ") "";

  fun spacify tok =
      let
        val chs = explode tok
        val (r,chs) = chop (rev chs)
        val (l,chs) = chop (rev chs)
      in
        ((l,r), implode chs)
      end;

  fun lrspaces (l,r) =
      (if l = 0 then K () else C addString (nspaces l),
       if r = 0 then K () else C addBreak (r, 0));
in
  fun opSpaces s = let val (l_r,s) = spacify s in (lrspaces l_r, s) end;

  val opClean = snd o spacify;
end;

val infixTokens : infixities -> string list =
    List.map (fn {token,...} => opClean token);

fun parseGenInfix update sof toks parse inp =
    let
      val (e, rest) = parse inp
                      
      val continue =
          case rest of
            Stream.NIL => NONE
          | Stream.CONS (h, t) => if mem h toks then SOME (h, t) else NONE
    in
      case continue of
        NONE => (sof e, rest)
      | SOME (h,t) => parseGenInfix update (update sof h e) toks parse (t ())
    end;

fun parseLeftInfix toks con =
    parseGenInfix (fn f => fn t => fn a => fn b => con (t, f a, b)) I toks;

fun parseRightInfix toks con =
    parseGenInfix (fn f => fn t => fn a => fn b => f (con (t, a, b))) I toks;

fun parseInfixes ops =
    let
      fun layeredOp (x,y) = (x, List.map opClean y)

      val layeredOps = List.map layeredOp (layerOps ops)

      fun iparser (a,t) = (if a then parseLeftInfix else parseRightInfix) t

      val iparsers = List.map iparser layeredOps
    in
      fn con => fn subparser => foldl (fn (p,sp) => p con sp) subparser iparsers
    end;

fun ppGenInfix left toks =
    let
      val spc = List.map opSpaces toks
    in
      fn dest => fn ppSub =>
      let
        fun dest' tm =
            case dest tm of
              NONE => NONE
            | SOME (t, a, b) =>
              Option.map (pair (a,b)) (List.find (equal t o snd) spc)

        open PP

        fun ppGo pp (tmr as (tm,r)) =
            case dest' tm of
              NONE => ppSub pp tmr
            | SOME ((a,b),((lspc,rspc),tok)) =>
              ((if left then ppGo else ppSub) pp (a,true);
               lspc pp; addString pp tok; rspc pp;
               (if left then ppSub else ppGo) pp (b,r))
      in
        fn pp => fn tmr as (tm,_) =>
        case dest' tm of
          NONE => ppSub pp tmr
        | SOME _ => (beginBlock pp Inconsistent 0; ppGo pp tmr; endBlock pp)
      end
    end;

fun ppLeftInfix toks = ppGenInfix true toks;

fun ppRightInfix toks = ppGenInfix false toks;

fun ppInfixes ops =
    let
      val layeredOps = layerOps ops
                       
      val toks = List.concat (List.map (List.map opClean o snd) layeredOps)
                 
      fun iprinter (a,t) = (if a then ppLeftInfix else ppRightInfix) t
                           
      val iprinters = List.map iprinter layeredOps
    in
      fn dest => fn ppSub =>
      let
        fun printer sub = foldl (fn (ip,p) => ip dest p) sub iprinters

        fun isOp t = case dest t of SOME (x,_,_) => mem x toks | _ => false

        open PP

        fun subpr pp (tmr as (tm,_)) =
            if isOp tm then
              (beginBlock pp Inconsistent 1; addString pp "(";
               printer subpr pp (tm, false); addString pp ")"; endBlock pp)
            else ppSub pp tmr
      in
        fn pp => fn tmr =>
        (beginBlock pp Inconsistent 0; printer subpr pp tmr; endBlock pp)
      end
    end;

(* ------------------------------------------------------------------------- *)
(* Quotations                                                                *)
(* ------------------------------------------------------------------------- *)

type 'a quotation = 'a frag list;

fun parseQuotation printer parser quote =
  let
    fun expand (QUOTE q, s) = s ^ q
      | expand (ANTIQUOTE a, s) = s ^ printer a

    val string = foldl expand "" quote
  in
    parser string
  end;

end
end;

(**** Original file: Options.sig ****)

(* ========================================================================= *)
(* PROCESSING COMMAND LINE OPTIONS                                           *)
(* Copyright (c) 2003-2004 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Options =
sig

(* ------------------------------------------------------------------------- *)
(* Option processors take an option with its associated arguments.           *)
(* ------------------------------------------------------------------------- *)

type proc = string * string list -> unit

type ('a,'x) mkProc = ('x -> proc) -> ('a -> 'x) -> proc

(* ------------------------------------------------------------------------- *)
(* One command line option: names, arguments, description and a processor.   *)
(* ------------------------------------------------------------------------- *)

type opt =
     {switches : string list, arguments : string list,
      description : string, processor : proc}

(* ------------------------------------------------------------------------- *)
(* Option processors may raise an OptionExit exception.                      *)
(* ------------------------------------------------------------------------- *)

type optionExit = {message : string option, usage : bool, success : bool}

exception OptionExit of optionExit

(* ------------------------------------------------------------------------- *)
(* Constructing option processors.                                           *)
(* ------------------------------------------------------------------------- *)

val beginOpt : (string,'x) mkProc

val endOpt : unit -> proc

val stringOpt : (string,'x) mkProc

val intOpt : int option * int option -> (int,'x) mkProc

val realOpt : real option * real option -> (real,'x) mkProc

val enumOpt : string list -> (string,'x) mkProc

val optionOpt : string * ('a,'x) mkProc -> ('a option,'x) mkProc

(* ------------------------------------------------------------------------- *)
(* Basic options useful for all programs.                                    *)
(* ------------------------------------------------------------------------- *)

val basicOptions : opt list

(* ------------------------------------------------------------------------- *)
(* All the command line options of a program.                                *)
(* ------------------------------------------------------------------------- *)

type allOptions =
     {name : string, version : string, header : string,
      footer : string, options : opt list}

(* ------------------------------------------------------------------------- *)
(* Usage information.                                                        *)
(* ------------------------------------------------------------------------- *)

val versionInformation : allOptions -> string

val usageInformation : allOptions -> string

(* ------------------------------------------------------------------------- *)
(* Exit the program gracefully.                                              *)
(* ------------------------------------------------------------------------- *)

val exit : allOptions -> optionExit -> 'exit

val succeed : allOptions -> 'exit

val fail : allOptions -> string -> 'exit

val usage : allOptions -> string -> 'exit

val version : allOptions -> 'exit

(* ------------------------------------------------------------------------- *)
(* Process the command line options passed to the program.                   *)
(* ------------------------------------------------------------------------- *)

val processOptions : allOptions -> string list -> string list * string list

end

(**** Original file: Options.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* PROCESSING COMMAND LINE OPTIONS                                           *)
(* Copyright (c) 2003-2004 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Options :> Options =
struct

infix ##

open Useful;

(* ------------------------------------------------------------------------- *)
(* One command line option: names, arguments, description and a processor    *)
(* ------------------------------------------------------------------------- *)

type proc = string * string list -> unit;

type ('a,'x) mkProc = ('x -> proc) -> ('a -> 'x) -> proc;

type opt = {switches : string list, arguments : string list,
            description : string, processor : proc};

(* ------------------------------------------------------------------------- *)
(* Option processors may raise an OptionExit exception                       *)
(* ------------------------------------------------------------------------- *)

type optionExit = {message : string option, usage : bool, success : bool};

exception OptionExit of optionExit;

(* ------------------------------------------------------------------------- *)
(* Wrappers for option processors                                            *)
(* ------------------------------------------------------------------------- *)

fun beginOpt f p (s : string, l : string list) : unit = f (p s) (s,l);

fun endOpt () (_ : string, [] : string list) = ()
  | endOpt _ (_, _ :: _) = raise Bug "endOpt";

fun stringOpt _ _ (_ : string, []) = raise Bug "stringOpt"
  | stringOpt f p (s, (h : string) :: t) : unit = f (p h) (s,t);

local
  fun range NONE NONE = "Z"
    | range (SOME i) NONE = "{n IN Z | " ^ Int.toString i ^ " <= n}"
    | range NONE (SOME j) = "{n IN Z | n <= " ^ Int.toString j ^ "}"
    | range (SOME i) (SOME j) =
    "{n IN Z | " ^ Int.toString i ^ " <= n <= " ^ Int.toString j ^ "}";
  fun oLeq (SOME x) (SOME y) = x <= y | oLeq _ _ = true;
  fun argToInt arg omin omax x =
    (case Int.fromString x of
       SOME i =>
       if oLeq omin (SOME i) andalso oLeq (SOME i) omax then i else
         raise OptionExit
           {success = false, usage = false, message =
            SOME (arg ^ " option needs an integer argument in the range "
                  ^ range omin omax ^ " (not " ^ x ^ ")")}
     | NONE =>
       raise OptionExit
         {success = false, usage = false, message =
          SOME (arg ^ " option needs an integer argument (not \"" ^ x ^ "\")")})
    handle Overflow =>
       raise OptionExit
         {success = false, usage = false, message =
          SOME (arg ^ " option suffered integer overflow on argument " ^ x)};
in
  fun intOpt _ _ _ (_,[]) = raise Bug "intOpt"
    | intOpt (omin,omax) f p (s:string, h :: (t : string list)) : unit =
      f (p (argToInt s omin omax h)) (s,t);
end;

local
  fun range NONE NONE = "R"
    | range (SOME i) NONE = "{n IN R | " ^ Real.toString i ^ " <= n}"
    | range NONE (SOME j) = "{n IN R | n <= " ^ Real.toString j ^ "}"
    | range (SOME i) (SOME j) =
    "{n IN R | " ^ Real.toString i ^ " <= n <= " ^ Real.toString j ^ "}";
  fun oLeq (SOME (x:real)) (SOME y) = x <= y | oLeq _ _ = true;
  fun argToReal arg omin omax x =
    (case Real.fromString x of
       SOME i =>
       if oLeq omin (SOME i) andalso oLeq (SOME i) omax then i else
         raise OptionExit
           {success = false, usage = false, message =
            SOME (arg ^ " option needs an real argument in the range "
                  ^ range omin omax ^ " (not " ^ x ^ ")")}
     | NONE =>
       raise OptionExit
         {success = false, usage = false, message =
          SOME (arg ^ " option needs an real argument (not \"" ^ x ^ "\")")})
in
  fun realOpt _ _ _ (_,[]) = raise Bug "realOpt"
    | realOpt (omin,omax) f p (s:string, h :: (t : string list)) : unit =
      f (p (argToReal s omin omax h)) (s,t);
end;

fun enumOpt _ _ _ (_,[]) = raise Bug "enumOpt"
  | enumOpt (choices : string list) f p (s : string, h :: t) : unit =
    if mem h choices then f (p h) (s,t) else
      raise OptionExit
        {success = false, usage = false,
         message = SOME ("follow parameter " ^ s ^ " with one of {" ^
                         join "," choices ^ "}, not \"" ^ h ^ "\"")};

fun optionOpt _ _ _ (_,[]) = raise Bug "optionOpt"
  | optionOpt (x : string, p) f q (s : string, l as h :: t) : unit =
    if h = x then f (q NONE) (s,t) else p f (q o SOME) (s,l);

(* ------------------------------------------------------------------------- *)
(* Basic options useful for all programs                                     *)
(* ------------------------------------------------------------------------- *)

val basicOptions : opt list =
  [{switches = ["--"], arguments = [],
    description = "no more options",
    processor = fn _ => raise Fail "basicOptions: --"},
   {switches = ["-?","-h","--help"], arguments = [],
    description = "display all options and exit",
    processor = fn _ => raise OptionExit
    {message = SOME "displaying all options", usage = true, success = true}},
   {switches = ["-v", "--version"], arguments = [],
    description = "display version information",
    processor = fn _ => raise Fail "basicOptions: -v, --version"}];

(* ------------------------------------------------------------------------- *)
(* All the command line options of a program                                 *)
(* ------------------------------------------------------------------------- *)

type allOptions = {name : string, version : string, header : string,
                   footer : string, options : opt list};

(* ------------------------------------------------------------------------- *)
(* Usage information                                                         *)
(* ------------------------------------------------------------------------- *)

fun versionInformation ({version, ...} : allOptions) = version;

fun usageInformation ({name,version,header,footer,options} : allOptions) =
  let
    fun listOpts {switches = n, arguments = r, description = s,
                  processor = _} =
        let
          fun indent (s, "" :: l) = indent (s ^ "  ", l) | indent x = x
          val (res,n) = indent ("  ",n)
          val res = res ^ join ", " n
          val res = foldl (fn (x,y) => y ^ " " ^ x) res r
        in
          [res ^ " ...", " " ^ s]
        end

    val alignment =
        [{leftAlign = true, padChar = #"."},
         {leftAlign = true, padChar = #" "}]

    val table = alignTable alignment (map listOpts options)
  in
    header ^ join "\n" table ^ "\n" ^ footer
  end;

(* ------------------------------------------------------------------------- *)
(* Exit the program gracefully                                               *)
(* ------------------------------------------------------------------------- *)

fun exit (allopts : allOptions) (optexit : optionExit) =
  let
    val {name, options, ...} = allopts
    val {message, usage, success} = optexit
    fun err s = TextIO.output (TextIO.stdErr, s)
  in
    case message of NONE => () | SOME m => err (name ^ ": " ^ m ^ "\n");
    if usage then err (usageInformation allopts) else ();
    OS.Process.exit (if success then OS.Process.success else OS.Process.failure)
  end;

fun succeed allopts =
    exit allopts {message = NONE, usage = false, success = true};

fun fail allopts mesg =
    exit allopts {message = SOME mesg, usage = false, success = false};

fun usage allopts mesg =
    exit allopts {message = SOME mesg, usage = true, success = false};

fun version allopts =
    (print (versionInformation allopts);
     exit allopts {message = NONE, usage = false, success = true});

(* ------------------------------------------------------------------------- *)
(* Process the command line options passed to the program                    *)
(* ------------------------------------------------------------------------- *)

fun processOptions (allopts : allOptions) =
  let
    fun findOption x =
      case List.find (fn {switches = n, ...} => mem x n) (#options allopts) of
        NONE => raise OptionExit
                        {message = SOME ("unknown switch \"" ^ x ^ "\""),
                         usage = true, success = false}
      | SOME {arguments = r, processor = f, ...} => (r,f)

    fun getArgs x r xs =
      let
        fun f 1 = "a following argument"
          | f m = Int.toString m ^ " following arguments"
        val m = length r
        val () =
          if m <= length xs then () else
            raise OptionExit
              {usage = false, success = false, message = SOME
               (x ^ " option needs " ^ f m ^ ": " ^ join " " r)}
      in
        divide xs m
      end

    fun process [] = ([], [])
      | process ("--" :: xs) = ([("--",[])], xs)
      | process ("-v" :: _) = version allopts
      | process ("--version" :: _) = version allopts
      | process (x :: xs) =
      if x = "" orelse x = "-" orelse hd (explode x) <> #"-" then ([], x :: xs)
      else
        let
          val (r,f) = findOption x
          val (ys,xs) = getArgs x r xs
          val () = f (x,ys)
        in
          (cons (x,ys) ## I) (process xs)
        end
  in
    fn l =>
    let
      val (a,b) = process l
      val a = foldl (fn ((x,xs),ys) => x :: xs @ ys) [] (rev a)
    in
      (a,b)
    end
    handle OptionExit x => exit allopts x
  end;

end
end;

(**** Original file: Name.sig ****)

(* ========================================================================= *)
(* NAMES                                                                     *)
(* Copyright (c) 2004-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Name =
sig

type name = string

val compare : name * name -> order

val pp : name Metis.Parser.pp

end

(**** Original file: Name.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* NAMES                                                                     *)
(* Copyright (c) 2004-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Name :> Name =
struct

type name = string;

val compare = String.compare;

val pp = Parser.ppString;

end

structure NameOrdered =
struct type t = Name.name val compare = Name.compare end

structure NameSet =
struct

  local
    structure S = ElementSet (NameOrdered);
  in
    open S;
  end;

  val pp =
      Parser.ppMap
        toList
        (Parser.ppBracket "{" "}" (Parser.ppSequence "," Name.pp));

end

structure NameMap = KeyMap (NameOrdered);

structure NameArity =
struct

type nameArity = Name.name * int;

fun name ((n,_) : nameArity) = n;

fun arity ((_,i) : nameArity) = i;

fun nary i n_i = arity n_i = i;

val nullary = nary 0
and unary = nary 1
and binary = nary 2
and ternary = nary 3;

fun compare ((n1,i1),(n2,i2)) =
    case Name.compare (n1,n2) of
      LESS => LESS
    | EQUAL => Int.compare (i1,i2)
    | GREATER => GREATER;

val pp = Parser.ppMap (fn (n,i) => n ^ "/" ^ Int.toString i) Parser.ppString;

end

structure NameArityOrdered =
struct type t = NameArity.nameArity val compare = NameArity.compare end

structure NameAritySet =
struct

  local
    structure S = ElementSet (NameArityOrdered);
  in
    open S;
  end;

  val allNullary = all NameArity.nullary;

  val pp =
      Parser.ppMap
        toList
        (Parser.ppBracket "{" "}" (Parser.ppSequence "," NameArity.pp));

end

structure NameArityMap = KeyMap (NameArityOrdered);
end;

(**** Original file: Term.sig ****)

(* ========================================================================= *)
(* FIRST ORDER LOGIC TERMS                                                   *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Term =
sig

(* ------------------------------------------------------------------------- *)
(* A type of first order logic terms.                                        *)
(* ------------------------------------------------------------------------- *)

type var = Metis.Name.name

type functionName = Metis.Name.name

type function = functionName * int

type const = functionName

datatype term =
    Var of var
  | Fn of functionName * term list

(* ------------------------------------------------------------------------- *)
(* Constructors and destructors.                                             *)
(* ------------------------------------------------------------------------- *)

(* Variables *)

val destVar : term -> var

val isVar : term -> bool

val equalVar : var -> term -> bool

(* Functions *)

val destFn : term -> functionName * term list

val isFn : term -> bool

val fnName : term -> functionName

val fnArguments : term -> term list

val fnArity : term -> int

val fnFunction : term -> function

val functions : term -> Metis.NameAritySet.set

val functionNames : term -> Metis.NameSet.set

(* Constants *)

val mkConst : const -> term

val destConst : term -> const

val isConst : term -> bool

(* Binary functions *)

val mkBinop : functionName -> term * term -> term

val destBinop : functionName -> term -> term * term

val isBinop : functionName -> term -> bool

(* ------------------------------------------------------------------------- *)
(* The size of a term in symbols.                                            *)
(* ------------------------------------------------------------------------- *)

val symbols : term -> int

(* ------------------------------------------------------------------------- *)
(* A total comparison function for terms.                                    *)
(* ------------------------------------------------------------------------- *)

val compare : term * term -> order

(* ------------------------------------------------------------------------- *)
(* Subterms.                                                                 *)
(* ------------------------------------------------------------------------- *)

type path = int list

val subterm : term -> path -> term

val subterms : term -> (path * term) list

val replace : term -> path * term -> term

val find : (term -> bool) -> term -> path option

val ppPath : path Metis.Parser.pp

val pathToString : path -> string

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

val freeIn : var -> term -> bool

val freeVars : term -> Metis.NameSet.set

(* ------------------------------------------------------------------------- *)
(* Fresh variables.                                                          *)
(* ------------------------------------------------------------------------- *)

val newVar : unit -> term

val newVars : int -> term list

val variantPrime : Metis.NameSet.set -> var -> var

val variantNum : Metis.NameSet.set -> var -> var

(* ------------------------------------------------------------------------- *)
(* Special support for terms with type annotations.                          *)
(* ------------------------------------------------------------------------- *)

val isTypedVar : term -> bool

val typedSymbols : term -> int

val nonVarTypedSubterms : term -> (path * term) list

(* ------------------------------------------------------------------------- *)
(* Special support for terms with an explicit function application operator. *)
(* ------------------------------------------------------------------------- *)

val mkComb : term * term -> term

val destComb : term -> term * term

val isComb : term -> bool

val listMkComb : term * term list -> term

val stripComb : term -> term * term list

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty printing.                                              *)
(* ------------------------------------------------------------------------- *)

(* Infix symbols *)

val infixes : Metis.Parser.infixities Unsynchronized.ref

(* The negation symbol *)

val negation : Metis.Name.name Unsynchronized.ref

(* Binder symbols *)

val binders : Metis.Name.name list Unsynchronized.ref

(* Bracket symbols *)

val brackets : (Metis.Name.name * Metis.Name.name) list Unsynchronized.ref

(* Pretty printing *)

val pp : term Metis.Parser.pp

val toString : term -> string

(* Parsing *)

val fromString : string -> term

val parse : term Metis.Parser.quotation -> term

end

(**** Original file: Term.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* FIRST ORDER LOGIC TERMS                                                   *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Term :> Term =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun stripSuffix pred s =
    let
      fun f 0 = ""
        | f n =
          let
            val n' = n - 1
          in
            if pred (String.sub (s,n')) then f n'
            else String.substring (s,0,n)
          end
    in
      f (size s)
    end;

(* ------------------------------------------------------------------------- *)
(* A type of first order logic terms.                                        *)
(* ------------------------------------------------------------------------- *)

type var = Name.name;

type functionName = Name.name;

type function = functionName * int;

type const = functionName;

datatype term =
    Var of Name.name
  | Fn of Name.name * term list;

(* ------------------------------------------------------------------------- *)
(* Constructors and destructors.                                             *)
(* ------------------------------------------------------------------------- *)

(* Variables *)

fun destVar (Var v) = v
  | destVar (Fn _) = raise Error "destVar";

val isVar = can destVar;

fun equalVar v (Var v') = v = v'
  | equalVar _ _ = false;

(* Functions *)

fun destFn (Fn f) = f
  | destFn (Var _) = raise Error "destFn";

val isFn = can destFn;

fun fnName tm = fst (destFn tm);

fun fnArguments tm = snd (destFn tm);

fun fnArity tm = length (fnArguments tm);

fun fnFunction tm = (fnName tm, fnArity tm);

local
  fun func fs [] = fs
    | func fs (Var _ :: tms) = func fs tms
    | func fs (Fn (n,l) :: tms) =
      func (NameAritySet.add fs (n, length l)) (l @ tms);
in
  fun functions tm = func NameAritySet.empty [tm];
end;

local
  fun func fs [] = fs
    | func fs (Var _ :: tms) = func fs tms
    | func fs (Fn (n,l) :: tms) = func (NameSet.add fs n) (l @ tms);
in
  fun functionNames tm = func NameSet.empty [tm];
end;

(* Constants *)

fun mkConst c = (Fn (c, []));

fun destConst (Fn (c, [])) = c
  | destConst _ = raise Error "destConst";

val isConst = can destConst;

(* Binary functions *)

fun mkBinop f (a,b) = Fn (f,[a,b]);

fun destBinop f (Fn (x,[a,b])) =
    if x = f then (a,b) else raise Error "Term.destBinop: wrong binop"
  | destBinop _ _ = raise Error "Term.destBinop: not a binop";

fun isBinop f = can (destBinop f);

(* ------------------------------------------------------------------------- *)
(* The size of a term in symbols.                                            *)
(* ------------------------------------------------------------------------- *)

val VAR_SYMBOLS = 1;

val FN_SYMBOLS = 1;

local
  fun sz n [] = n
    | sz n (Var _ :: tms) = sz (n + VAR_SYMBOLS) tms
    | sz n (Fn (func,args) :: tms) = sz (n + FN_SYMBOLS) (args @ tms);
in
  fun symbols tm = sz 0 [tm];
end;

(* ------------------------------------------------------------------------- *)
(* A total comparison function for terms.                                    *)
(* ------------------------------------------------------------------------- *)

local
  fun cmp [] [] = EQUAL
    | cmp (Var _ :: _) (Fn _ :: _) = LESS
    | cmp (Fn _ :: _) (Var _ :: _) = GREATER
    | cmp (Var v1 :: tms1) (Var v2 :: tms2) =
      (case Name.compare (v1,v2) of
         LESS => LESS
       | EQUAL => cmp tms1 tms2
       | GREATER => GREATER)
    | cmp (Fn (f1,a1) :: tms1) (Fn (f2,a2) :: tms2) =
      (case Name.compare (f1,f2) of
         LESS => LESS
       | EQUAL =>
         (case Int.compare (length a1, length a2) of
            LESS => LESS
          | EQUAL => cmp (a1 @ tms1) (a2 @ tms2)
          | GREATER => GREATER)
       | GREATER => GREATER)
    | cmp _ _ = raise Bug "Term.compare";
in
  fun compare (tm1,tm2) = cmp [tm1] [tm2];
end;

(* ------------------------------------------------------------------------- *)
(* Subterms.                                                                 *)
(* ------------------------------------------------------------------------- *)

type path = int list;

fun subterm tm [] = tm
  | subterm (Var _) (_ :: _) = raise Error "Term.subterm: Var"
  | subterm (Fn (_,tms)) (h :: t) =
    if h >= length tms then raise Error "Term.replace: Fn"
    else subterm (List.nth (tms,h)) t;

local
  fun subtms [] acc = acc
    | subtms ((path,tm) :: rest) acc =
      let
        fun f (n,arg) = (n :: path, arg)

        val acc = (rev path, tm) :: acc
      in
        case tm of
          Var _ => subtms rest acc
        | Fn (_,args) => subtms (map f (enumerate args) @ rest) acc
      end;
in
  fun subterms tm = subtms [([],tm)] [];
end;

fun replace tm ([],res) = if res = tm then tm else res
  | replace tm (h :: t, res) =
    case tm of
      Var _ => raise Error "Term.replace: Var"
    | Fn (func,tms) =>
      if h >= length tms then raise Error "Term.replace: Fn"
      else
        let
          val arg = List.nth (tms,h)
          val arg' = replace arg (t,res)
        in
          if Sharing.pointerEqual (arg',arg) then tm
          else Fn (func, updateNth (h,arg') tms)
        end;

fun find pred =
    let
      fun search [] = NONE
        | search ((path,tm) :: rest) =
          if pred tm then SOME (rev path)
          else
            case tm of
              Var _ => search rest
            | Fn (_,a) =>
              let
                val subtms = map (fn (i,t) => (i :: path, t)) (enumerate a)
              in
                search (subtms @ rest)
              end
    in
      fn tm => search [([],tm)]
    end;

val ppPath = Parser.ppList Parser.ppInt;

val pathToString = Parser.toString ppPath;

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

local
  fun free _ [] = false
    | free v (Var w :: tms) = v = w orelse free v tms
    | free v (Fn (_,args) :: tms) = free v (args @ tms);
in
  fun freeIn v tm = free v [tm];
end;

local
  fun free vs [] = vs
    | free vs (Var v :: tms) = free (NameSet.add vs v) tms
    | free vs (Fn (_,args) :: tms) = free vs (args @ tms);
in
  fun freeVars tm = free NameSet.empty [tm];
end;

(* ------------------------------------------------------------------------- *)
(* Fresh variables.                                                          *)
(* ------------------------------------------------------------------------- *)

local
  val prefix  = "_";

  fun numVar i = Var (mkPrefix prefix (Int.toString i));
in
  fun newVar () = numVar (newInt ());

  fun newVars n = map numVar (newInts n);
end;

fun variantPrime avoid =
    let
      fun f v = if NameSet.member v avoid then f (v ^ "'") else v
    in
      f
    end;

fun variantNum avoid v =
    if not (NameSet.member v avoid) then v
    else
      let
        val v = stripSuffix Char.isDigit v
                                                                    
        fun f n =
            let
              val v_n = v ^ Int.toString n
            in
              if NameSet.member v_n avoid then f (n + 1) else v_n
            end
      in
        f 0
      end;

(* ------------------------------------------------------------------------- *)
(* Special support for terms with type annotations.                          *)
(* ------------------------------------------------------------------------- *)

fun isTypedVar (Var _) = true
  | isTypedVar (Fn (":", [Var _, _])) = true
  | isTypedVar (Fn _) = false;

local
  fun sz n [] = n
    | sz n (Var _ :: tms) = sz (n + 1) tms
    | sz n (Fn (":",[tm,_]) :: tms) = sz n (tm :: tms)
    | sz n (Fn (_,args) :: tms) = sz (n + 1) (args @ tms);
in
  fun typedSymbols tm = sz 0 [tm];
end;

local
  fun subtms [] acc = acc
    | subtms ((_, Var _) :: rest) acc = subtms rest acc
    | subtms ((_, Fn (":", [Var _, _])) :: rest) acc = subtms rest acc
    | subtms ((path, tm as Fn func) :: rest) acc =
      let
        fun f (n,arg) = (n :: path, arg)

        val acc = (rev path, tm) :: acc
      in
        case func of
          (":",[arg,_]) => subtms ((0 :: path, arg) :: rest) acc
        | (_,args) => subtms (map f (enumerate args) @ rest) acc
      end;
in
  fun nonVarTypedSubterms tm = subtms [([],tm)] [];
end;

(* ------------------------------------------------------------------------- *)
(* Special support for terms with an explicit function application operator. *)
(* ------------------------------------------------------------------------- *)

fun mkComb (f,a) = Fn (".",[f,a]);

fun destComb (Fn (".",[f,a])) = (f,a)
  | destComb _ = raise Error "destComb";

val isComb = can destComb;

fun listMkComb (f,l) = foldl mkComb f l;

local
  fun strip tms (Fn (".",[f,a])) = strip (a :: tms) f
    | strip tms tm = (tm,tms);
in
  fun stripComb tm = strip [] tm;
end;

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty printing.                                              *)
(* ------------------------------------------------------------------------- *)

(* Operators parsed and printed infix *)

val infixes : Parser.infixities Unsynchronized.ref = Unsynchronized.ref
  [(* ML symbols *)
   {token = " / ", precedence = 7, leftAssoc = true},
   {token = " div ", precedence = 7, leftAssoc = true},
   {token = " mod ", precedence = 7, leftAssoc = true},
   {token = " * ", precedence = 7, leftAssoc = true},
   {token = " + ", precedence = 6, leftAssoc = true},
   {token = " - ", precedence = 6, leftAssoc = true},
   {token = " ^ ", precedence = 6, leftAssoc = true},
   {token = " @ ", precedence = 5, leftAssoc = false},
   {token = " :: ", precedence = 5, leftAssoc = false},
   {token = " = ", precedence = 4, leftAssoc = true},
   {token = " <> ", precedence = 4, leftAssoc = true},
   {token = " <= ", precedence = 4, leftAssoc = true},
   {token = " < ", precedence = 4, leftAssoc = true},
   {token = " >= ", precedence = 4, leftAssoc = true},
   {token = " > ", precedence = 4, leftAssoc = true},
   {token = " o ", precedence = 3, leftAssoc = true},
   {token = " -> ", precedence = 2, leftAssoc = false},  (* inferred prec *)
   {token = " : ", precedence = 1, leftAssoc = false},  (* inferred prec *)
   {token = ", ", precedence = 0, leftAssoc = false},  (* inferred prec *)

   (* Logical connectives *)
   {token = " /\\ ", precedence = ~1, leftAssoc = false},
   {token = " \\/ ", precedence = ~2, leftAssoc = false},
   {token = " ==> ", precedence = ~3, leftAssoc = false},
   {token = " <=> ", precedence = ~4, leftAssoc = false},

   (* Other symbols *)
   {token = " . ", precedence = 9, leftAssoc = true},  (* function app *)
   {token = " ** ", precedence = 8, leftAssoc = true},
   {token = " ++ ", precedence = 6, leftAssoc = true},
   {token = " -- ", precedence = 6, leftAssoc = true},
   {token = " == ", precedence = 4, leftAssoc = true}];

(* The negation symbol *)

val negation : Name.name Unsynchronized.ref = Unsynchronized.ref "~";

(* Binder symbols *)

val binders : Name.name list Unsynchronized.ref = Unsynchronized.ref ["\\","!","?","?!"];

(* Bracket symbols *)

val brackets : (Name.name * Name.name) list Unsynchronized.ref = Unsynchronized.ref [("[","]"),("{","}")];

(* Pretty printing *)

local
  open Parser;
in
  fun pp inputPpstrm inputTerm =
      let
        val quants = !binders
        and iOps = !infixes
        and neg = !negation
        and bracks = !brackets

        val bracks = map (fn (b1,b2) => (b1 ^ b2, b1, b2)) bracks

        val bTokens = map #2 bracks @ map #3 bracks

        val iTokens = infixTokens iOps

        fun destI (Fn (f,[a,b])) =
            if mem f iTokens then SOME (f,a,b) else NONE
          | destI _ = NONE

        val iPrinter = ppInfixes iOps destI

        val specialTokens = neg :: quants @ ["$","(",")"] @ bTokens @ iTokens

        fun vName bv s = NameSet.member s bv

        fun checkVarName bv s = if vName bv s then s else "$" ^ s

        fun varName bv = ppMap (checkVarName bv) ppString

        fun checkFunctionName bv s =
            if mem s specialTokens orelse vName bv s then "(" ^ s ^ ")" else s

        fun functionName bv = ppMap (checkFunctionName bv) ppString

        fun isI tm = Option.isSome (destI tm)

        fun stripNeg (tm as Fn (f,[a])) =
            if f <> neg then (0,tm)
            else let val (n,tm) = stripNeg a in (n + 1, tm) end
          | stripNeg tm = (0,tm)

        val destQuant =
            let
              fun dest q (Fn (q', [Var v, body])) =
                  if q <> q' then NONE
                  else
                    (case dest q body of
                       NONE => SOME (q,v,[],body)
                     | SOME (_,v',vs,body) => SOME (q, v, v' :: vs, body))
                | dest _ _ = NONE
            in
              fn tm => Useful.first (fn q => dest q tm) quants
            end

        fun isQuant tm = Option.isSome (destQuant tm)

        fun destBrack (Fn (b,[tm])) =
            (case List.find (fn (n,_,_) => n = b) bracks of
               NONE => NONE
             | SOME (_,b1,b2) => SOME (b1,tm,b2))
          | destBrack _ = NONE

        fun isBrack tm = Option.isSome (destBrack tm)
            
        fun functionArgument bv ppstrm tm =
            (addBreak ppstrm (1,0);
             if isBrack tm then customBracket bv ppstrm tm
             else if isVar tm orelse isConst tm then basic bv ppstrm tm
             else bracket bv ppstrm tm)

        and basic bv ppstrm (Var v) = varName bv ppstrm v
          | basic bv ppstrm (Fn (f,args)) =
            (beginBlock ppstrm Inconsistent 2;
             functionName bv ppstrm f;
             app (functionArgument bv ppstrm) args;
             endBlock ppstrm)

        and customBracket bv ppstrm tm =
            case destBrack tm of
              SOME (b1,tm,b2) => ppBracket b1 b2 (term bv) ppstrm tm
            | NONE => basic bv ppstrm tm

        and innerQuant bv ppstrm tm =
            case destQuant tm of
              NONE => term bv ppstrm tm
            | SOME (q,v,vs,tm) =>
              let
                val bv = NameSet.addList (NameSet.add bv v) vs
              in
                addString ppstrm q;
                varName bv ppstrm v;
                app (fn v => (addBreak ppstrm (1,0); varName bv ppstrm v)) vs;
                addString ppstrm ".";
                addBreak ppstrm (1,0);
                innerQuant bv ppstrm tm
              end

        and quantifier bv ppstrm tm =
            if not (isQuant tm) then customBracket bv ppstrm tm
            else
              (beginBlock ppstrm Inconsistent 2;
               innerQuant bv ppstrm tm;
               endBlock ppstrm)

        and molecule bv ppstrm (tm,r) =
            let
              val (n,tm) = stripNeg tm
            in
              beginBlock ppstrm Inconsistent n;
              funpow n (fn () => addString ppstrm neg) ();
              if isI tm orelse (r andalso isQuant tm) then bracket bv ppstrm tm
              else quantifier bv ppstrm tm;
              endBlock ppstrm
            end

        and term bv ppstrm tm = iPrinter (molecule bv) ppstrm (tm,false)

        and bracket bv ppstrm tm = ppBracket "(" ")" (term bv) ppstrm tm
  in
    term NameSet.empty
  end inputPpstrm inputTerm;
end;

fun toString tm = Parser.toString pp tm;

(* Parsing *)

local
  open Parser;

  infixr 9 >>++
  infixr 8 ++
  infixr 7 >>
  infixr 6 ||

  val isAlphaNum =
      let
        val alphaNumChars = explode "_'"
      in
        fn c => mem c alphaNumChars orelse Char.isAlphaNum c
      end;

  local
    val alphaNumToken = atLeastOne (some isAlphaNum) >> implode;

    val symbolToken =
        let
          fun isNeg c = str c = !negation
                        
          val symbolChars = explode "<>=-*+/\\?@|!$%&#^:;~"

          fun isSymbol c = mem c symbolChars

          fun isNonNegSymbol c = not (isNeg c) andalso isSymbol c
        in
          some isNeg >> str ||
          (some isNonNegSymbol ++ many (some isSymbol)) >> (implode o op::)
        end;

    val punctToken =
        let
          val punctChars = explode "()[]{}.,"

          fun isPunct c = mem c punctChars
        in
          some isPunct >> str
        end;

    val lexToken = alphaNumToken || symbolToken || punctToken;

    val space = many (some Char.isSpace);
  in
    val lexer = (space ++ lexToken ++ space) >> (fn (_,(tok,_)) => tok);
  end;

  fun termParser inputStream =
      let
        val quants = !binders
        and iOps = !infixes
        and neg = !negation
        and bracks = ("(",")") :: !brackets

        val bracks = map (fn (b1,b2) => (b1 ^ b2, b1, b2)) bracks

        val bTokens = map #2 bracks @ map #3 bracks

        fun possibleVarName "" = false
          | possibleVarName s = isAlphaNum (String.sub (s,0))

        fun vName bv s = NameSet.member s bv

        val iTokens = infixTokens iOps

        val iParser = parseInfixes iOps (fn (f,a,b) => Fn (f,[a,b]))

        val specialTokens = neg :: quants @ ["$"] @ bTokens @ iTokens

        fun varName bv =
            Parser.some (vName bv) ||
            (exact "$" ++ some possibleVarName) >> (fn (_,s) => s)

        fun fName bv s = not (mem s specialTokens) andalso not (vName bv s)

        fun functionName bv =
            Parser.some (fName bv) ||
            (exact "(" ++ any ++ exact ")") >> (fn (_,(s,_)) => s)

        fun basic bv tokens =
            let
              val var = varName bv >> Var

              val const = functionName bv >> (fn f => Fn (f,[]))

              fun bracket (ab,a,b) =
                  (exact a ++ term bv ++ exact b) >>
                  (fn (_,(tm,_)) => if ab = "()" then tm else Fn (ab,[tm]))

              fun quantifier q =
                  let
                    fun bind (v,t) = Fn (q, [Var v, t])
                  in
                    (exact q ++ atLeastOne (some possibleVarName) ++
                     exact ".") >>++
                    (fn (_,(vs,_)) =>
                        term (NameSet.addList bv vs) >>
                        (fn body => foldr bind body vs))
                  end
            in
              var ||
              const ||
              first (map bracket bracks) ||
              first (map quantifier quants)
            end tokens

        and molecule bv tokens =
            let
              val negations = many (exact neg) >> length

              val function =
                  (functionName bv ++ many (basic bv)) >> Fn || basic bv
            in
              (negations ++ function) >>
              (fn (n,tm) => funpow n (fn t => Fn (neg,[t])) tm)
            end tokens

        and term bv tokens = iParser (molecule bv) tokens
      in
        term NameSet.empty
      end inputStream;
in
  fun fromString input =
      let
        val chars = Stream.fromList (explode input)

        val tokens = everything (lexer >> singleton) chars

        val terms = everything (termParser >> singleton) tokens
      in
        case Stream.toList terms of
          [tm] => tm
        | _ => raise Error "Syntax.stringToTerm"
      end;
end;

local
  val antiquotedTermToString =
      Parser.toString (Parser.ppBracket "(" ")" pp);
in
  val parse = Parser.parseQuotation antiquotedTermToString fromString;
end;

end

structure TermOrdered =
struct type t = Term.term val compare = Term.compare end

structure TermSet = ElementSet (TermOrdered);

structure TermMap = KeyMap (TermOrdered);
end;

(**** Original file: Subst.sig ****)

(* ========================================================================= *)
(* FIRST ORDER LOGIC SUBSTITUTIONS                                           *)
(* Copyright (c) 2002-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Subst =
sig

(* ------------------------------------------------------------------------- *)
(* A type of first order logic substitutions.                                *)
(* ------------------------------------------------------------------------- *)

type subst

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val empty : subst

val null : subst -> bool

val size : subst -> int

val peek : subst -> Metis.Term.var -> Metis.Term.term option

val insert : subst -> Metis.Term.var * Metis.Term.term -> subst

val singleton : Metis.Term.var * Metis.Term.term -> subst

val union : subst -> subst -> subst

val toList : subst -> (Metis.Term.var * Metis.Term.term) list

val fromList : (Metis.Term.var * Metis.Term.term) list -> subst

val foldl : (Metis.Term.var * Metis.Term.term * 'a -> 'a) -> 'a -> subst -> 'a

val foldr : (Metis.Term.var * Metis.Term.term * 'a -> 'a) -> 'a -> subst -> 'a

val pp : subst Metis.Parser.pp

val toString : subst -> string

(* ------------------------------------------------------------------------- *)
(* Normalizing removes identity substitutions.                               *)
(* ------------------------------------------------------------------------- *)

val normalize : subst -> subst

(* ------------------------------------------------------------------------- *)
(* Applying a substitution to a first order logic term.                      *)
(* ------------------------------------------------------------------------- *)

val subst : subst -> Metis.Term.term -> Metis.Term.term

(* ------------------------------------------------------------------------- *)
(* Restricting a substitution to a smaller set of variables.                 *)
(* ------------------------------------------------------------------------- *)

val restrict : subst -> Metis.NameSet.set -> subst

val remove : subst -> Metis.NameSet.set -> subst

(* ------------------------------------------------------------------------- *)
(* Composing two substitutions so that the following identity holds:         *)
(*                                                                           *)
(* subst (compose sub1 sub2) tm = subst sub2 (subst sub1 tm)                 *)
(* ------------------------------------------------------------------------- *)

val compose : subst -> subst -> subst

(* ------------------------------------------------------------------------- *)
(* Substitutions can be inverted iff they are renaming substitutions.        *) 
(* ------------------------------------------------------------------------- *)

val invert : subst -> subst  (* raises Error *)

val isRenaming : subst -> bool

(* ------------------------------------------------------------------------- *)
(* Creating a substitution to freshen variables.                             *)
(* ------------------------------------------------------------------------- *)

val freshVars : Metis.NameSet.set -> subst

(* ------------------------------------------------------------------------- *)
(* Matching for first order logic terms.                                     *)
(* ------------------------------------------------------------------------- *)

val match : subst -> Metis.Term.term -> Metis.Term.term -> subst  (* raises Error *)

(* ------------------------------------------------------------------------- *)
(* Unification for first order logic terms.                                  *)
(* ------------------------------------------------------------------------- *)

val unify : subst -> Metis.Term.term -> Metis.Term.term -> subst  (* raises Error *)

end

(**** Original file: Subst.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* FIRST ORDER LOGIC SUBSTITUTIONS                                           *)
(* Copyright (c) 2002-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Subst :> Subst =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* A type of first order logic substitutions.                                *)
(* ------------------------------------------------------------------------- *)

datatype subst = Subst of Term.term NameMap.map;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val empty = Subst (NameMap.new ());

fun null (Subst m) = NameMap.null m;

fun size (Subst m) = NameMap.size m;

fun peek (Subst m) v = NameMap.peek m v;

fun insert (Subst m) v_tm = Subst (NameMap.insert m v_tm);

fun singleton v_tm = insert empty v_tm;

local
  fun compatible (tm1,tm2) =
      if tm1 = tm2 then SOME tm1 else raise Error "Subst.union: incompatible";
in
  fun union (s1 as Subst m1) (s2 as Subst m2) =
      if NameMap.null m1 then s2
      else if NameMap.null m2 then s1
      else Subst (NameMap.union compatible m1 m2);
end;

fun toList (Subst m) = NameMap.toList m;

fun fromList l = Subst (NameMap.fromList l);

fun foldl f b (Subst m) = NameMap.foldl f b m;

fun foldr f b (Subst m) = NameMap.foldr f b m;

fun pp ppstrm sub =
    Parser.ppBracket "<[" "]>"
      (Parser.ppSequence "," (Parser.ppBinop " |->" Parser.ppString Term.pp))
      ppstrm (toList sub);

val toString = Parser.toString pp;

(* ------------------------------------------------------------------------- *)
(* Normalizing removes identity substitutions.                               *)
(* ------------------------------------------------------------------------- *)

local
  fun isNotId (v,tm) = not (Term.equalVar v tm);
in
  fun normalize (sub as Subst m) =
      let
        val m' = NameMap.filter isNotId m
      in
        if NameMap.size m = NameMap.size m' then sub else Subst m'
      end;
end;

(* ------------------------------------------------------------------------- *)
(* Applying a substitution to a first order logic term.                      *)
(* ------------------------------------------------------------------------- *)

fun subst sub =
    let
      fun tmSub (tm as Term.Var v) =
          (case peek sub v of
             SOME tm' => if Sharing.pointerEqual (tm,tm') then tm else tm'
           | NONE => tm)
        | tmSub (tm as Term.Fn (f,args)) =
          let
            val args' = Sharing.map tmSub args
          in
            if Sharing.pointerEqual (args,args') then tm
            else Term.Fn (f,args')
          end
    in
      fn tm => if null sub then tm else tmSub tm
    end;

(* ------------------------------------------------------------------------- *)
(* Restricting a substitution to a given set of variables.                   *)
(* ------------------------------------------------------------------------- *)

fun restrict (sub as Subst m) varSet =
    let
      fun isRestrictedVar (v,_) = NameSet.member v varSet

      val m' = NameMap.filter isRestrictedVar m
    in
      if NameMap.size m = NameMap.size m' then sub else Subst m'
    end;

fun remove (sub as Subst m) varSet =
    let
      fun isRestrictedVar (v,_) = not (NameSet.member v varSet)

      val m' = NameMap.filter isRestrictedVar m
    in
      if NameMap.size m = NameMap.size m' then sub else Subst m'
    end;

(* ------------------------------------------------------------------------- *)
(* Composing two substitutions so that the following identity holds:         *)
(*                                                                           *)
(* subst (compose sub1 sub2) tm = subst sub2 (subst sub1 tm)                 *)
(* ------------------------------------------------------------------------- *)

fun compose (sub1 as Subst m1) sub2 =
    let
      fun f (v,tm,s) = insert s (v, subst sub2 tm)
    in
      if null sub2 then sub1 else NameMap.foldl f sub2 m1
    end;

(* ------------------------------------------------------------------------- *)
(* Substitutions can be inverted iff they are renaming substitutions.        *) 
(* ------------------------------------------------------------------------- *)

local
  fun inv (v, Term.Var w, s) =
      if NameMap.inDomain w s then raise Error "Subst.invert: non-injective"
      else NameMap.insert s (w, Term.Var v)
    | inv (_, Term.Fn _, _) = raise Error "Subst.invert: non-variable";
in
  fun invert (Subst m) = Subst (NameMap.foldl inv (NameMap.new ()) m);
end;

val isRenaming = can invert;

(* ------------------------------------------------------------------------- *)
(* Creating a substitution to freshen variables.                             *)
(* ------------------------------------------------------------------------- *)

val freshVars =
    let
      fun add (v,m) = insert m (v, Term.newVar ())
    in
      NameSet.foldl add empty
    end;

(* ------------------------------------------------------------------------- *)
(* Matching for first order logic terms.                                     *)
(* ------------------------------------------------------------------------- *)

local
  fun matchList sub [] = sub
    | matchList sub ((Term.Var v, tm) :: rest) =
      let
        val sub =
            case peek sub v of
              NONE => insert sub (v,tm)
            | SOME tm' =>
              if tm = tm' then sub
              else raise Error "Subst.match: incompatible matches"
      in
        matchList sub rest
      end
    | matchList sub ((Term.Fn (f1,args1), Term.Fn (f2,args2)) :: rest) =
      if f1 = f2 andalso length args1 = length args2 then
        matchList sub (zip args1 args2 @ rest)
      else raise Error "Subst.match: different structure"
    | matchList _ _ = raise Error "Subst.match: functions can't match vars";
in
  fun match sub tm1 tm2 = matchList sub [(tm1,tm2)];
end;

(* ------------------------------------------------------------------------- *)
(* Unification for first order logic terms.                                  *)
(* ------------------------------------------------------------------------- *)

local
  fun solve sub [] = sub
    | solve sub ((tm1_tm2 as (tm1,tm2)) :: rest) =
      if Portable.pointerEqual tm1_tm2 then solve sub rest
      else solve' sub (subst sub tm1) (subst sub tm2) rest

  and solve' sub (Term.Var v) tm rest =
      if Term.equalVar v tm then solve sub rest
      else if Term.freeIn v tm then raise Error "Subst.unify: occurs check"
      else
        (case peek sub v of
           NONE => solve (compose sub (singleton (v,tm))) rest
         | SOME tm' => solve' sub tm' tm rest)
    | solve' sub tm1 (tm2 as Term.Var _) rest = solve' sub tm2 tm1 rest
    | solve' sub (Term.Fn (f1,args1)) (Term.Fn (f2,args2)) rest =
      if f1 = f2 andalso length args1 = length args2 then
        solve sub (zip args1 args2 @ rest)
      else
        raise Error "Subst.unify: different structure";
in
  fun unify sub tm1 tm2 = solve sub [(tm1,tm2)];
end;

end
end;

(**** Original file: Atom.sig ****)

(* ========================================================================= *)
(* FIRST ORDER LOGIC ATOMS                                                   *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Atom =
sig

(* ------------------------------------------------------------------------- *)
(* A type for storing first order logic atoms.                               *)
(* ------------------------------------------------------------------------- *)

type relationName = Metis.Name.name

type relation = relationName * int

type atom = relationName * Metis.Term.term list

(* ------------------------------------------------------------------------- *)
(* Constructors and destructors.                                             *)
(* ------------------------------------------------------------------------- *)

val name : atom -> relationName

val arguments : atom -> Metis.Term.term list

val arity : atom -> int

val relation : atom -> relation

val functions : atom -> Metis.NameAritySet.set

val functionNames : atom -> Metis.NameSet.set

(* Binary relations *)

val mkBinop : relationName -> Metis.Term.term * Metis.Term.term -> atom

val destBinop : relationName -> atom -> Metis.Term.term * Metis.Term.term

val isBinop : relationName -> atom -> bool

(* ------------------------------------------------------------------------- *)
(* The size of an atom in symbols.                                           *)
(* ------------------------------------------------------------------------- *)

val symbols : atom -> int

(* ------------------------------------------------------------------------- *)
(* A total comparison function for atoms.                                    *)
(* ------------------------------------------------------------------------- *)

val compare : atom * atom -> order

(* ------------------------------------------------------------------------- *)
(* Subterms.                                                                 *)
(* ------------------------------------------------------------------------- *)

val subterm : atom -> Metis.Term.path -> Metis.Term.term

val subterms : atom -> (Metis.Term.path * Metis.Term.term) list

val replace : atom -> Metis.Term.path * Metis.Term.term -> atom

val find : (Metis.Term.term -> bool) -> atom -> Metis.Term.path option

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

val freeIn : Metis.Term.var -> atom -> bool

val freeVars : atom -> Metis.NameSet.set

(* ------------------------------------------------------------------------- *)
(* Substitutions.                                                            *)
(* ------------------------------------------------------------------------- *)

val subst : Metis.Subst.subst -> atom -> atom

(* ------------------------------------------------------------------------- *)
(* Matching.                                                                 *)
(* ------------------------------------------------------------------------- *)

val match : Metis.Subst.subst -> atom -> atom -> Metis.Subst.subst  (* raises Error *)

(* ------------------------------------------------------------------------- *)
(* Unification.                                                              *)
(* ------------------------------------------------------------------------- *)

val unify : Metis.Subst.subst -> atom -> atom -> Metis.Subst.subst  (* raises Error *)

(* ------------------------------------------------------------------------- *)
(* The equality relation.                                                    *)
(* ------------------------------------------------------------------------- *)

val eqRelation : relation

val mkEq : Metis.Term.term * Metis.Term.term -> atom

val destEq : atom -> Metis.Term.term * Metis.Term.term

val isEq : atom -> bool

val mkRefl : Metis.Term.term -> atom

val destRefl : atom -> Metis.Term.term

val isRefl : atom -> bool

val sym : atom -> atom  (* raises Error if given a refl *)

val lhs : atom -> Metis.Term.term

val rhs : atom -> Metis.Term.term

(* ------------------------------------------------------------------------- *)
(* Special support for terms with type annotations.                          *)
(* ------------------------------------------------------------------------- *)

val typedSymbols : atom -> int

val nonVarTypedSubterms : atom -> (Metis.Term.path * Metis.Term.term) list

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty printing.                                              *)
(* ------------------------------------------------------------------------- *)

val pp : atom Metis.Parser.pp

val toString : atom -> string

val fromString : string -> atom

val parse : Metis.Term.term Metis.Parser.quotation -> atom

end

(**** Original file: Atom.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* FIRST ORDER LOGIC ATOMS                                                   *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Atom :> Atom =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* A type for storing first order logic atoms.                               *)
(* ------------------------------------------------------------------------- *)

type relationName = Name.name;

type relation = relationName * int;

type atom = relationName * Term.term list;

(* ------------------------------------------------------------------------- *)
(* Constructors and destructors.                                             *)
(* ------------------------------------------------------------------------- *)

fun name ((rel,_) : atom) = rel;

fun arguments ((_,args) : atom) = args;

fun arity atm = length (arguments atm);

fun relation atm = (name atm, arity atm);

val functions =
    let
      fun f (tm,acc) = NameAritySet.union (Term.functions tm) acc
    in
      fn atm => foldl f NameAritySet.empty (arguments atm)
    end;

val functionNames =
    let
      fun f (tm,acc) = NameSet.union (Term.functionNames tm) acc
    in
      fn atm => foldl f NameSet.empty (arguments atm)
    end;

(* Binary relations *)

fun mkBinop p (a,b) : atom = (p,[a,b]);

fun destBinop p (x,[a,b]) =
    if x = p then (a,b) else raise Error "Atom.destBinop: wrong binop"
  | destBinop _ _ = raise Error "Atom.destBinop: not a binop";

fun isBinop p = can (destBinop p);

(* ------------------------------------------------------------------------- *)
(* The size of an atom in symbols.                                           *)
(* ------------------------------------------------------------------------- *)

fun symbols atm = foldl (fn (tm,z) => Term.symbols tm + z) 1 (arguments atm);

(* ------------------------------------------------------------------------- *)
(* A total comparison function for atoms.                                    *)
(* ------------------------------------------------------------------------- *)

fun compare ((p1,tms1),(p2,tms2)) =
    case Name.compare (p1,p2) of
      LESS => LESS
    | EQUAL => lexCompare Term.compare (tms1,tms2)
    | GREATER => GREATER;

(* ------------------------------------------------------------------------- *)
(* Subterms.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun subterm _ [] = raise Bug "Atom.subterm: empty path"
  | subterm ((_,tms) : atom) (h :: t) =
    if h >= length tms then raise Error "Atom.subterm: bad path"
    else Term.subterm (List.nth (tms,h)) t;

fun subterms ((_,tms) : atom) =
    let
      fun f ((n,tm),l) = map (fn (p,s) => (n :: p, s)) (Term.subterms tm) @ l
    in
      foldl f [] (enumerate tms)
    end;

fun replace _ ([],_) = raise Bug "Atom.replace: empty path"
  | replace (atm as (rel,tms)) (h :: t, res) : atom =
    if h >= length tms then raise Error "Atom.replace: bad path"
    else
      let
        val tm = List.nth (tms,h)
        val tm' = Term.replace tm (t,res)
      in
        if Sharing.pointerEqual (tm,tm') then atm
        else (rel, updateNth (h,tm') tms)
      end;

fun find pred =
    let
      fun f (i,tm) =
          case Term.find pred tm of
            SOME path => SOME (i :: path)
          | NONE => NONE
    in
      fn (_,tms) : atom => first f (enumerate tms)
    end;

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

fun freeIn v atm = List.exists (Term.freeIn v) (arguments atm);

val freeVars =
    let
      fun f (tm,acc) = NameSet.union (Term.freeVars tm) acc
    in
      fn atm => foldl f NameSet.empty (arguments atm)
    end;

(* ------------------------------------------------------------------------- *)
(* Substitutions.                                                            *)
(* ------------------------------------------------------------------------- *)

fun subst sub (atm as (p,tms)) : atom =
    let
      val tms' = Sharing.map (Subst.subst sub) tms
    in
      if Sharing.pointerEqual (tms',tms) then atm else (p,tms')
    end;

(* ------------------------------------------------------------------------- *)
(* Matching.                                                                 *)
(* ------------------------------------------------------------------------- *)

local
  fun matchArg ((tm1,tm2),sub) = Subst.match sub tm1 tm2;
in
  fun match sub (p1,tms1) (p2,tms2) =
      let
        val _ = (p1 = p2 andalso length tms1 = length tms2) orelse
                raise Error "Atom.match"
      in
        foldl matchArg sub (zip tms1 tms2)
      end;
end;

(* ------------------------------------------------------------------------- *)
(* Unification.                                                              *)
(* ------------------------------------------------------------------------- *)

local
  fun unifyArg ((tm1,tm2),sub) = Subst.unify sub tm1 tm2;
in
  fun unify sub (p1,tms1) (p2,tms2) =
      let
        val _ = (p1 = p2 andalso length tms1 = length tms2) orelse
                raise Error "Atom.unify"
      in
        foldl unifyArg sub (zip tms1 tms2)
      end;
end;

(* ------------------------------------------------------------------------- *)
(* The equality relation.                                                    *)
(* ------------------------------------------------------------------------- *)

val eqName = "=";

val eqArity = 2;

val eqRelation = (eqName,eqArity);

val mkEq = mkBinop eqName;

fun destEq x = destBinop eqName x;

fun isEq x = isBinop eqName x;

fun mkRefl tm = mkEq (tm,tm);

fun destRefl atm =
    let
      val (l,r) = destEq atm
      val _ = l = r orelse raise Error "Atom.destRefl"
    in
      l
    end;

fun isRefl x = can destRefl x;

fun sym atm =
    let
      val (l,r) = destEq atm
      val _ = l <> r orelse raise Error "Atom.sym: refl"
    in
      mkEq (r,l)
    end;

fun lhs atm = fst (destEq atm);

fun rhs atm = snd (destEq atm);

(* ------------------------------------------------------------------------- *)
(* Special support for terms with type annotations.                          *)
(* ------------------------------------------------------------------------- *)

fun typedSymbols ((_,tms) : atom) =
    foldl (fn (tm,z) => Term.typedSymbols tm + z) 1 tms;

fun nonVarTypedSubterms (_,tms) =
    let
      fun addArg ((n,arg),acc) =
          let
            fun addTm ((path,tm),acc) = (n :: path, tm) :: acc
          in
            foldl addTm acc (Term.nonVarTypedSubterms arg)
          end
    in
      foldl addArg [] (enumerate tms)
    end;

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty printing.                                              *)
(* ------------------------------------------------------------------------- *)

val pp = Parser.ppMap Term.Fn Term.pp;

val toString = Parser.toString pp;

fun fromString s = Term.destFn (Term.fromString s);

val parse = Parser.parseQuotation Term.toString fromString;

end

structure AtomOrdered =
struct type t = Atom.atom val compare = Atom.compare end

structure AtomSet = ElementSet (AtomOrdered);

structure AtomMap = KeyMap (AtomOrdered);
end;

(**** Original file: Formula.sig ****)

(* ========================================================================= *)
(* FIRST ORDER LOGIC FORMULAS                                                *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Formula =
sig

(* ------------------------------------------------------------------------- *)
(* A type of first order logic formulas.                                     *)
(* ------------------------------------------------------------------------- *)

datatype formula =
    True
  | False
  | Atom of Metis.Atom.atom
  | Not of formula
  | And of formula * formula
  | Or of formula * formula
  | Imp of formula * formula
  | Iff of formula * formula
  | Forall of Metis.Term.var * formula
  | Exists of Metis.Term.var * formula

(* ------------------------------------------------------------------------- *)
(* Constructors and destructors.                                             *)
(* ------------------------------------------------------------------------- *)

(* Booleans *)

val mkBoolean : bool -> formula

val destBoolean : formula -> bool

val isBoolean : formula -> bool

(* Functions *)

val functions : formula -> Metis.NameAritySet.set

val functionNames : formula -> Metis.NameSet.set

(* Relations *)

val relations : formula -> Metis.NameAritySet.set

val relationNames : formula -> Metis.NameSet.set

(* Atoms *)

val destAtom : formula -> Metis.Atom.atom

val isAtom : formula -> bool

(* Negations *)

val destNeg : formula -> formula

val isNeg : formula -> bool

val stripNeg : formula -> int * formula

(* Conjunctions *)

val listMkConj : formula list -> formula

val stripConj : formula -> formula list

val flattenConj : formula -> formula list

(* Disjunctions *)

val listMkDisj : formula list -> formula

val stripDisj : formula -> formula list

val flattenDisj : formula -> formula list

(* Equivalences *)

val listMkEquiv : formula list -> formula

val stripEquiv : formula -> formula list

val flattenEquiv : formula -> formula list

(* Universal quantification *)

val destForall : formula -> Metis.Term.var * formula

val isForall : formula -> bool

val listMkForall : Metis.Term.var list * formula -> formula

val stripForall : formula -> Metis.Term.var list * formula

(* Existential quantification *)

val destExists : formula -> Metis.Term.var * formula

val isExists : formula -> bool

val listMkExists : Metis.Term.var list * formula -> formula

val stripExists : formula -> Metis.Term.var list * formula

(* ------------------------------------------------------------------------- *)
(* The size of a formula in symbols.                                         *)
(* ------------------------------------------------------------------------- *)

val symbols : formula -> int

(* ------------------------------------------------------------------------- *)
(* A total comparison function for formulas.                                 *)
(* ------------------------------------------------------------------------- *)

val compare : formula * formula -> order

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

val freeIn : Metis.Term.var -> formula -> bool

val freeVars : formula -> Metis.NameSet.set

val specialize : formula -> formula

val generalize : formula -> formula

(* ------------------------------------------------------------------------- *)
(* Substitutions.                                                            *)
(* ------------------------------------------------------------------------- *)

val subst : Metis.Subst.subst -> formula -> formula

(* ------------------------------------------------------------------------- *)
(* The equality relation.                                                    *)
(* ------------------------------------------------------------------------- *)

val mkEq : Metis.Term.term * Metis.Term.term -> formula

val destEq : formula -> Metis.Term.term * Metis.Term.term

val isEq : formula -> bool

val mkNeq : Metis.Term.term * Metis.Term.term -> formula

val destNeq : formula -> Metis.Term.term * Metis.Term.term

val isNeq : formula -> bool

val mkRefl : Metis.Term.term -> formula

val destRefl : formula -> Metis.Term.term

val isRefl : formula -> bool

val sym : formula -> formula  (* raises Error if given a refl *)

val lhs : formula -> Metis.Term.term

val rhs : formula -> Metis.Term.term

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty-printing.                                              *)
(* ------------------------------------------------------------------------- *)

type quotation = formula Metis.Parser.quotation

val pp : formula Metis.Parser.pp

val toString : formula -> string

val fromString : string -> formula

val parse : quotation -> formula

end

(**** Original file: Formula.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* FIRST ORDER LOGIC FORMULAS                                                *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Formula :> Formula =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* A type of first order logic formulas.                                     *)
(* ------------------------------------------------------------------------- *)

datatype formula =
    True
  | False
  | Atom of Atom.atom
  | Not of formula
  | And of formula * formula
  | Or of formula * formula
  | Imp of formula * formula
  | Iff of formula * formula
  | Forall of Term.var * formula
  | Exists of Term.var * formula;

(* ------------------------------------------------------------------------- *)
(* Constructors and destructors.                                             *)
(* ------------------------------------------------------------------------- *)

(* Booleans *)

fun mkBoolean true = True
  | mkBoolean false = False;

fun destBoolean True = true
  | destBoolean False = false
  | destBoolean _ = raise Error "destBoolean";

val isBoolean = can destBoolean;

(* Functions *)

local
  fun funcs fs [] = fs
    | funcs fs (True :: fms) = funcs fs fms
    | funcs fs (False :: fms) = funcs fs fms
    | funcs fs (Atom atm :: fms) =
      funcs (NameAritySet.union (Atom.functions atm) fs) fms
    | funcs fs (Not p :: fms) = funcs fs (p :: fms)
    | funcs fs (And (p,q) :: fms) = funcs fs (p :: q :: fms)
    | funcs fs (Or (p,q) :: fms) = funcs fs (p :: q :: fms)
    | funcs fs (Imp (p,q) :: fms) = funcs fs (p :: q :: fms)
    | funcs fs (Iff (p,q) :: fms) = funcs fs (p :: q :: fms)
    | funcs fs (Forall (_,p) :: fms) = funcs fs (p :: fms)
    | funcs fs (Exists (_,p) :: fms) = funcs fs (p :: fms);
in
  fun functions fm = funcs NameAritySet.empty [fm];
end;

local
  fun funcs fs [] = fs
    | funcs fs (True :: fms) = funcs fs fms
    | funcs fs (False :: fms) = funcs fs fms
    | funcs fs (Atom atm :: fms) =
      funcs (NameSet.union (Atom.functionNames atm) fs) fms
    | funcs fs (Not p :: fms) = funcs fs (p :: fms)
    | funcs fs (And (p,q) :: fms) = funcs fs (p :: q :: fms)
    | funcs fs (Or (p,q) :: fms) = funcs fs (p :: q :: fms)
    | funcs fs (Imp (p,q) :: fms) = funcs fs (p :: q :: fms)
    | funcs fs (Iff (p,q) :: fms) = funcs fs (p :: q :: fms)
    | funcs fs (Forall (_,p) :: fms) = funcs fs (p :: fms)
    | funcs fs (Exists (_,p) :: fms) = funcs fs (p :: fms);
in
  fun functionNames fm = funcs NameSet.empty [fm];
end;

(* Relations *)

local
  fun rels fs [] = fs
    | rels fs (True :: fms) = rels fs fms
    | rels fs (False :: fms) = rels fs fms
    | rels fs (Atom atm :: fms) =
      rels (NameAritySet.add fs (Atom.relation atm)) fms
    | rels fs (Not p :: fms) = rels fs (p :: fms)
    | rels fs (And (p,q) :: fms) = rels fs (p :: q :: fms)
    | rels fs (Or (p,q) :: fms) = rels fs (p :: q :: fms)
    | rels fs (Imp (p,q) :: fms) = rels fs (p :: q :: fms)
    | rels fs (Iff (p,q) :: fms) = rels fs (p :: q :: fms)
    | rels fs (Forall (_,p) :: fms) = rels fs (p :: fms)
    | rels fs (Exists (_,p) :: fms) = rels fs (p :: fms);
in
  fun relations fm = rels NameAritySet.empty [fm];
end;

local
  fun rels fs [] = fs
    | rels fs (True :: fms) = rels fs fms
    | rels fs (False :: fms) = rels fs fms
    | rels fs (Atom atm :: fms) = rels (NameSet.add fs (Atom.name atm)) fms
    | rels fs (Not p :: fms) = rels fs (p :: fms)
    | rels fs (And (p,q) :: fms) = rels fs (p :: q :: fms)
    | rels fs (Or (p,q) :: fms) = rels fs (p :: q :: fms)
    | rels fs (Imp (p,q) :: fms) = rels fs (p :: q :: fms)
    | rels fs (Iff (p,q) :: fms) = rels fs (p :: q :: fms)
    | rels fs (Forall (_,p) :: fms) = rels fs (p :: fms)
    | rels fs (Exists (_,p) :: fms) = rels fs (p :: fms);
in
  fun relationNames fm = rels NameSet.empty [fm];
end;

(* Atoms *)

fun destAtom (Atom atm) = atm
  | destAtom _ = raise Error "Formula.destAtom";

val isAtom = can destAtom;

(* Negations *)

fun destNeg (Not p) = p
  | destNeg _ = raise Error "Formula.destNeg";

val isNeg = can destNeg;

val stripNeg =
    let
      fun strip n (Not fm) = strip (n + 1) fm
        | strip n fm = (n,fm)
    in
      strip 0
    end;

(* Conjunctions *)

fun listMkConj fms =
    case rev fms of [] => True | fm :: fms => foldl And fm fms;

local
  fun strip cs (And (p,q)) = strip (p :: cs) q
    | strip cs fm = rev (fm :: cs);
in
  fun stripConj True = []
    | stripConj fm = strip [] fm;
end;

val flattenConj =
    let
      fun flat acc [] = acc
        | flat acc (And (p,q) :: fms) = flat acc (q :: p :: fms)
        | flat acc (True :: fms) = flat acc fms
        | flat acc (fm :: fms) = flat (fm :: acc) fms
    in
      fn fm => flat [] [fm]
    end;

(* Disjunctions *)

fun listMkDisj fms =
    case rev fms of [] => False | fm :: fms => foldl Or fm fms;

local
  fun strip cs (Or (p,q)) = strip (p :: cs) q
    | strip cs fm = rev (fm :: cs);
in
  fun stripDisj False = []
    | stripDisj fm = strip [] fm;
end;

val flattenDisj =
    let
      fun flat acc [] = acc
        | flat acc (Or (p,q) :: fms) = flat acc (q :: p :: fms)
        | flat acc (False :: fms) = flat acc fms
        | flat acc (fm :: fms) = flat (fm :: acc) fms
    in
      fn fm => flat [] [fm]
    end;

(* Equivalences *)

fun listMkEquiv fms =
    case rev fms of [] => True | fm :: fms => foldl Iff fm fms;

local
  fun strip cs (Iff (p,q)) = strip (p :: cs) q
    | strip cs fm = rev (fm :: cs);
in
  fun stripEquiv True = []
    | stripEquiv fm = strip [] fm;
end;

val flattenEquiv =
    let
      fun flat acc [] = acc
        | flat acc (Iff (p,q) :: fms) = flat acc (q :: p :: fms)
        | flat acc (True :: fms) = flat acc fms
        | flat acc (fm :: fms) = flat (fm :: acc) fms
    in
      fn fm => flat [] [fm]
    end;

(* Universal quantifiers *)

fun destForall (Forall v_f) = v_f
  | destForall _ = raise Error "destForall";

val isForall = can destForall;

fun listMkForall ([],body) = body
  | listMkForall (v :: vs, body) = Forall (v, listMkForall (vs,body));

local
  fun strip vs (Forall (v,b)) = strip (v :: vs) b
    | strip vs tm = (rev vs, tm);
in
  val stripForall = strip [];
end;

(* Existential quantifiers *)

fun destExists (Exists v_f) = v_f
  | destExists _ = raise Error "destExists";

val isExists = can destExists;

fun listMkExists ([],body) = body
  | listMkExists (v :: vs, body) = Exists (v, listMkExists (vs,body));

local
  fun strip vs (Exists (v,b)) = strip (v :: vs) b
    | strip vs tm = (rev vs, tm);
in
  val stripExists = strip [];
end;

(* ------------------------------------------------------------------------- *)
(* The size of a formula in symbols.                                         *)
(* ------------------------------------------------------------------------- *)

local
  fun sz n [] = n
    | sz n (True :: fms) = sz (n + 1) fms
    | sz n (False :: fms) = sz (n + 1) fms
    | sz n (Atom atm :: fms) = sz (n + Atom.symbols atm) fms
    | sz n (Not p :: fms) = sz (n + 1) (p :: fms)
    | sz n (And (p,q) :: fms) = sz (n + 1) (p :: q :: fms)
    | sz n (Or (p,q) :: fms) = sz (n + 1) (p :: q :: fms)
    | sz n (Imp (p,q) :: fms) = sz (n + 1) (p :: q :: fms)
    | sz n (Iff (p,q) :: fms) = sz (n + 1) (p :: q :: fms)
    | sz n (Forall (_,p) :: fms) = sz (n + 1) (p :: fms)
    | sz n (Exists (_,p) :: fms) = sz (n + 1) (p :: fms);
in
  fun symbols fm = sz 0 [fm];
end;

(* ------------------------------------------------------------------------- *)
(* A total comparison function for formulas.                                 *)
(* ------------------------------------------------------------------------- *)

local
  fun cmp [] = EQUAL
    | cmp ((True,True) :: l) = cmp l
    | cmp ((True,_) :: _) = LESS
    | cmp ((_,True) :: _) = GREATER
    | cmp ((False,False) :: l) = cmp l
    | cmp ((False,_) :: _) = LESS
    | cmp ((_,False) :: _) = GREATER
    | cmp ((Atom atm1, Atom atm2) :: l) =
      (case Atom.compare (atm1,atm2) of
         LESS => LESS
       | EQUAL => cmp l
       | GREATER => GREATER)
    | cmp ((Atom _, _) :: _) = LESS
    | cmp ((_, Atom _) :: _) = GREATER
    | cmp ((Not p1, Not p2) :: l) = cmp ((p1,p2) :: l)
    | cmp ((Not _, _) :: _) = LESS
    | cmp ((_, Not _) :: _) = GREATER
    | cmp ((And (p1,q1), And (p2,q2)) :: l) = cmp ((p1,p2) :: (q1,q2) :: l)
    | cmp ((And _, _) :: _) = LESS
    | cmp ((_, And _) :: _) = GREATER
    | cmp ((Or (p1,q1), Or (p2,q2)) :: l) = cmp ((p1,p2) :: (q1,q2) :: l)
    | cmp ((Or _, _) :: _) = LESS
    | cmp ((_, Or _) :: _) = GREATER
    | cmp ((Imp (p1,q1), Imp (p2,q2)) :: l) = cmp ((p1,p2) :: (q1,q2) :: l)
    | cmp ((Imp _, _) :: _) = LESS
    | cmp ((_, Imp _) :: _) = GREATER
    | cmp ((Iff (p1,q1), Iff (p2,q2)) :: l) = cmp ((p1,p2) :: (q1,q2) :: l)
    | cmp ((Iff _, _) :: _) = LESS
    | cmp ((_, Iff _) :: _) = GREATER
    | cmp ((Forall (v1,p1), Forall (v2,p2)) :: l) =
      (case Name.compare (v1,v2) of
         LESS => LESS
       | EQUAL => cmp ((p1,p2) :: l)
       | GREATER => GREATER)
    | cmp ((Forall _, Exists _) :: _) = LESS
    | cmp ((Exists _, Forall _) :: _) = GREATER
    | cmp ((Exists (v1,p1), Exists (v2,p2)) :: l) =
      (case Name.compare (v1,v2) of
         LESS => LESS
       | EQUAL => cmp ((p1,p2) :: l)
       | GREATER => GREATER);
in
  fun compare fm1_fm2 = cmp [fm1_fm2];
end;

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

fun freeIn v =
    let
      fun f [] = false
        | f (True :: fms) = f fms
        | f (False :: fms) = f fms
        | f (Atom atm :: fms) = Atom.freeIn v atm orelse f fms
        | f (Not p :: fms) = f (p :: fms)
        | f (And (p,q) :: fms) = f (p :: q :: fms)
        | f (Or (p,q) :: fms) = f (p :: q :: fms)
        | f (Imp (p,q) :: fms) = f (p :: q :: fms)
        | f (Iff (p,q) :: fms) = f (p :: q :: fms)
        | f (Forall (w,p) :: fms) = if v = w then f fms else f (p :: fms)
        | f (Exists (w,p) :: fms) = if v = w then f fms else f (p :: fms)
    in
      fn fm => f [fm]
    end;

local
  fun fv vs [] = vs
    | fv vs ((_,True) :: fms) = fv vs fms
    | fv vs ((_,False) :: fms) = fv vs fms
    | fv vs ((bv, Atom atm) :: fms) =
      fv (NameSet.union vs (NameSet.difference (Atom.freeVars atm) bv)) fms
    | fv vs ((bv, Not p) :: fms) = fv vs ((bv,p) :: fms)
    | fv vs ((bv, And (p,q)) :: fms) = fv vs ((bv,p) :: (bv,q) :: fms)
    | fv vs ((bv, Or (p,q)) :: fms) = fv vs ((bv,p) :: (bv,q) :: fms)
    | fv vs ((bv, Imp (p,q)) :: fms) = fv vs ((bv,p) :: (bv,q) :: fms)
    | fv vs ((bv, Iff (p,q)) :: fms) = fv vs ((bv,p) :: (bv,q) :: fms)
    | fv vs ((bv, Forall (v,p)) :: fms) = fv vs ((NameSet.add bv v, p) :: fms)
    | fv vs ((bv, Exists (v,p)) :: fms) = fv vs ((NameSet.add bv v, p) :: fms);
in
  fun freeVars fm = fv NameSet.empty [(NameSet.empty,fm)];
end;

fun specialize fm = snd (stripForall fm);

fun generalize fm = listMkForall (NameSet.toList (freeVars fm), fm);

(* ------------------------------------------------------------------------- *)
(* Substitutions.                                                            *)
(* ------------------------------------------------------------------------- *)

local
  fun substCheck sub fm = if Subst.null sub then fm else substFm sub fm

  and substFm sub fm =
      case fm of
        True => fm
      | False => fm
      | Atom (p,tms) =>
        let
          val tms' = Sharing.map (Subst.subst sub) tms
        in
          if Sharing.pointerEqual (tms,tms') then fm else Atom (p,tms')
        end
      | Not p =>
        let
          val p' = substFm sub p
        in
          if Sharing.pointerEqual (p,p') then fm else Not p'
        end
      | And (p,q) => substConn sub fm And p q
      | Or (p,q) => substConn sub fm Or p q
      | Imp (p,q) => substConn sub fm Imp p q
      | Iff (p,q) => substConn sub fm Iff p q
      | Forall (v,p) => substQuant sub fm Forall v p
      | Exists (v,p) => substQuant sub fm Exists v p

  and substConn sub fm conn p q =
      let
        val p' = substFm sub p
        and q' = substFm sub q
      in
        if Sharing.pointerEqual (p,p') andalso
           Sharing.pointerEqual (q,q')
        then fm
        else conn (p',q')
      end

  and substQuant sub fm quant v p =
      let
        val v' =
            let
              fun f (w,s) =
                  if w = v then s
                  else
                    case Subst.peek sub w of
                      NONE => NameSet.add s w
                    | SOME tm => NameSet.union s (Term.freeVars tm)
                  
              val vars = freeVars p
              val vars = NameSet.foldl f NameSet.empty vars
            in
              Term.variantPrime vars v
            end

        val sub =
            if v = v' then Subst.remove sub (NameSet.singleton v)
            else Subst.insert sub (v, Term.Var v')

        val p' = substCheck sub p
      in
        if v = v' andalso Sharing.pointerEqual (p,p') then fm
        else quant (v',p')
      end;
in
  val subst = substCheck;
end;

(* ------------------------------------------------------------------------- *)
(* The equality relation.                                                    *)
(* ------------------------------------------------------------------------- *)

fun mkEq a_b = Atom (Atom.mkEq a_b);

fun destEq fm = Atom.destEq (destAtom fm);

val isEq = can destEq;

fun mkNeq a_b = Not (mkEq a_b);

fun destNeq (Not fm) = destEq fm
  | destNeq _ = raise Error "Formula.destNeq";

val isNeq = can destNeq;

fun mkRefl tm = Atom (Atom.mkRefl tm);

fun destRefl fm = Atom.destRefl (destAtom fm);

val isRefl = can destRefl;

fun sym fm = Atom (Atom.sym (destAtom fm));

fun lhs fm = fst (destEq fm);

fun rhs fm = snd (destEq fm);

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty-printing.                                              *)
(* ------------------------------------------------------------------------- *)

type quotation = formula Parser.quotation

val truthSymbol = "T"
and falsitySymbol = "F"
and conjunctionSymbol = "/\\"
and disjunctionSymbol = "\\/"
and implicationSymbol = "==>"
and equivalenceSymbol = "<=>"
and universalSymbol = "!"
and existentialSymbol = "?";

local
  fun demote True = Term.Fn (truthSymbol,[])
    | demote False = Term.Fn (falsitySymbol,[])
    | demote (Atom (p,tms)) = Term.Fn (p,tms)
    | demote (Not p) = Term.Fn (!Term.negation, [demote p])
    | demote (And (p,q)) = Term.Fn (conjunctionSymbol, [demote p, demote q])
    | demote (Or (p,q)) = Term.Fn (disjunctionSymbol, [demote p, demote q])
    | demote (Imp (p,q)) = Term.Fn (implicationSymbol, [demote p, demote q])
    | demote (Iff (p,q)) = Term.Fn (equivalenceSymbol, [demote p, demote q])
    | demote (Forall (v,b)) = Term.Fn (universalSymbol, [Term.Var v, demote b])
    | demote (Exists (v,b)) =
      Term.Fn (existentialSymbol, [Term.Var v, demote b]);
in
  fun pp ppstrm fm = Term.pp ppstrm (demote fm);
end;

val toString = Parser.toString pp;

local
  fun isQuant [Term.Var _, _] = true
    | isQuant _ = false;

  fun promote (Term.Var v) = Atom (v,[])
    | promote (Term.Fn (f,tms)) =
      if f = truthSymbol andalso null tms then
        True
      else if f = falsitySymbol andalso null tms then
        False
      else if f = !Term.negation andalso length tms = 1 then
        Not (promote (hd tms))
      else if f = conjunctionSymbol andalso length tms = 2 then
        And (promote (hd tms), promote (List.nth (tms,1)))
      else if f = disjunctionSymbol andalso length tms = 2 then
        Or (promote (hd tms), promote (List.nth (tms,1)))
      else if f = implicationSymbol andalso length tms = 2 then
        Imp (promote (hd tms), promote (List.nth (tms,1)))
      else if f = equivalenceSymbol andalso length tms = 2 then
        Iff (promote (hd tms), promote (List.nth (tms,1)))
      else if f = universalSymbol andalso isQuant tms then
        Forall (Term.destVar (hd tms), promote (List.nth (tms,1)))
      else if f = existentialSymbol andalso isQuant tms then
        Exists (Term.destVar (hd tms), promote (List.nth (tms,1)))
      else
        Atom (f,tms);
in
  fun fromString s = promote (Term.fromString s);
end;

val parse = Parser.parseQuotation toString fromString;

end
end;

(**** Original file: Literal.sig ****)

(* ========================================================================= *)
(* FIRST ORDER LOGIC LITERALS                                                *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Literal =
sig

(* ------------------------------------------------------------------------- *)
(* A type for storing first order logic literals.                            *)
(* ------------------------------------------------------------------------- *)

type polarity = bool

type literal = polarity * Metis.Atom.atom

(* ------------------------------------------------------------------------- *)
(* Constructors and destructors.                                             *)
(* ------------------------------------------------------------------------- *)

val polarity : literal -> polarity

val atom : literal -> Metis.Atom.atom

val name : literal -> Metis.Atom.relationName

val arguments : literal -> Metis.Term.term list

val arity : literal -> int

val positive : literal -> bool

val negative : literal -> bool

val negate : literal -> literal

val relation : literal -> Metis.Atom.relation

val functions : literal -> Metis.NameAritySet.set

val functionNames : literal -> Metis.NameSet.set

(* Binary relations *)

val mkBinop : Metis.Atom.relationName -> polarity * Metis.Term.term * Metis.Term.term -> literal

val destBinop : Metis.Atom.relationName -> literal -> polarity * Metis.Term.term * Metis.Term.term

val isBinop : Metis.Atom.relationName -> literal -> bool

(* Formulas *)

val toFormula : literal -> Metis.Formula.formula

val fromFormula : Metis.Formula.formula -> literal

(* ------------------------------------------------------------------------- *)
(* The size of a literal in symbols.                                         *)
(* ------------------------------------------------------------------------- *)

val symbols : literal -> int

(* ------------------------------------------------------------------------- *)
(* A total comparison function for literals.                                 *)
(* ------------------------------------------------------------------------- *)

val compare : literal * literal -> order  (* negative < positive *)

(* ------------------------------------------------------------------------- *)
(* Subterms.                                                                 *)
(* ------------------------------------------------------------------------- *)

val subterm : literal -> Metis.Term.path -> Metis.Term.term

val subterms : literal -> (Metis.Term.path * Metis.Term.term) list

val replace : literal -> Metis.Term.path * Metis.Term.term -> literal

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

val freeIn : Metis.Term.var -> literal -> bool

val freeVars : literal -> Metis.NameSet.set

(* ------------------------------------------------------------------------- *)
(* Substitutions.                                                            *)
(* ------------------------------------------------------------------------- *)

val subst : Metis.Subst.subst -> literal -> literal

(* ------------------------------------------------------------------------- *)
(* Matching.                                                                 *)
(* ------------------------------------------------------------------------- *)

val match :  (* raises Error *)
    Metis.Subst.subst -> literal -> literal -> Metis.Subst.subst

(* ------------------------------------------------------------------------- *)
(* Unification.                                                              *)
(* ------------------------------------------------------------------------- *)

val unify :  (* raises Error *)
    Metis.Subst.subst -> literal -> literal -> Metis.Subst.subst

(* ------------------------------------------------------------------------- *)
(* The equality relation.                                                    *)
(* ------------------------------------------------------------------------- *)

val mkEq : Metis.Term.term * Metis.Term.term -> literal

val destEq : literal -> Metis.Term.term * Metis.Term.term

val isEq : literal -> bool

val mkNeq : Metis.Term.term * Metis.Term.term -> literal

val destNeq : literal -> Metis.Term.term * Metis.Term.term

val isNeq : literal -> bool

val mkRefl : Metis.Term.term -> literal

val destRefl : literal -> Metis.Term.term

val isRefl : literal -> bool

val mkIrrefl : Metis.Term.term -> literal

val destIrrefl : literal -> Metis.Term.term

val isIrrefl : literal -> bool

(* The following work with both equalities and disequalities *)

val sym : literal -> literal  (* raises Error if given a refl or irrefl *)

val lhs : literal -> Metis.Term.term

val rhs : literal -> Metis.Term.term

(* ------------------------------------------------------------------------- *)
(* Special support for terms with type annotations.                          *)
(* ------------------------------------------------------------------------- *)

val typedSymbols : literal -> int

val nonVarTypedSubterms : literal -> (Metis.Term.path * Metis.Term.term) list

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty-printing.                                              *)
(* ------------------------------------------------------------------------- *)

val pp : literal Metis.Parser.pp

val toString : literal -> string

val fromString : string -> literal

val parse : Metis.Term.term Metis.Parser.quotation -> literal

end

(**** Original file: Literal.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* FIRST ORDER LOGIC LITERALS                                                *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Literal :> Literal =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* A type for storing first order logic literals.                            *)
(* ------------------------------------------------------------------------- *)

type polarity = bool;

type literal = polarity * Atom.atom;

(* ------------------------------------------------------------------------- *)
(* Constructors and destructors.                                             *)
(* ------------------------------------------------------------------------- *)

fun polarity ((pol,_) : literal) = pol;

fun atom ((_,atm) : literal) = atm;

fun name lit = Atom.name (atom lit);

fun arguments lit = Atom.arguments (atom lit);

fun arity lit = Atom.arity (atom lit);

fun positive lit = polarity lit;

fun negative lit = not (polarity lit);

fun negate (pol,atm) : literal = (not pol, atm)

fun relation lit = Atom.relation (atom lit);

fun functions lit = Atom.functions (atom lit);

fun functionNames lit = Atom.functionNames (atom lit);

(* Binary relations *)

fun mkBinop rel (pol,a,b) : literal = (pol, Atom.mkBinop rel (a,b));

fun destBinop rel ((pol,atm) : literal) =
    case Atom.destBinop rel atm of (a,b) => (pol,a,b);

fun isBinop rel = can (destBinop rel);

(* Formulas *)

fun toFormula (true,atm) = Formula.Atom atm
  | toFormula (false,atm) = Formula.Not (Formula.Atom atm);

fun fromFormula (Formula.Atom atm) = (true,atm)
  | fromFormula (Formula.Not (Formula.Atom atm)) = (false,atm)
  | fromFormula _ = raise Error "Literal.fromFormula";

(* ------------------------------------------------------------------------- *)
(* The size of a literal in symbols.                                         *)
(* ------------------------------------------------------------------------- *)

fun symbols ((_,atm) : literal) = Atom.symbols atm;

(* ------------------------------------------------------------------------- *)
(* A total comparison function for literals.                                 *)
(* ------------------------------------------------------------------------- *)

fun compare ((pol1,atm1),(pol2,atm2)) =
    case boolCompare (pol1,pol2) of
      LESS => GREATER
    | EQUAL => Atom.compare (atm1,atm2)
    | GREATER => LESS;

(* ------------------------------------------------------------------------- *)
(* Subterms.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun subterm lit path = Atom.subterm (atom lit) path;

fun subterms lit = Atom.subterms (atom lit);

fun replace (lit as (pol,atm)) path_tm =
    let
      val atm' = Atom.replace atm path_tm
    in
      if Sharing.pointerEqual (atm,atm') then lit else (pol,atm')
    end;

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

fun freeIn v lit = Atom.freeIn v (atom lit);

fun freeVars lit = Atom.freeVars (atom lit);

(* ------------------------------------------------------------------------- *)
(* Substitutions.                                                            *)
(* ------------------------------------------------------------------------- *)

fun subst sub (lit as (pol,atm)) : literal =
    let
      val atm' = Atom.subst sub atm
    in
      if Sharing.pointerEqual (atm',atm) then lit else (pol,atm')
    end;

(* ------------------------------------------------------------------------- *)
(* Matching.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun match sub ((pol1,atm1) : literal) (pol2,atm2) =
    let
      val _ = pol1 = pol2 orelse raise Error "Literal.match"
    in
      Atom.match sub atm1 atm2
    end;

(* ------------------------------------------------------------------------- *)
(* Unification.                                                              *)
(* ------------------------------------------------------------------------- *)

fun unify sub ((pol1,atm1) : literal) (pol2,atm2) =
    let
      val _ = pol1 = pol2 orelse raise Error "Literal.unify"
    in
      Atom.unify sub atm1 atm2
    end;

(* ------------------------------------------------------------------------- *)
(* The equality relation.                                                    *)
(* ------------------------------------------------------------------------- *)

fun mkEq l_r : literal = (true, Atom.mkEq l_r);

fun destEq ((true,atm) : literal) = Atom.destEq atm
  | destEq (false,_) = raise Error "Literal.destEq";

val isEq = can destEq;

fun mkNeq l_r : literal = (false, Atom.mkEq l_r);

fun destNeq ((false,atm) : literal) = Atom.destEq atm
  | destNeq (true,_) = raise Error "Literal.destNeq";

val isNeq = can destNeq;

fun mkRefl tm = (true, Atom.mkRefl tm);

fun destRefl (true,atm) = Atom.destRefl atm
  | destRefl (false,_) = raise Error "Literal.destRefl";

val isRefl = can destRefl;

fun mkIrrefl tm = (false, Atom.mkRefl tm);

fun destIrrefl (true,_) = raise Error "Literal.destIrrefl"
  | destIrrefl (false,atm) = Atom.destRefl atm;

val isIrrefl = can destIrrefl;

fun sym (pol,atm) : literal = (pol, Atom.sym atm);

fun lhs ((_,atm) : literal) = Atom.lhs atm;

fun rhs ((_,atm) : literal) = Atom.rhs atm;

(* ------------------------------------------------------------------------- *)
(* Special support for terms with type annotations.                          *)
(* ------------------------------------------------------------------------- *)

fun typedSymbols ((_,atm) : literal) = Atom.typedSymbols atm;

fun nonVarTypedSubterms ((_,atm) : literal) = Atom.nonVarTypedSubterms atm;

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty-printing.                                              *)
(* ------------------------------------------------------------------------- *)

val pp = Parser.ppMap toFormula Formula.pp;

val toString = Parser.toString pp;

fun fromString s = fromFormula (Formula.fromString s);

val parse = Parser.parseQuotation Term.toString fromString;

end

structure LiteralOrdered =
struct type t = Literal.literal val compare = Literal.compare end

structure LiteralSet =
struct

  local
    structure S = ElementSet (LiteralOrdered);
  in
    open S;
  end;

  fun negateMember lit set = member (Literal.negate lit) set;

  val negate =
      let
        fun f (lit,set) = add set (Literal.negate lit)
      in
        foldl f empty
      end;

  val relations =
      let
        fun f (lit,set) = NameAritySet.add set (Literal.relation lit)
      in
        foldl f NameAritySet.empty
      end;

  val functions =
      let
        fun f (lit,set) = NameAritySet.union set (Literal.functions lit)
      in
        foldl f NameAritySet.empty
      end;

  val freeVars =
      let
        fun f (lit,set) = NameSet.union set (Literal.freeVars lit)
      in
        foldl f NameSet.empty
      end;

  val symbols =
      let
        fun f (lit,z) = Literal.symbols lit + z
      in
        foldl f 0
      end;

  val typedSymbols =
      let
        fun f (lit,z) = Literal.typedSymbols lit + z
      in
        foldl f 0
      end;

  fun subst sub lits =
      let
        fun substLit (lit,(eq,lits')) =
            let
              val lit' = Literal.subst sub lit
              val eq = eq andalso Sharing.pointerEqual (lit,lit')
            in
              (eq, add lits' lit')
            end
              
        val (eq,lits') = foldl substLit (true,empty) lits
      in
        if eq then lits else lits'
      end;

  val pp =
      Parser.ppMap
        toList
        (Parser.ppBracket "{" "}" (Parser.ppSequence "," Literal.pp));

end

structure LiteralMap = KeyMap (LiteralOrdered);
end;

(**** Original file: Thm.sig ****)

(* ========================================================================= *)
(* A LOGICAL KERNEL FOR FIRST ORDER CLAUSES                                  *)
(* Copyright (c) 2001-2004 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Thm =
sig

(* ------------------------------------------------------------------------- *)
(* An abstract type of first order logic theorems.                           *)
(* ------------------------------------------------------------------------- *)

type clause = Metis.LiteralSet.set

datatype inferenceType =
    Axiom
  | Assume
  | Subst
  | Factor
  | Resolve
  | Refl
  | Equality

type thm

type inference = inferenceType * thm list

(* ------------------------------------------------------------------------- *)
(* Theorem destructors.                                                      *)
(* ------------------------------------------------------------------------- *)

val clause : thm -> clause

val inference : thm -> inference

(* Tautologies *)

val isTautology : thm -> bool

(* Contradictions *)

val isContradiction : thm -> bool

(* Unit theorems *)

val destUnit : thm -> Metis.Literal.literal

val isUnit : thm -> bool

(* Unit equality theorems *)

val destUnitEq : thm -> Metis.Term.term * Metis.Term.term

val isUnitEq : thm -> bool

(* Literals *)

val member : Metis.Literal.literal -> thm -> bool

val negateMember : Metis.Literal.literal -> thm -> bool

(* ------------------------------------------------------------------------- *)
(* A total order.                                                            *)
(* ------------------------------------------------------------------------- *)

val compare : thm * thm -> order

val equal : thm -> thm -> bool

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

val freeIn : Metis.Term.var -> thm -> bool

val freeVars : thm -> Metis.NameSet.set

(* ------------------------------------------------------------------------- *)
(* Pretty-printing.                                                          *)
(* ------------------------------------------------------------------------- *)

val ppInferenceType : inferenceType Metis.Parser.pp

val inferenceTypeToString : inferenceType -> string

val pp : thm Metis.Parser.pp

val toString : thm -> string

(* ------------------------------------------------------------------------- *)
(* Primitive rules of inference.                                             *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ----- axiom C                                                             *)
(*   C                                                                       *)
(* ------------------------------------------------------------------------- *)

val axiom : clause -> thm

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ----------- assume L                                                      *)
(*   L \/ ~L                                                                 *)
(* ------------------------------------------------------------------------- *)

val assume : Metis.Literal.literal -> thm

(* ------------------------------------------------------------------------- *)
(*    C                                                                      *)
(* -------- subst s                                                          *)
(*   C[s]                                                                    *)
(* ------------------------------------------------------------------------- *)

val subst : Metis.Subst.subst -> thm -> thm

(* ------------------------------------------------------------------------- *)
(*   L \/ C    ~L \/ D                                                       *)
(* --------------------- resolve L                                           *)
(*        C \/ D                                                             *)
(*                                                                           *)
(* The literal L must occur in the first theorem, and the literal ~L must    *)
(* occur in the second theorem.                                              *)
(* ------------------------------------------------------------------------- *)

val resolve : Metis.Literal.literal -> thm -> thm -> thm

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* --------- refl t                                                          *)
(*   t = t                                                                   *)
(* ------------------------------------------------------------------------- *)

val refl : Metis.Term.term -> thm

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------ equality L p t                                   *)
(*   ~(s = t) \/ ~L \/ L'                                                    *)
(*                                                                           *)
(* where s is the subterm of L at path p, and L' is L with the subterm at    *)
(* path p being replaced by t.                                               *)
(* ------------------------------------------------------------------------- *)

val equality : Metis.Literal.literal -> Metis.Term.path -> Metis.Term.term -> thm

end

(**** Original file: Thm.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* A LOGICAL KERNEL FOR FIRST ORDER CLAUSES                                  *)
(* Copyright (c) 2001-2004 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Thm :> Thm =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* An abstract type of first order logic theorems.                           *)
(* ------------------------------------------------------------------------- *)

type clause = LiteralSet.set;

datatype inferenceType =
    Axiom
  | Assume
  | Subst
  | Factor
  | Resolve
  | Refl
  | Equality;

datatype thm = Thm of clause * (inferenceType * thm list);

type inference = inferenceType * thm list;

(* ------------------------------------------------------------------------- *)
(* Theorem destructors.                                                      *)
(* ------------------------------------------------------------------------- *)

fun clause (Thm (cl,_)) = cl;

fun inference (Thm (_,inf)) = inf;

(* Tautologies *)

local
  fun chk (_,NONE) = NONE
    | chk ((pol,atm), SOME set) =
      if (pol andalso Atom.isRefl atm) orelse AtomSet.member atm set then NONE
      else SOME (AtomSet.add set atm);
in
  fun isTautology th =
      case LiteralSet.foldl chk (SOME AtomSet.empty) (clause th) of
        SOME _ => false
      | NONE => true;
end;

(* Contradictions *)

fun isContradiction th = LiteralSet.null (clause th);

(* Unit theorems *)

fun destUnit (Thm (cl,_)) =
    if LiteralSet.size cl = 1 then LiteralSet.pick cl
    else raise Error "Thm.destUnit";

val isUnit = can destUnit;

(* Unit equality theorems *)

fun destUnitEq th = Literal.destEq (destUnit th);

val isUnitEq = can destUnitEq;

(* Literals *)

fun member lit (Thm (cl,_)) = LiteralSet.member lit cl;

fun negateMember lit (Thm (cl,_)) = LiteralSet.negateMember lit cl;

(* ------------------------------------------------------------------------- *)
(* A total order.                                                            *)
(* ------------------------------------------------------------------------- *)

fun compare (th1,th2) = LiteralSet.compare (clause th1, clause th2);

fun equal th1 th2 = LiteralSet.equal (clause th1) (clause th2);

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

fun freeIn v (Thm (cl,_)) = LiteralSet.exists (Literal.freeIn v) cl;

local
  fun free (lit,set) = NameSet.union (Literal.freeVars lit) set;
in
  fun freeVars (Thm (cl,_)) = LiteralSet.foldl free NameSet.empty cl;
end;

(* ------------------------------------------------------------------------- *)
(* Pretty-printing.                                                          *)
(* ------------------------------------------------------------------------- *)

fun inferenceTypeToString Axiom = "Axiom"
  | inferenceTypeToString Assume = "Assume"
  | inferenceTypeToString Subst = "Subst"
  | inferenceTypeToString Factor = "Factor"
  | inferenceTypeToString Resolve = "Resolve"
  | inferenceTypeToString Refl = "Refl"
  | inferenceTypeToString Equality = "Equality";

fun ppInferenceType ppstrm inf =
    Parser.ppString ppstrm (inferenceTypeToString inf);

local
  fun toFormula th =
      Formula.listMkDisj
        (map Literal.toFormula (LiteralSet.toList (clause th)));
in
  fun pp ppstrm th =
    let
      open PP
    in
      begin_block ppstrm INCONSISTENT 3;
      add_string ppstrm "|- ";
      Formula.pp ppstrm (toFormula th);
      end_block ppstrm
    end;
end;

val toString = Parser.toString pp;

(* ------------------------------------------------------------------------- *)
(* Primitive rules of inference.                                             *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ----- axiom C                                                             *)
(*   C                                                                       *)
(* ------------------------------------------------------------------------- *)

fun axiom cl = Thm (cl,(Axiom,[]));

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ----------- assume L                                                      *)
(*   L \/ ~L                                                                 *)
(* ------------------------------------------------------------------------- *)

fun assume lit =
    Thm (LiteralSet.fromList [lit, Literal.negate lit], (Assume,[]));

(* ------------------------------------------------------------------------- *)
(*    C                                                                      *)
(* -------- subst s                                                          *)
(*   C[s]                                                                    *)
(* ------------------------------------------------------------------------- *)

fun subst sub (th as Thm (cl,inf)) =
    let
      val cl' = LiteralSet.subst sub cl
    in
      if Sharing.pointerEqual (cl,cl') then th
      else
        case inf of
          (Subst,_) => Thm (cl',inf)
        | _ => Thm (cl',(Subst,[th]))
    end;

(* ------------------------------------------------------------------------- *)
(*   L \/ C    ~L \/ D                                                       *)
(* --------------------- resolve L                                           *)
(*        C \/ D                                                             *)
(*                                                                           *)
(* The literal L must occur in the first theorem, and the literal ~L must    *)
(* occur in the second theorem.                                              *)
(* ------------------------------------------------------------------------- *)

fun resolve lit (th1 as Thm (cl1,_)) (th2 as Thm (cl2,_)) =
    let
      val cl1' = LiteralSet.delete cl1 lit
      and cl2' = LiteralSet.delete cl2 (Literal.negate lit)
    in
      Thm (LiteralSet.union cl1' cl2', (Resolve,[th1,th2]))
    end;

(*DEBUG
val resolve = fn lit => fn pos => fn neg =>
    resolve lit pos neg
    handle Error err =>
      raise Error ("Thm.resolve:\nlit = " ^ Literal.toString lit ^
                   "\npos = " ^ toString pos ^
                   "\nneg = " ^ toString neg ^ "\n" ^ err);
*)

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* --------- refl t                                                          *)
(*   t = t                                                                   *)
(* ------------------------------------------------------------------------- *)

fun refl tm = Thm (LiteralSet.singleton (true, Atom.mkRefl tm), (Refl,[]));

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------ equality L p t                                   *)
(*   ~(s = t) \/ ~L \/ L'                                                    *)
(*                                                                           *)
(* where s is the subterm of L at path p, and L' is L with the subterm at    *)
(* path p being replaced by t.                                               *)
(* ------------------------------------------------------------------------- *)

fun equality lit path t =
    let
      val s = Literal.subterm lit path

      val lit' = Literal.replace lit (path,t)

      val eqLit = Literal.mkNeq (s,t)

      val cl = LiteralSet.fromList [eqLit, Literal.negate lit, lit']
    in
      Thm (cl,(Equality,[]))
    end;

end
end;

(**** Original file: Proof.sig ****)

(* ========================================================================= *)
(* PROOFS IN FIRST ORDER LOGIC                                               *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Proof =
sig

(* ------------------------------------------------------------------------- *)
(* A type of first order logic proofs.                                       *)
(* ------------------------------------------------------------------------- *)

datatype inference =
    Axiom of Metis.LiteralSet.set
  | Assume of Metis.Atom.atom
  | Subst of Metis.Subst.subst * Metis.Thm.thm
  | Resolve of Metis.Atom.atom * Metis.Thm.thm * Metis.Thm.thm
  | Refl of Metis.Term.term
  | Equality of Metis.Literal.literal * Metis.Term.path * Metis.Term.term

type proof = (Metis.Thm.thm * inference) list

(* ------------------------------------------------------------------------- *)
(* Reconstructing single inferences.                                         *)
(* ------------------------------------------------------------------------- *)

val inferenceType : inference -> Metis.Thm.inferenceType

val parents : inference -> Metis.Thm.thm list

val inferenceToThm : inference -> Metis.Thm.thm

val thmToInference : Metis.Thm.thm -> inference

(* ------------------------------------------------------------------------- *)
(* Reconstructing whole proofs.                                              *)
(* ------------------------------------------------------------------------- *)

val proof : Metis.Thm.thm -> proof

(* ------------------------------------------------------------------------- *)
(* Printing.                                                                 *)
(* ------------------------------------------------------------------------- *)

val ppInference : inference Metis.Parser.pp

val inferenceToString : inference -> string

val pp : proof Metis.Parser.pp

val toString : proof -> string

end

(**** Original file: Proof.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* PROOFS IN FIRST ORDER LOGIC                                               *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Proof :> Proof =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* A type of first order logic proofs.                                       *)
(* ------------------------------------------------------------------------- *)

datatype inference =
    Axiom of LiteralSet.set
  | Assume of Atom.atom
  | Subst of Subst.subst * Thm.thm
  | Resolve of Atom.atom * Thm.thm * Thm.thm
  | Refl of Term.term
  | Equality of Literal.literal * Term.path * Term.term;

type proof = (Thm.thm * inference) list;

(* ------------------------------------------------------------------------- *)
(* Printing.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun inferenceType (Axiom _) = Thm.Axiom
  | inferenceType (Assume _) = Thm.Assume
  | inferenceType (Subst _) = Thm.Subst
  | inferenceType (Resolve _) = Thm.Resolve
  | inferenceType (Refl _) = Thm.Refl
  | inferenceType (Equality _) = Thm.Equality;

local
  fun ppAssume pp atm = (Parser.addBreak pp (1,0); Atom.pp pp atm);

  fun ppSubst ppThm pp (sub,thm) =
      (Parser.addBreak pp (1,0);
       Parser.beginBlock pp Parser.Inconsistent 1;
       Parser.addString pp "{";
       Parser.ppBinop " =" Parser.ppString Subst.pp pp ("sub",sub);
       Parser.addString pp ",";
       Parser.addBreak pp (1,0);
       Parser.ppBinop " =" Parser.ppString ppThm pp ("thm",thm);
       Parser.addString pp "}";
       Parser.endBlock pp);

  fun ppResolve ppThm pp (res,pos,neg) =
      (Parser.addBreak pp (1,0);
       Parser.beginBlock pp Parser.Inconsistent 1;
       Parser.addString pp "{";
       Parser.ppBinop " =" Parser.ppString Atom.pp pp ("res",res);
       Parser.addString pp ",";
       Parser.addBreak pp (1,0);
       Parser.ppBinop " =" Parser.ppString ppThm pp ("pos",pos);
       Parser.addString pp ",";
       Parser.addBreak pp (1,0);
       Parser.ppBinop " =" Parser.ppString ppThm pp ("neg",neg);
       Parser.addString pp "}";
       Parser.endBlock pp);

  fun ppRefl pp tm = (Parser.addBreak pp (1,0); Term.pp pp tm);

  fun ppEquality pp (lit,path,res) =
      (Parser.addBreak pp (1,0);
       Parser.beginBlock pp Parser.Inconsistent 1;
       Parser.addString pp "{";
       Parser.ppBinop " =" Parser.ppString Literal.pp pp ("lit",lit);
       Parser.addString pp ",";
       Parser.addBreak pp (1,0);
       Parser.ppBinop " =" Parser.ppString Term.ppPath pp ("path",path);
       Parser.addString pp ",";
       Parser.addBreak pp (1,0);
       Parser.ppBinop " =" Parser.ppString Term.pp pp ("res",res);
       Parser.addString pp "}";
       Parser.endBlock pp);

  fun ppInf ppAxiom ppThm pp inf =
      let
        val infString = Thm.inferenceTypeToString (inferenceType inf)
      in
        Parser.beginBlock pp Parser.Inconsistent (size infString + 1);
        Parser.ppString pp infString;
        case inf of
          Axiom cl => ppAxiom pp cl
        | Assume x => ppAssume pp x
        | Subst x => ppSubst ppThm pp x
        | Resolve x => ppResolve ppThm pp x
        | Refl x => ppRefl pp x
        | Equality x => ppEquality pp x;
        Parser.endBlock pp
      end;

  fun ppAxiom pp cl =
      (Parser.addBreak pp (1,0);
       Parser.ppMap
         LiteralSet.toList
         (Parser.ppBracket "{" "}" (Parser.ppSequence "," Literal.pp)) pp cl);
in
  val ppInference = ppInf ppAxiom Thm.pp;

  fun pp p prf =
      let
        fun thmString n = "(" ^ Int.toString n ^ ")"
                          
        val prf = enumerate prf

        fun ppThm p th =
            let
              val cl = Thm.clause th

              fun pred (_,(th',_)) = LiteralSet.equal (Thm.clause th') cl
            in
              case List.find pred prf of
                NONE => Parser.addString p "(?)"
              | SOME (n,_) => Parser.addString p (thmString n)
            end

        fun ppStep (n,(th,inf)) =
            let
              val s = thmString n
            in
              Parser.beginBlock p Parser.Consistent (1 + size s);
              Parser.addString p (s ^ " ");
              Thm.pp p th;
              Parser.addBreak p (2,0);
              Parser.ppBracket "[" "]" (ppInf (K (K ())) ppThm) p inf;
              Parser.endBlock p;
              Parser.addNewline p
            end
      in
        Parser.beginBlock p Parser.Consistent 0;
        Parser.addString p "START OF PROOF";
        Parser.addNewline p;
        app ppStep prf;
        Parser.addString p "END OF PROOF";
        Parser.addNewline p;
        Parser.endBlock p
      end
(*DEBUG
      handle Error err => raise Bug ("Proof.pp: shouldn't fail:\n" ^ err);
*)

end;

val inferenceToString = Parser.toString ppInference;

val toString = Parser.toString pp;

(* ------------------------------------------------------------------------- *)
(* Reconstructing single inferences.                                         *)
(* ------------------------------------------------------------------------- *)

fun parents (Axiom _) = []
  | parents (Assume _) = []
  | parents (Subst (_,th)) = [th]
  | parents (Resolve (_,th,th')) = [th,th']
  | parents (Refl _) = []
  | parents (Equality _) = [];

fun inferenceToThm (Axiom cl) = Thm.axiom cl
  | inferenceToThm (Assume atm) = Thm.assume (true,atm)
  | inferenceToThm (Subst (sub,th)) = Thm.subst sub th
  | inferenceToThm (Resolve (atm,th,th')) = Thm.resolve (true,atm) th th'
  | inferenceToThm (Refl tm) = Thm.refl tm
  | inferenceToThm (Equality (lit,path,r)) = Thm.equality lit path r;

local
  fun reconstructSubst cl cl' =
      let
        fun recon [] =
            let
(*TRACE3
              val () = Parser.ppTrace LiteralSet.pp "reconstructSubst: cl" cl
              val () = Parser.ppTrace LiteralSet.pp "reconstructSubst: cl'" cl'
*)
            in
              raise Bug "can't reconstruct Subst rule"
            end
          | recon (([],sub) :: others) =
            if LiteralSet.equal (LiteralSet.subst sub cl) cl' then sub
            else recon others
          | recon ((lit :: lits, sub) :: others) =
            let
              fun checkLit (lit',acc) =
                  case total (Literal.match sub lit) lit' of
                    NONE => acc
                  | SOME sub => (lits,sub) :: acc
            in
              recon (LiteralSet.foldl checkLit others cl')
            end
      in
        Subst.normalize (recon [(LiteralSet.toList cl, Subst.empty)])
      end
(*DEBUG
      handle Error err =>
        raise Bug ("Proof.recontructSubst: shouldn't fail:\n" ^ err);
*)

  fun reconstructResolvant cl1 cl2 cl =
      (if not (LiteralSet.subset cl1 cl) then
         LiteralSet.pick (LiteralSet.difference cl1 cl)
       else if not (LiteralSet.subset cl2 cl) then
         Literal.negate (LiteralSet.pick (LiteralSet.difference cl2 cl))
       else
         (* A useless resolution, but we must reconstruct it anyway *)
         let
           val cl1' = LiteralSet.negate cl1
           and cl2' = LiteralSet.negate cl2
           val lits = LiteralSet.intersectList [cl1,cl1',cl2,cl2']
         in
           if not (LiteralSet.null lits) then LiteralSet.pick lits
           else raise Bug "can't reconstruct Resolve rule"
         end)
(*DEBUG
      handle Error err =>
        raise Bug ("Proof.recontructResolvant: shouldn't fail:\n" ^ err);
*)

  fun reconstructEquality cl =
      let
(*TRACE3
        val () = Parser.ppTrace LiteralSet.pp "Proof.reconstructEquality: cl" cl
*)

        fun sync s t path (f,a) (f',a') =
            if f <> f' orelse length a <> length a' then NONE
            else
              case List.filter (op<> o snd) (enumerate (zip a a')) of
                [(i,(tm,tm'))] =>
                let
                  val path = i :: path
                in
                  if tm = s andalso tm' = t then SOME (rev path)
                  else 
                    case (tm,tm') of
                      (Term.Fn f_a, Term.Fn f_a') => sync s t path f_a f_a'
                    | _ => NONE
                end
              | _ => NONE

        fun recon (neq,(pol,atm),(pol',atm')) =
            if pol = pol' then NONE
            else
              let
                val (s,t) = Literal.destNeq neq

                val path =
                    if s <> t then sync s t [] atm atm'
                    else if atm <> atm' then NONE
                    else Atom.find (equal s) atm
              in
                case path of
                  SOME path => SOME ((pol',atm),path,t)
                | NONE => NONE
              end

        val candidates =
            case List.partition Literal.isNeq (LiteralSet.toList cl) of
              ([l1],[l2,l3]) => [(l1,l2,l3),(l1,l3,l2)]
            | ([l1,l2],[l3]) => [(l1,l2,l3),(l1,l3,l2),(l2,l1,l3),(l2,l3,l1)]
            | ([l1],[l2]) => [(l1,l1,l2),(l1,l2,l1)]
            | _ => raise Bug "reconstructEquality: malformed"

(*TRACE3
        val ppCands =
            Parser.ppList (Parser.ppTriple Literal.pp Literal.pp Literal.pp)
        val () = Parser.ppTrace ppCands
                   "Proof.reconstructEquality: candidates" candidates
*)
      in
        case first recon candidates of
          SOME info => info
        | NONE => raise Bug "can't reconstruct Equality rule"
      end
(*DEBUG
      handle Error err =>
        raise Bug ("Proof.recontructEquality: shouldn't fail:\n" ^ err);
*)

  fun reconstruct cl (Thm.Axiom,[]) = Axiom cl
    | reconstruct cl (Thm.Assume,[]) =
      (case LiteralSet.findl Literal.positive cl of
         SOME (_,atm) => Assume atm
       | NONE => raise Bug "malformed Assume inference")
    | reconstruct cl (Thm.Subst,[th]) =
      Subst (reconstructSubst (Thm.clause th) cl, th)
    | reconstruct cl (Thm.Resolve,[th1,th2]) =
      let
        val cl1 = Thm.clause th1
        and cl2 = Thm.clause th2
        val (pol,atm) = reconstructResolvant cl1 cl2 cl
      in
        if pol then Resolve (atm,th1,th2) else Resolve (atm,th2,th1)
      end
    | reconstruct cl (Thm.Refl,[]) =
      (case LiteralSet.findl (K true) cl of
         SOME lit => Refl (Literal.destRefl lit)
       | NONE => raise Bug "malformed Refl inference")
    | reconstruct cl (Thm.Equality,[]) = Equality (reconstructEquality cl)
    | reconstruct _ _ = raise Bug "malformed inference";
in
  fun thmToInference th =
      let
(*TRACE3
        val () = Parser.ppTrace Thm.pp "Proof.thmToInference: th" th
*)

        val cl = Thm.clause th

        val thmInf = Thm.inference th

(*TRACE3
        val ppThmInf = Parser.ppPair Thm.ppInferenceType (Parser.ppList Thm.pp)
        val () = Parser.ppTrace ppThmInf "Proof.thmToInference: thmInf" thmInf
*)

        val inf = reconstruct cl thmInf

(*TRACE3
        val () = Parser.ppTrace ppInference "Proof.thmToInference: inf" inf
*)
(*DEBUG
        val () =
            let
              val th' = inferenceToThm inf
            in
              if LiteralSet.equal (Thm.clause th') cl then ()
              else
                raise
                  Bug
                    ("Proof.thmToInference: bad inference reconstruction:" ^
                     "\n  th = " ^ Thm.toString th ^
                     "\n  inf = " ^ inferenceToString inf ^
                     "\n  inf th = " ^ Thm.toString th')
            end
*)
      in
        inf
      end
(*DEBUG
      handle Error err =>
        raise Bug ("Proof.thmToInference: shouldn't fail:\n" ^ err);
*)
end;

(* ------------------------------------------------------------------------- *)
(* Reconstructing whole proofs.                                              *)
(* ------------------------------------------------------------------------- *)

local
  fun thmCompare (th1,th2) =
      LiteralSet.compare (Thm.clause th1, Thm.clause th2);

  fun buildProof (th,(m,l)) =
      if Map.inDomain th m then (m,l)
      else
        let
          val (_,deps) = Thm.inference th
          val (m,l) = foldl buildProof (m,l) deps
        in
          if Map.inDomain th m then (m,l)
          else
            let
              val l = (th, thmToInference th) :: l
            in
              (Map.insert m (th,l), l)
            end
        end;
in
  fun proof th =
      let
(*TRACE3
        val () = Parser.ppTrace Thm.pp "Proof.proof: th" th
*)
        val (m,_) = buildProof (th, (Map.new thmCompare, []))
(*TRACE3
        val () = Parser.ppTrace Parser.ppInt "Proof.proof: size" (Map.size m)
*)
      in
        case Map.peek m th of
          SOME l => rev l
        | NONE => raise Bug "Proof.proof"
      end;
end;

end
end;

(**** Original file: Rule.sig ****)

(* ========================================================================= *)
(* DERIVED RULES FOR CREATING FIRST ORDER LOGIC THEOREMS                     *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Rule =
sig

(* ------------------------------------------------------------------------- *)
(* An equation consists of two terms (t,u) plus a theorem (stronger than)    *)
(* t = u \/ C.                                                               *)
(* ------------------------------------------------------------------------- *)

type equation = (Metis.Term.term * Metis.Term.term) * Metis.Thm.thm

val ppEquation : equation Metis.Parser.pp

val equationToString : equation -> string

(* Returns t = u if the equation theorem contains this literal *)
val equationLiteral : equation -> Metis.Literal.literal option

val reflEqn : Metis.Term.term -> equation

val symEqn : equation -> equation

val transEqn : equation -> equation -> equation

(* ------------------------------------------------------------------------- *)
(* A conversion takes a term t and either:                                   *)
(* 1. Returns a term u together with a theorem (stronger than) t = u \/ C.   *)
(* 2. Raises an Error exception.                                             *)
(* ------------------------------------------------------------------------- *)

type conv = Metis.Term.term -> Metis.Term.term * Metis.Thm.thm

val allConv : conv

val noConv : conv

val thenConv : conv -> conv -> conv

val orelseConv : conv -> conv -> conv

val tryConv : conv -> conv

val repeatConv : conv -> conv

val firstConv : conv list -> conv

val everyConv : conv list -> conv

val rewrConv : equation -> Metis.Term.path -> conv

val pathConv : conv -> Metis.Term.path -> conv

val subtermConv : conv -> int -> conv

val subtermsConv : conv -> conv  (* All function arguments *)

(* ------------------------------------------------------------------------- *)
(* Applying a conversion to every subterm, with some traversal strategy.     *)
(* ------------------------------------------------------------------------- *)

val bottomUpConv : conv -> conv

val topDownConv : conv -> conv

val repeatTopDownConv : conv -> conv  (* useful for rewriting *)

(* ------------------------------------------------------------------------- *)
(* A literule (bad pun) takes a literal L and either:                        *)
(* 1. Returns a literal L' with a theorem (stronger than) ~L \/ L' \/ C.     *)
(* 2. Raises an Error exception.                                             *)
(* ------------------------------------------------------------------------- *)

type literule = Metis.Literal.literal -> Metis.Literal.literal * Metis.Thm.thm

val allLiterule : literule

val noLiterule : literule

val thenLiterule : literule -> literule -> literule

val orelseLiterule : literule -> literule -> literule

val tryLiterule : literule -> literule

val repeatLiterule : literule -> literule

val firstLiterule : literule list -> literule

val everyLiterule : literule list -> literule

val rewrLiterule : equation -> Metis.Term.path -> literule

val pathLiterule : conv -> Metis.Term.path -> literule

val argumentLiterule : conv -> int -> literule

val allArgumentsLiterule : conv -> literule

(* ------------------------------------------------------------------------- *)
(* A rule takes one theorem and either deduces another or raises an Error    *)
(* exception.                                                                *)
(* ------------------------------------------------------------------------- *)

type rule = Metis.Thm.thm -> Metis.Thm.thm

val allRule : rule

val noRule : rule

val thenRule : rule -> rule -> rule

val orelseRule : rule -> rule -> rule

val tryRule : rule -> rule

val changedRule : rule -> rule

val repeatRule : rule -> rule

val firstRule : rule list -> rule

val everyRule : rule list -> rule

val literalRule : literule -> Metis.Literal.literal -> rule

val rewrRule : equation -> Metis.Literal.literal -> Metis.Term.path -> rule

val pathRule : conv -> Metis.Literal.literal -> Metis.Term.path -> rule

val literalsRule : literule -> Metis.LiteralSet.set -> rule

val allLiteralsRule : literule -> rule

val convRule : conv -> rule  (* All arguments of all literals *)

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* --------- reflexivity                                                     *)
(*   x = x                                                                   *)
(* ------------------------------------------------------------------------- *)

val reflexivity : Metis.Thm.thm

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* --------------------- symmetry                                            *)
(*   ~(x = y) \/ y = x                                                       *)
(* ------------------------------------------------------------------------- *)

val symmetry : Metis.Thm.thm

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* --------------------------------- transitivity                            *)
(*   ~(x = y) \/ ~(y = z) \/ x = z                                           *)
(* ------------------------------------------------------------------------- *)

val transitivity : Metis.Thm.thm

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ---------------------------------------------- functionCongruence (f,n)   *)
(*   ~(x0 = y0) \/ ... \/ ~(x{n-1} = y{n-1}) \/                              *)
(*   f x0 ... x{n-1} = f y0 ... y{n-1}                                       *)
(* ------------------------------------------------------------------------- *)

val functionCongruence : Metis.Term.function -> Metis.Thm.thm

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ---------------------------------------------- relationCongruence (R,n)   *)
(*   ~(x0 = y0) \/ ... \/ ~(x{n-1} = y{n-1}) \/                              *)
(*   ~R x0 ... x{n-1} \/ R y0 ... y{n-1}                                     *)
(* ------------------------------------------------------------------------- *)

val relationCongruence : Metis.Atom.relation -> Metis.Thm.thm

(* ------------------------------------------------------------------------- *)
(*   x = y \/ C                                                              *)
(* -------------- symEq (x = y)                                              *)
(*   y = x \/ C                                                              *)
(* ------------------------------------------------------------------------- *)

val symEq : Metis.Literal.literal -> rule

(* ------------------------------------------------------------------------- *)
(*   ~(x = y) \/ C                                                           *)
(* ----------------- symNeq ~(x = y)                                         *)
(*   ~(y = x) \/ C                                                           *)
(* ------------------------------------------------------------------------- *)

val symNeq : Metis.Literal.literal -> rule

(* ------------------------------------------------------------------------- *)
(* sym (x = y) = symEq (x = y)  /\  sym ~(x = y) = symNeq ~(x = y)           *)
(* ------------------------------------------------------------------------- *)

val sym : Metis.Literal.literal -> rule

(* ------------------------------------------------------------------------- *)
(*   ~(x = x) \/ C                                                           *)
(* ----------------- removeIrrefl                                            *)
(*         C                                                                 *)
(*                                                                           *)
(* where all irreflexive equalities.                                         *)
(* ------------------------------------------------------------------------- *)

val removeIrrefl : rule

(* ------------------------------------------------------------------------- *)
(*   x = y \/ y = x \/ C                                                     *)
(* ----------------------- removeSym                                         *)
(*       x = y \/ C                                                          *)
(*                                                                           *)
(* where all duplicate copies of equalities and disequalities are removed.   *)
(* ------------------------------------------------------------------------- *)

val removeSym : rule

(* ------------------------------------------------------------------------- *)
(*   ~(v = t) \/ C                                                           *)
(* ----------------- expandAbbrevs                                           *)
(*      C[t/v]                                                               *)
(*                                                                           *)
(* where t must not contain any occurrence of the variable v.                *)
(* ------------------------------------------------------------------------- *)

val expandAbbrevs : rule

(* ------------------------------------------------------------------------- *)
(* simplify = isTautology + expandAbbrevs + removeSym                        *)
(* ------------------------------------------------------------------------- *)

val simplify : Metis.Thm.thm -> Metis.Thm.thm option

(* ------------------------------------------------------------------------- *)
(*    C                                                                      *)
(* -------- freshVars                                                        *)
(*   C[s]                                                                    *)
(*                                                                           *)
(* where s is a renaming substitution chosen so that all of the variables in *)
(* C are replaced by fresh variables.                                        *)
(* ------------------------------------------------------------------------- *)

val freshVars : rule

(* ------------------------------------------------------------------------- *)
(*               C                                                           *)
(* ---------------------------- factor                                       *)
(*   C_s_1, C_s_2, ..., C_s_n                                                *)
(*                                                                           *)
(* where each s_i is a substitution that factors C, meaning that the theorem *)
(*                                                                           *)
(*   C_s_i = (removeIrrefl o removeSym o Metis.Thm.subst s_i) C                    *)
(*                                                                           *)
(* has fewer literals than C.                                                *)
(*                                                                           *)
(* Also, if s is any substitution that factors C, then one of the s_i will   *)
(* result in a theorem C_s_i that strictly subsumes the theorem C_s.         *)
(* ------------------------------------------------------------------------- *)

val factor' : Metis.Thm.clause -> Metis.Subst.subst list

val factor : Metis.Thm.thm -> Metis.Thm.thm list

end

(**** Original file: Rule.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* DERIVED RULES FOR CREATING FIRST ORDER LOGIC THEOREMS                     *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Rule :> Rule =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* --------- reflexivity                                                     *)
(*   x = x                                                                   *)
(* ------------------------------------------------------------------------- *)

val reflexivity = Thm.refl (Term.Var "x");

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* --------------------- symmetry                                            *)
(*   ~(x = y) \/ y = x                                                       *)
(* ------------------------------------------------------------------------- *)

val symmetry =
    let
      val x = Term.Var "x"
      and y = Term.Var "y"
      val reflTh = reflexivity
      val reflLit = Thm.destUnit reflTh
      val eqTh = Thm.equality reflLit [0] y
    in
      Thm.resolve reflLit reflTh eqTh
    end;

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* --------------------------------- transitivity                            *)
(*   ~(x = y) \/ ~(y = z) \/ x = z                                           *)
(* ------------------------------------------------------------------------- *)

val transitivity =
    let
      val x = Term.Var "x"
      and y = Term.Var "y"
      and z = Term.Var "z"
      val eqTh = Thm.equality (Literal.mkEq (y,z)) [0] x
    in
      Thm.resolve (Literal.mkEq (y,x)) symmetry eqTh
    end;

(* ------------------------------------------------------------------------- *)
(*   x = y \/ C                                                              *)
(* -------------- symEq (x = y)                                              *)
(*   y = x \/ C                                                              *)
(* ------------------------------------------------------------------------- *)

fun symEq lit th =
    let
      val (x,y) = Literal.destEq lit
    in
      if x = y then th
      else
        let
          val sub = Subst.fromList [("x",x),("y",y)]
          val symTh = Thm.subst sub symmetry
        in
          Thm.resolve lit th symTh
        end
    end;

(* ------------------------------------------------------------------------- *)
(* An equation consists of two terms (t,u) plus a theorem (stronger than)    *)
(* t = u \/ C.                                                               *)
(* ------------------------------------------------------------------------- *)

type equation = (Term.term * Term.term) * Thm.thm;

fun ppEquation pp (eqn as (_,th)) = Thm.pp pp th;

fun equationToString x = Parser.toString ppEquation x;

fun equationLiteral (t_u,th) =
    let
      val lit = Literal.mkEq t_u
    in
      if LiteralSet.member lit (Thm.clause th) then SOME lit else NONE
    end;

fun reflEqn t = ((t,t), Thm.refl t);

fun symEqn (eqn as ((t,u), th)) =
    if t = u then eqn
    else
      ((u,t),
       case equationLiteral eqn of
         SOME t_u => symEq t_u th
       | NONE => th);

fun transEqn (eqn1 as ((x,y), th1)) (eqn2 as ((_,z), th2)) =
    if x = y then eqn2
    else if y = z then eqn1
    else if x = z then reflEqn x
    else
      ((x,z),
       case equationLiteral eqn1 of
         NONE => th1
       | SOME x_y =>
         case equationLiteral eqn2 of
           NONE => th2
         | SOME y_z =>
           let
             val sub = Subst.fromList [("x",x),("y",y),("z",z)]
             val th = Thm.subst sub transitivity
             val th = Thm.resolve x_y th1 th
             val th = Thm.resolve y_z th2 th
           in
             th
           end);

(*DEBUG
val transEqn = fn eqn1 => fn eqn2 =>
    transEqn eqn1 eqn2
    handle Error err =>
      raise Error ("Rule.transEqn:\neqn1 = " ^ equationToString eqn1 ^
                   "\neqn2 = " ^ equationToString eqn2 ^ "\n" ^ err);
*)

(* ------------------------------------------------------------------------- *)
(* A conversion takes a term t and either:                                   *)
(* 1. Returns a term u together with a theorem (stronger than) t = u \/ C.   *)
(* 2. Raises an Error exception.                                             *)
(* ------------------------------------------------------------------------- *)

type conv = Term.term -> Term.term * Thm.thm;

fun allConv tm = (tm, Thm.refl tm);

val noConv : conv = fn _ => raise Error "noConv";

fun traceConv s conv tm =
    let
      val res as (tm',th) = conv tm
      val () = print (s ^ ": " ^ Term.toString tm ^ " --> " ^
                      Term.toString tm' ^ " " ^ Thm.toString th ^ "\n")
    in
      res
    end
    handle Error err =>
      (print (s ^ ": " ^ Term.toString tm ^ " --> Error: " ^ err ^ "\n");
       raise Error (s ^ ": " ^ err));
    
fun thenConvTrans tm (tm',th1) (tm'',th2) =
    let
      val eqn1 = ((tm,tm'),th1)
      and eqn2 = ((tm',tm''),th2)
      val (_,th) = transEqn eqn1 eqn2
    in
      (tm'',th)
    end;

fun thenConv conv1 conv2 tm =
    let
      val res1 as (tm',_) = conv1 tm
      val res2 = conv2 tm'
    in
      thenConvTrans tm res1 res2
    end;

fun orelseConv (conv1 : conv) conv2 tm = conv1 tm handle Error _ => conv2 tm;

fun tryConv conv = orelseConv conv allConv;

fun changedConv conv tm =
    let
      val res as (tm',_) = conv tm
    in
      if tm = tm' then raise Error "changedConv" else res
    end;

fun repeatConv conv tm = tryConv (thenConv conv (repeatConv conv)) tm;

fun firstConv [] _ = raise Error "firstConv"
  | firstConv [conv] tm = conv tm
  | firstConv (conv :: convs) tm = orelseConv conv (firstConv convs) tm;

fun everyConv [] tm = allConv tm
  | everyConv [conv] tm = conv tm
  | everyConv (conv :: convs) tm = thenConv conv (everyConv convs) tm;

fun rewrConv (eqn as ((x,y), eqTh)) path tm =
    if x = y then allConv tm
    else if null path then (y,eqTh)
    else
      let
        val reflTh = Thm.refl tm
        val reflLit = Thm.destUnit reflTh
        val th = Thm.equality reflLit (1 :: path) y
        val th = Thm.resolve reflLit reflTh th
        val th =
            case equationLiteral eqn of
              NONE => th
            | SOME x_y => Thm.resolve x_y eqTh th
        val tm' = Term.replace tm (path,y)
      in
        (tm',th)
      end;

(*DEBUG
val rewrConv = fn eqn as ((x,y),eqTh) => fn path => fn tm =>
    rewrConv eqn path tm
    handle Error err =>
      raise Error ("Rule.rewrConv:\nx = " ^ Term.toString x ^
                   "\ny = " ^ Term.toString y ^
                   "\neqTh = " ^ Thm.toString eqTh ^
                   "\npath = " ^ Term.pathToString path ^
                   "\ntm = " ^ Term.toString tm ^ "\n" ^ err);
*)

fun pathConv conv path tm =
    let
      val x = Term.subterm tm path
      val (y,th) = conv x
    in
      rewrConv ((x,y),th) path tm
    end;

fun subtermConv conv i = pathConv conv [i];

fun subtermsConv _ (tm as Term.Var _) = allConv tm
  | subtermsConv conv (tm as Term.Fn (_,a)) =
    everyConv (map (subtermConv conv) (interval 0 (length a))) tm;

(* ------------------------------------------------------------------------- *)
(* Applying a conversion to every subterm, with some traversal strategy.     *)
(* ------------------------------------------------------------------------- *)

fun bottomUpConv conv tm =
    thenConv (subtermsConv (bottomUpConv conv)) (repeatConv conv) tm;

fun topDownConv conv tm =
    thenConv (repeatConv conv) (subtermsConv (topDownConv conv)) tm;

fun repeatTopDownConv conv =
    let
      fun f tm = thenConv (repeatConv conv) g tm
      and g tm = thenConv (subtermsConv f) h tm
      and h tm = tryConv (thenConv conv f) tm
    in
      f
    end;

(*DEBUG
val repeatTopDownConv = fn conv => fn tm =>
    repeatTopDownConv conv tm
    handle Error err => raise Error ("repeatTopDownConv: " ^ err);
*)

(* ------------------------------------------------------------------------- *)
(* A literule (bad pun) takes a literal L and either:                        *)
(* 1. Returns a literal L' with a theorem (stronger than) ~L \/ L' \/ C.     *)
(* 2. Raises an Error exception.                                             *)
(* ------------------------------------------------------------------------- *)

type literule = Literal.literal -> Literal.literal * Thm.thm;

fun allLiterule lit = (lit, Thm.assume lit);

val noLiterule : literule = fn _ => raise Error "noLiterule";

fun thenLiterule literule1 literule2 lit =
    let
      val res1 as (lit',th1) = literule1 lit
      val res2 as (lit'',th2) = literule2 lit'
    in
      if lit = lit' then res2
      else if lit' = lit'' then res1
      else if lit = lit'' then allLiterule lit
      else
        (lit'',
         if not (Thm.member lit' th1) then th1
         else if not (Thm.negateMember lit' th2) then th2
         else Thm.resolve lit' th1 th2)
    end;

fun orelseLiterule (literule1 : literule) literule2 lit =
    literule1 lit handle Error _ => literule2 lit;

fun tryLiterule literule = orelseLiterule literule allLiterule;

fun changedLiterule literule lit =
    let
      val res as (lit',_) = literule lit
    in
      if lit = lit' then raise Error "changedLiterule" else res
    end;

fun repeatLiterule literule lit =
    tryLiterule (thenLiterule literule (repeatLiterule literule)) lit;

fun firstLiterule [] _ = raise Error "firstLiterule"
  | firstLiterule [literule] lit = literule lit
  | firstLiterule (literule :: literules) lit =
    orelseLiterule literule (firstLiterule literules) lit;

fun everyLiterule [] lit = allLiterule lit
  | everyLiterule [literule] lit = literule lit
  | everyLiterule (literule :: literules) lit =
    thenLiterule literule (everyLiterule literules) lit;

fun rewrLiterule (eqn as ((x,y),eqTh)) path lit =
    if x = y then allLiterule lit
    else
      let
        val th = Thm.equality lit path y
        val th =
            case equationLiteral eqn of
              NONE => th
            | SOME x_y => Thm.resolve x_y eqTh th
        val lit' = Literal.replace lit (path,y)
      in
        (lit',th)
      end;

(*DEBUG
val rewrLiterule = fn eqn => fn path => fn lit =>
    rewrLiterule eqn path lit
    handle Error err =>
      raise Error ("Rule.rewrLiterule:\neqn = " ^ equationToString eqn ^
                   "\npath = " ^ Term.pathToString path ^
                   "\nlit = " ^ Literal.toString lit ^ "\n" ^ err);
*)

fun pathLiterule conv path lit =
    let
      val tm = Literal.subterm lit path
      val (tm',th) = conv tm
    in
      rewrLiterule ((tm,tm'),th) path lit
    end;

fun argumentLiterule conv i = pathLiterule conv [i];

fun allArgumentsLiterule conv lit =
    everyLiterule
      (map (argumentLiterule conv) (interval 0 (Literal.arity lit))) lit;

(* ------------------------------------------------------------------------- *)
(* A rule takes one theorem and either deduces another or raises an Error    *)
(* exception.                                                                *)
(* ------------------------------------------------------------------------- *)

type rule = Thm.thm -> Thm.thm;

val allRule : rule = fn th => th;

val noRule : rule = fn _ => raise Error "noRule";

fun thenRule (rule1 : rule) (rule2 : rule) th = rule1 (rule2 th);

fun orelseRule (rule1 : rule) rule2 th = rule1 th handle Error _ => rule2 th;

fun tryRule rule = orelseRule rule allRule;

fun changedRule rule th =
    let
      val th' = rule th
    in
      if not (LiteralSet.equal (Thm.clause th) (Thm.clause th')) then th'
      else raise Error "changedRule"
    end;

fun repeatRule rule lit = tryRule (thenRule rule (repeatRule rule)) lit;

fun firstRule [] _ = raise Error "firstRule"
  | firstRule [rule] th = rule th
  | firstRule (rule :: rules) th = orelseRule rule (firstRule rules) th;

fun everyRule [] th = allRule th
  | everyRule [rule] th = rule th
  | everyRule (rule :: rules) th = thenRule rule (everyRule rules) th;

fun literalRule literule lit th =
    let
      val (lit',litTh) = literule lit
    in
      if lit = lit' then th
      else if not (Thm.negateMember lit litTh) then litTh
      else Thm.resolve lit th litTh
    end;

(*DEBUG
val literalRule = fn literule => fn lit => fn th =>
    literalRule literule lit th
    handle Error err =>
      raise Error ("Rule.literalRule:\nlit = " ^ Literal.toString lit ^
                   "\nth = " ^ Thm.toString th ^ "\n" ^ err);
*)

fun rewrRule eqTh lit path = literalRule (rewrLiterule eqTh path) lit;

fun pathRule conv lit path = literalRule (pathLiterule conv path) lit;

fun literalsRule literule =
    let
      fun f (lit,th) =
          if Thm.member lit th then literalRule literule lit th else th
    in
      fn lits => fn th => LiteralSet.foldl f th lits
    end;

fun allLiteralsRule literule th = literalsRule literule (Thm.clause th) th;

fun convRule conv = allLiteralsRule (allArgumentsLiterule conv);
  
(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ---------------------------------------------- functionCongruence (f,n)   *)
(*   ~(x0 = y0) \/ ... \/ ~(x{n-1} = y{n-1}) \/                              *)
(*   f x0 ... x{n-1} = f y0 ... y{n-1}                                       *)
(* ------------------------------------------------------------------------- *)

fun functionCongruence (f,n) =
    let
      val xs = List.tabulate (n, fn i => Term.Var ("x" ^ Int.toString i))
      and ys = List.tabulate (n, fn i => Term.Var ("y" ^ Int.toString i))

      fun cong ((i,yi),(th,lit)) =
          let
            val path = [1,i]
            val th = Thm.resolve lit th (Thm.equality lit path yi)
            val lit = Literal.replace lit (path,yi)
          in
            (th,lit)
          end

      val reflTh = Thm.refl (Term.Fn (f,xs))
      val reflLit = Thm.destUnit reflTh
    in
      fst (foldl cong (reflTh,reflLit) (enumerate ys))
    end;

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ---------------------------------------------- relationCongruence (R,n)   *)
(*   ~(x0 = y0) \/ ... \/ ~(x{n-1} = y{n-1}) \/                              *)
(*   ~R x0 ... x{n-1} \/ R y0 ... y{n-1}                                     *)
(* ------------------------------------------------------------------------- *)

fun relationCongruence (R,n) =
    let
      val xs = List.tabulate (n, fn i => Term.Var ("x" ^ Int.toString i))
      and ys = List.tabulate (n, fn i => Term.Var ("y" ^ Int.toString i))

      fun cong ((i,yi),(th,lit)) =
          let
            val path = [i]
            val th = Thm.resolve lit th (Thm.equality lit path yi)
            val lit = Literal.replace lit (path,yi)
          in
            (th,lit)
          end

      val assumeLit = (false,(R,xs))
      val assumeTh = Thm.assume assumeLit
    in
      fst (foldl cong (assumeTh,assumeLit) (enumerate ys))
    end;

(* ------------------------------------------------------------------------- *)
(*   ~(x = y) \/ C                                                           *)
(* ----------------- symNeq ~(x = y)                                         *)
(*   ~(y = x) \/ C                                                           *)
(* ------------------------------------------------------------------------- *)

fun symNeq lit th =
    let
      val (x,y) = Literal.destNeq lit
    in
      if x = y then th
      else
        let
          val sub = Subst.fromList [("x",y),("y",x)]
          val symTh = Thm.subst sub symmetry
        in
          Thm.resolve lit th symTh
        end
    end;

(* ------------------------------------------------------------------------- *)
(* sym (x = y) = symEq (x = y)  /\  sym ~(x = y) = symNeq ~(x = y)           *)
(* ------------------------------------------------------------------------- *)

fun sym (lit as (pol,_)) th = if pol then symEq lit th else symNeq lit th;

(* ------------------------------------------------------------------------- *)
(*   ~(x = x) \/ C                                                           *)
(* ----------------- removeIrrefl                                            *)
(*         C                                                                 *)
(*                                                                           *)
(* where all irreflexive equalities.                                         *)
(* ------------------------------------------------------------------------- *)

local
  fun irrefl ((true,_),th) = th
    | irrefl (lit as (false,atm), th) =
      case total Atom.destRefl atm of
        SOME x => Thm.resolve lit th (Thm.refl x)
      | NONE => th;
in
  fun removeIrrefl th = LiteralSet.foldl irrefl th (Thm.clause th);
end;

(* ------------------------------------------------------------------------- *)
(*   x = y \/ y = x \/ C                                                     *)
(* ----------------------- removeSym                                         *)
(*       x = y \/ C                                                          *)
(*                                                                           *)
(* where all duplicate copies of equalities and disequalities are removed.   *)
(* ------------------------------------------------------------------------- *)

local
  fun rem (lit as (pol,atm), eqs_th as (eqs,th)) =
      case total Atom.sym atm of
        NONE => eqs_th
      | SOME atm' =>
        if LiteralSet.member lit eqs then
          (eqs, if pol then symEq lit th else symNeq lit th)
        else
          (LiteralSet.add eqs (pol,atm'), th);
in
  fun removeSym th =
      snd (LiteralSet.foldl rem (LiteralSet.empty,th) (Thm.clause th));
end;

(* ------------------------------------------------------------------------- *)
(*   ~(v = t) \/ C                                                           *)
(* ----------------- expandAbbrevs                                           *)
(*      C[t/v]                                                               *)
(*                                                                           *)
(* where t must not contain any occurrence of the variable v.                *)
(* ------------------------------------------------------------------------- *)

local
  fun expand lit =
      let
        val (x,y) = Literal.destNeq lit
      in
        if (Term.isTypedVar x orelse Term.isTypedVar y) andalso x <> y then
          Subst.unify Subst.empty x y
        else raise Error "expand"
      end;
in
  fun expandAbbrevs th =
      case LiteralSet.firstl (total expand) (Thm.clause th) of
        NONE => removeIrrefl th
      | SOME sub => expandAbbrevs (Thm.subst sub th);
end;

(* ------------------------------------------------------------------------- *)
(* simplify = isTautology + expandAbbrevs + removeSym                        *)
(* ------------------------------------------------------------------------- *)

fun simplify th =
    if Thm.isTautology th then NONE
    else
      let
        val th' = th
        val th' = expandAbbrevs th'
        val th' = removeSym th'
      in
        if Thm.equal th th' then SOME th else simplify th'
      end;

(* ------------------------------------------------------------------------- *)
(*    C                                                                      *)
(* -------- freshVars                                                        *)
(*   C[s]                                                                    *)
(*                                                                           *)
(* where s is a renaming substitution chosen so that all of the variables in *)
(* C are replaced by fresh variables.                                        *)
(* ------------------------------------------------------------------------- *)

fun freshVars th = Thm.subst (Subst.freshVars (Thm.freeVars th)) th;

(* ------------------------------------------------------------------------- *)
(*               C                                                           *)
(* ---------------------------- factor                                       *)
(*   C_s_1, C_s_2, ..., C_s_n                                                *)
(*                                                                           *)
(* where each s_i is a substitution that factors C, meaning that the theorem *)
(*                                                                           *)
(*   C_s_i = (removeIrrefl o removeSym o Thm.subst s_i) C                    *)
(*                                                                           *)
(* has fewer literals than C.                                                *)
(*                                                                           *)
(* Also, if s is any substitution that factors C, then one of the s_i will   *)
(* result in a theorem C_s_i that strictly subsumes the theorem C_s.         *)
(* ------------------------------------------------------------------------- *)

local
  datatype edge =
      FactorEdge of Atom.atom * Atom.atom
    | ReflEdge of Term.term * Term.term;

  fun ppEdge p (FactorEdge atm_atm') = Parser.ppPair Atom.pp Atom.pp p atm_atm'
    | ppEdge p (ReflEdge tm_tm') = Parser.ppPair Term.pp Term.pp p tm_tm';

  datatype joinStatus =
      Joined
    | Joinable of Subst.subst
    | Apart;

  fun joinEdge sub edge =
      let
        val result =
            case edge of
              FactorEdge (atm,atm') => total (Atom.unify sub atm) atm'
            | ReflEdge (tm,tm') => total (Subst.unify sub tm) tm'
      in
        case result of
          NONE => Apart
        | SOME sub' =>
          if Portable.pointerEqual (sub,sub') then Joined else Joinable sub'
      end;

  fun updateApart sub =
      let
        fun update acc [] = SOME acc
          | update acc (edge :: edges) =
            case joinEdge sub edge of
              Joined => NONE
            | Joinable _ => update (edge :: acc) edges
            | Apart => update acc edges
      in
        update []
      end;

  fun addFactorEdge (pol,atm) ((pol',atm'),acc) =
      if pol <> pol' then acc
      else
        let
          val edge = FactorEdge (atm,atm')
        in
          case joinEdge Subst.empty edge of
            Joined => raise Bug "addFactorEdge: joined"
          | Joinable sub => (sub,edge) :: acc
          | Apart => acc
        end;

  fun addReflEdge (false,_) acc = acc
    | addReflEdge (true,atm) acc =
      let
        val edge = ReflEdge (Atom.destEq atm)
      in
        case joinEdge Subst.empty edge of
          Joined => raise Bug "addRefl: joined"
        | Joinable _ => edge :: acc
        | Apart => acc
      end;

  fun addIrreflEdge (true,_) acc = acc
    | addIrreflEdge (false,atm) acc =
      let
        val edge = ReflEdge (Atom.destEq atm)
      in
        case joinEdge Subst.empty edge of
          Joined => raise Bug "addRefl: joined"
        | Joinable sub => (sub,edge) :: acc
        | Apart => acc
      end;

  fun init_edges acc _ [] =
      let
        fun init ((apart,sub,edge),(edges,acc)) =
            (edge :: edges, (apart,sub,edges) :: acc)
      in
        snd (List.foldl init ([],[]) acc)
      end
    | init_edges acc apart ((sub,edge) :: sub_edges) =
      let
(*DEBUG
        val () = if not (Subst.null sub) then ()
                 else raise Bug "Rule.factor.init_edges: empty subst"
*)
        val (acc,apart) =
            case updateApart sub apart of
              SOME apart' => ((apart',sub,edge) :: acc, edge :: apart)
            | NONE => (acc,apart)
      in
        init_edges acc apart sub_edges
      end;

  fun mk_edges apart sub_edges [] = init_edges [] apart sub_edges
    | mk_edges apart sub_edges (lit :: lits) =
      let
        val sub_edges = List.foldl (addFactorEdge lit) sub_edges lits

        val (apart,sub_edges) =
            case total Literal.sym lit of
              NONE => (apart,sub_edges)
            | SOME lit' =>
              let
                val apart = addReflEdge lit apart
                val sub_edges = addIrreflEdge lit sub_edges
                val sub_edges = List.foldl (addFactorEdge lit') sub_edges lits
              in
                (apart,sub_edges)
              end
      in
        mk_edges apart sub_edges lits
      end;

  fun fact acc [] = acc
    | fact acc ((_,sub,[]) :: others) = fact (sub :: acc) others
    | fact acc ((apart, sub, edge :: edges) :: others) =
      let
        val others =
            case joinEdge sub edge of
              Joinable sub' =>
              let
                val others = (edge :: apart, sub, edges) :: others
              in
                case updateApart sub' apart of
                  NONE => others
                | SOME apart' => (apart',sub',edges) :: others
              end
            | _ => (apart,sub,edges) :: others
      in
        fact acc others
      end;
in
  fun factor' cl =
      let
(*TRACE6
        val () = Parser.ppTrace LiteralSet.pp "Rule.factor': cl" cl
*)
        val edges = mk_edges [] [] (LiteralSet.toList cl)
(*TRACE6
        val ppEdgesSize = Parser.ppMap length Parser.ppInt
        val ppEdgel = Parser.ppList ppEdge
        val ppEdges = Parser.ppList (Parser.ppTriple ppEdgel Subst.pp ppEdgel)
        val () = Parser.ppTrace ppEdgesSize "Rule.factor': |edges|" edges
        val () = Parser.ppTrace ppEdges "Rule.factor': edges" edges
*)
        val result = fact [] edges
(*TRACE6
        val ppResult = Parser.ppList Subst.pp
        val () = Parser.ppTrace ppResult "Rule.factor': result" result
*)
      in
        result
      end;
end;

fun factor th =
    let
      fun fact sub = removeSym (Thm.subst sub th)
    in
      map fact (factor' (Thm.clause th))
    end;

end
end;

(**** Original file: Normalize.sig ****)

(* ========================================================================= *)
(* NORMALIZING FORMULAS                                                      *)
(* Copyright (c) 2001-2007 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Normalize =
sig

(* ------------------------------------------------------------------------- *)
(* Negation normal form.                                                     *)
(* ------------------------------------------------------------------------- *)

val nnf : Metis.Formula.formula -> Metis.Formula.formula

(* ------------------------------------------------------------------------- *)
(* Conjunctive normal form.                                                  *)
(* ------------------------------------------------------------------------- *)

val cnf : Metis.Formula.formula -> Metis.Formula.formula list

end

(**** Original file: Normalize.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* NORMALIZING FORMULAS                                                      *)
(* Copyright (c) 2001-2007 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Normalize :> Normalize =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* Counting the clauses that would be generated by conjunctive normal form.  *)
(* ------------------------------------------------------------------------- *)

datatype count = Count of {positive : real, negative : real};

fun positive (Count {positive = p, ...}) = p;

fun negative (Count {negative = n, ...}) = n;

fun countNegate (Count {positive = p, negative = n}) =
    Count {positive = n, negative = p};

fun countEqualish count1 count2 =
    let
      val Count {positive = p1, negative = n1} = count1
      and Count {positive = p2, negative = n2} = count2
    in
      Real.abs (p1 - p2) < 0.5 andalso Real.abs (n1 - n2) < 0.5
    end;

val countTrue = Count {positive = 0.0, negative = 1.0};

val countFalse = Count {positive = 1.0, negative = 0.0};

val countLiteral = Count {positive = 1.0, negative = 1.0};

fun countAnd2 (count1,count2) =
    let
      val Count {positive = p1, negative = n1} = count1
      and Count {positive = p2, negative = n2} = count2
      val p = p1 + p2
      and n = n1 * n2
    in
      Count {positive = p, negative = n}
    end;

fun countOr2 (count1,count2) =
    let
      val Count {positive = p1, negative = n1} = count1
      and Count {positive = p2, negative = n2} = count2
      val p = p1 * p2
      and n = n1 + n2
    in
      Count {positive = p, negative = n}
    end;

(*** Is this associative? ***)
fun countXor2 (count1,count2) =
    let
      val Count {positive = p1, negative = n1} = count1
      and Count {positive = p2, negative = n2} = count2
      val p = p1 * p2 + n1 * n2
      and n = p1 * n2 + n1 * p2
    in
      Count {positive = p, negative = n}
    end;

fun countDefinition body_count = countXor2 (countLiteral,body_count);

(* ------------------------------------------------------------------------- *)
(* A type of normalized formula.                                             *)
(* ------------------------------------------------------------------------- *)

datatype formula =
    True
  | False
  | Literal of NameSet.set * Literal.literal
  | And of NameSet.set * count * formula Set.set
  | Or of NameSet.set * count * formula Set.set
  | Xor of NameSet.set * count * bool * formula Set.set
  | Exists of NameSet.set * count * NameSet.set * formula
  | Forall of NameSet.set * count * NameSet.set * formula;

fun compare f1_f2 =
    case f1_f2 of
      (True,True) => EQUAL
    | (True,_) => LESS
    | (_,True) => GREATER
    | (False,False) => EQUAL
    | (False,_) => LESS
    | (_,False) => GREATER
    | (Literal (_,l1), Literal (_,l2)) => Literal.compare (l1,l2)
    | (Literal _, _) => LESS
    | (_, Literal _) => GREATER
    | (And (_,_,s1), And (_,_,s2)) => Set.compare (s1,s2)
    | (And _, _) => LESS
    | (_, And _) => GREATER
    | (Or (_,_,s1), Or (_,_,s2)) => Set.compare (s1,s2)
    | (Or _, _) => LESS
    | (_, Or _) => GREATER
    | (Xor (_,_,p1,s1), Xor (_,_,p2,s2)) =>
      (case boolCompare (p1,p2) of
         LESS => LESS
       | EQUAL => Set.compare (s1,s2)
       | GREATER => GREATER)
    | (Xor _, _) => LESS
    | (_, Xor _) => GREATER
    | (Exists (_,_,n1,f1), Exists (_,_,n2,f2)) =>
      (case NameSet.compare (n1,n2) of
         LESS => LESS
       | EQUAL => compare (f1,f2)
       | GREATER => GREATER)
    | (Exists _, _) => LESS
    | (_, Exists _) => GREATER
    | (Forall (_,_,n1,f1), Forall (_,_,n2,f2)) =>
      (case NameSet.compare (n1,n2) of
         LESS => LESS
       | EQUAL => compare (f1,f2)
       | GREATER => GREATER);

val empty = Set.empty compare;

val singleton = Set.singleton compare;

local
  fun neg True = False
    | neg False = True
    | neg (Literal (fv,lit)) = Literal (fv, Literal.negate lit)
    | neg (And (fv,c,s)) = Or (fv, countNegate c, neg_set s)
    | neg (Or (fv,c,s)) = And (fv, countNegate c, neg_set s)
    | neg (Xor (fv,c,p,s)) = Xor (fv, c, not p, s)
    | neg (Exists (fv,c,n,f)) = Forall (fv, countNegate c, n, neg f)
    | neg (Forall (fv,c,n,f)) = Exists (fv, countNegate c, n, neg f)

  and neg_set s = Set.foldl neg_elt empty s

  and neg_elt (f,s) = Set.add s (neg f);
in
  val negate = neg;

  val negateSet = neg_set;
end;

fun negateMember x s = Set.member (negate x) s;

local
  fun member s x = negateMember x s;
in
  fun negateDisjoint s1 s2 =
      if Set.size s1 < Set.size s2 then not (Set.exists (member s2) s1)
      else not (Set.exists (member s1) s2);
end;

fun polarity True = true
  | polarity False = false
  | polarity (Literal (_,(pol,_))) = not pol
  | polarity (And _) = true
  | polarity (Or _) = false
  | polarity (Xor (_,_,pol,_)) = pol
  | polarity (Exists _) = true
  | polarity (Forall _) = false;

(*DEBUG
val polarity = fn f =>
    let
      val res1 = compare (f, negate f) = LESS
      val res2 = polarity f
      val _ = res1 = res2 orelse raise Bug "polarity"
    in
      res2
    end;
*)

fun applyPolarity true fm = fm
  | applyPolarity false fm = negate fm;

fun freeVars True = NameSet.empty
  | freeVars False = NameSet.empty
  | freeVars (Literal (fv,_)) = fv
  | freeVars (And (fv,_,_)) = fv
  | freeVars (Or (fv,_,_)) = fv
  | freeVars (Xor (fv,_,_,_)) = fv
  | freeVars (Exists (fv,_,_,_)) = fv
  | freeVars (Forall (fv,_,_,_)) = fv;

fun freeIn v fm = NameSet.member v (freeVars fm);

val freeVarsSet =
    let
      fun free (fm,acc) = NameSet.union (freeVars fm) acc
    in
      Set.foldl free NameSet.empty
    end;

fun count True = countTrue
  | count False = countFalse
  | count (Literal _) = countLiteral
  | count (And (_,c,_)) = c
  | count (Or (_,c,_)) = c
  | count (Xor (_,c,p,_)) = if p then c else countNegate c
  | count (Exists (_,c,_,_)) = c
  | count (Forall (_,c,_,_)) = c;

val countAndSet =
    let
      fun countAnd (fm,c) = countAnd2 (count fm, c)
    in
      Set.foldl countAnd countTrue
    end;

val countOrSet =
    let
      fun countOr (fm,c) = countOr2 (count fm, c)
    in
      Set.foldl countOr countFalse
    end;

val countXorSet =
    let
      fun countXor (fm,c) = countXor2 (count fm, c)
    in
      Set.foldl countXor countFalse
    end;

fun And2 (False,_) = False
  | And2 (_,False) = False
  | And2 (True,f2) = f2
  | And2 (f1,True) = f1
  | And2 (f1,f2) =
    let
      val (fv1,c1,s1) =
          case f1 of
            And fv_c_s => fv_c_s
          | _ => (freeVars f1, count f1, singleton f1)

      and (fv2,c2,s2) =
          case f2 of
            And fv_c_s => fv_c_s
          | _ => (freeVars f2, count f2, singleton f2)
    in
      if not (negateDisjoint s1 s2) then False
      else
        let
          val s = Set.union s1 s2
        in
          case Set.size s of
            0 => True
          | 1 => Set.pick s
          | n =>
            if n = Set.size s1 + Set.size s2 then
              And (NameSet.union fv1 fv2, countAnd2 (c1,c2), s)
            else
              And (freeVarsSet s, countAndSet s, s)
        end
    end;

val AndList = foldl And2 True;

val AndSet = Set.foldl And2 True;

fun Or2 (True,_) = True
  | Or2 (_,True) = True
  | Or2 (False,f2) = f2
  | Or2 (f1,False) = f1
  | Or2 (f1,f2) =
    let
      val (fv1,c1,s1) =
          case f1 of
            Or fv_c_s => fv_c_s
          | _ => (freeVars f1, count f1, singleton f1)

      and (fv2,c2,s2) =
          case f2 of
            Or fv_c_s => fv_c_s
          | _ => (freeVars f2, count f2, singleton f2)
    in
      if not (negateDisjoint s1 s2) then True
      else
        let
          val s = Set.union s1 s2
        in
          case Set.size s of
            0 => False
          | 1 => Set.pick s
          | n =>
            if n = Set.size s1 + Set.size s2 then
              Or (NameSet.union fv1 fv2, countOr2 (c1,c2), s)
            else
              Or (freeVarsSet s, countOrSet s, s)
        end
    end;

val OrList = foldl Or2 False;

val OrSet = Set.foldl Or2 False;

fun pushOr2 (f1,f2) =
    let
      val s1 = case f1 of And (_,_,s) => s | _ => singleton f1
      and s2 = case f2 of And (_,_,s) => s | _ => singleton f2

      fun g x1 (x2,acc) = And2 (Or2 (x1,x2), acc)
      fun f (x1,acc) = Set.foldl (g x1) acc s2
    in
      Set.foldl f True s1
    end;

val pushOrList = foldl pushOr2 False;

local
  fun normalize fm =
      let
        val p = polarity fm
        val fm = applyPolarity p fm
      in
        (freeVars fm, count fm, p, singleton fm)
      end;
in
  fun Xor2 (False,f2) = f2
    | Xor2 (f1,False) = f1
    | Xor2 (True,f2) = negate f2
    | Xor2 (f1,True) = negate f1
    | Xor2 (f1,f2) =
      let
        val (fv1,c1,p1,s1) = case f1 of Xor x => x | _ => normalize f1
        and (fv2,c2,p2,s2) = case f2 of Xor x => x | _ => normalize f2

        val s = Set.symmetricDifference s1 s2

        val fm =
            case Set.size s of
              0 => False
            | 1 => Set.pick s
            | n =>
              if n = Set.size s1 + Set.size s2 then
                Xor (NameSet.union fv1 fv2, countXor2 (c1,c2), true, s)
              else
                Xor (freeVarsSet s, countXorSet s, true, s)

        val p = p1 = p2
      in
        applyPolarity p fm
      end;
end;

val XorList = foldl Xor2 False;

val XorSet = Set.foldl Xor2 False;

fun XorPolarityList (p,l) = applyPolarity p (XorList l);

fun XorPolaritySet (p,s) = applyPolarity p (XorSet s);

fun destXor (Xor (_,_,p,s)) =
    let
      val (fm1,s) = Set.deletePick s
      val fm2 =
          if Set.size s = 1 then applyPolarity p (Set.pick s)
          else Xor (freeVarsSet s, countXorSet s, p, s)
    in
      (fm1,fm2)
    end
  | destXor _ = raise Error "destXor";

fun pushXor fm =
    let
      val (f1,f2) = destXor fm
      val f1' = negate f1
      and f2' = negate f2
    in
      And2 (Or2 (f1,f2), Or2 (f1',f2'))
    end;

fun Exists1 (v,init_fm) =
    let
      fun exists_gen fm =
          let
            val fv = NameSet.delete (freeVars fm) v
            val c = count fm
            val n = NameSet.singleton v
          in
            Exists (fv,c,n,fm)
          end

      fun exists fm = if freeIn v fm then exists_free fm else fm

      and exists_free (Or (_,_,s)) = OrList (Set.transform exists s)
        | exists_free (fm as And (_,_,s)) =
          let
            val sv = Set.filter (freeIn v) s
          in
            if Set.size sv <> 1 then exists_gen fm
            else
              let
                val fm = Set.pick sv
                val s = Set.delete s fm
              in
                And2 (exists_free fm, AndSet s)
              end
          end
        | exists_free (Exists (fv,c,n,f)) =
          Exists (NameSet.delete fv v, c, NameSet.add n v, f)
        | exists_free fm = exists_gen fm
    in
      exists init_fm
    end;

fun ExistsList (vs,f) = foldl Exists1 f vs;

fun ExistsSet (n,f) = NameSet.foldl Exists1 f n;

fun Forall1 (v,init_fm) =
    let
      fun forall_gen fm =
          let
            val fv = NameSet.delete (freeVars fm) v
            val c = count fm
            val n = NameSet.singleton v
          in
            Forall (fv,c,n,fm)
          end

      fun forall fm = if freeIn v fm then forall_free fm else fm

      and forall_free (And (_,_,s)) = AndList (Set.transform forall s)
        | forall_free (fm as Or (_,_,s)) =
          let
            val sv = Set.filter (freeIn v) s
          in
            if Set.size sv <> 1 then forall_gen fm
            else
              let
                val fm = Set.pick sv
                val s = Set.delete s fm
              in
                Or2 (forall_free fm, OrSet s)
              end
          end
        | forall_free (Forall (fv,c,n,f)) =
          Forall (NameSet.delete fv v, c, NameSet.add n v, f)
        | forall_free fm = forall_gen fm
    in
      forall init_fm
    end;

fun ForallList (vs,f) = foldl Forall1 f vs;

fun ForallSet (n,f) = NameSet.foldl Forall1 f n;

local
  fun subst_fv fvSub =
      let
        fun add_fv (v,s) = NameSet.union (NameMap.get fvSub v) s
      in
        NameSet.foldl add_fv NameSet.empty
      end;

  fun subst_rename (v,(avoid,bv,sub,domain,fvSub)) =
      let
        val v' = Term.variantPrime avoid v
        val avoid = NameSet.add avoid v'
        val bv = NameSet.add bv v'
        val sub = Subst.insert sub (v, Term.Var v')
        val domain = NameSet.add domain v
        val fvSub = NameMap.insert fvSub (v, NameSet.singleton v')
      in
        (avoid,bv,sub,domain,fvSub)
      end;

  fun subst_check sub domain fvSub fm =
      let
        val domain = NameSet.intersect domain (freeVars fm)
      in
        if NameSet.null domain then fm
        else subst_domain sub domain fvSub fm
      end

  and subst_domain sub domain fvSub fm =
      case fm of
        Literal (fv,lit) =>
        let
          val fv = NameSet.difference fv domain
          val fv = NameSet.union fv (subst_fv fvSub domain)
          val lit = Literal.subst sub lit
        in
          Literal (fv,lit)
        end
      | And (_,_,s) =>
        AndList (Set.transform (subst_check sub domain fvSub) s)
      | Or (_,_,s) =>
        OrList (Set.transform (subst_check sub domain fvSub) s)
      | Xor (_,_,p,s) =>
        XorPolarityList (p, Set.transform (subst_check sub domain fvSub) s)
      | Exists fv_c_n_f => subst_quant Exists sub domain fvSub fv_c_n_f
      | Forall fv_c_n_f => subst_quant Forall sub domain fvSub fv_c_n_f
      | _ => raise Bug "subst_domain"

  and subst_quant quant sub domain fvSub (fv,c,bv,fm) =
      let
        val sub_fv = subst_fv fvSub domain
        val fv = NameSet.union sub_fv (NameSet.difference fv domain)
        val captured = NameSet.intersect bv sub_fv
        val bv = NameSet.difference bv captured
        val avoid = NameSet.union fv bv
        val (_,bv,sub,domain,fvSub) =
            NameSet.foldl subst_rename (avoid,bv,sub,domain,fvSub) captured
        val fm = subst_domain sub domain fvSub fm
      in
        quant (fv,c,bv,fm)
      end;
in
  fun subst sub =
      let
        fun mk_dom (v,tm,(d,fv)) =
            (NameSet.add d v, NameMap.insert fv (v, Term.freeVars tm))

        val domain_fvSub = (NameSet.empty, NameMap.new ())
        val (domain,fvSub) = Subst.foldl mk_dom domain_fvSub sub
      in
        subst_check sub domain fvSub
      end;
end;

fun fromFormula fm =
    case fm of
      Formula.True => True
    | Formula.False => False
    | Formula.Atom atm => Literal (Atom.freeVars atm, (true,atm))
    | Formula.Not p => negateFromFormula p
    | Formula.And (p,q) => And2 (fromFormula p, fromFormula q)
    | Formula.Or (p,q) => Or2 (fromFormula p, fromFormula q)
    | Formula.Imp (p,q) => Or2 (negateFromFormula p, fromFormula q)
    | Formula.Iff (p,q) => Xor2 (negateFromFormula p, fromFormula q)
    | Formula.Forall (v,p) => Forall1 (v, fromFormula p)
    | Formula.Exists (v,p) => Exists1 (v, fromFormula p)

and negateFromFormula fm =
    case fm of
      Formula.True => False
    | Formula.False => True
    | Formula.Atom atm => Literal (Atom.freeVars atm, (false,atm))
    | Formula.Not p => fromFormula p
    | Formula.And (p,q) => Or2 (negateFromFormula p, negateFromFormula q)
    | Formula.Or (p,q) => And2 (negateFromFormula p, negateFromFormula q)
    | Formula.Imp (p,q) => And2 (fromFormula p, negateFromFormula q)
    | Formula.Iff (p,q) => Xor2 (fromFormula p, fromFormula q)
    | Formula.Forall (v,p) => Exists1 (v, negateFromFormula p)
    | Formula.Exists (v,p) => Forall1 (v, negateFromFormula p);

local
  fun lastElt (s : formula Set.set) =
      case Set.findr (K true) s of
        NONE => raise Bug "lastElt: empty set"
      | SOME fm => fm;

  fun negateLastElt s =
      let
        val fm = lastElt s
      in
        Set.add (Set.delete s fm) (negate fm)
      end;

  fun form fm =
      case fm of
        True => Formula.True
      | False => Formula.False
      | Literal (_,lit) => Literal.toFormula lit
      | And (_,_,s) => Formula.listMkConj (Set.transform form s)
      | Or (_,_,s) => Formula.listMkDisj (Set.transform form s)
      | Xor (_,_,p,s) =>
        let
          val s = if p then negateLastElt s else s
        in
          Formula.listMkEquiv (Set.transform form s)
        end
      | Exists (_,_,n,f) => Formula.listMkExists (NameSet.toList n, form f)
      | Forall (_,_,n,f) => Formula.listMkForall (NameSet.toList n, form f);
in
  val toFormula = form;
end;

val pp = Parser.ppMap toFormula Formula.pp;

val toString = Parser.toString pp;

(* ------------------------------------------------------------------------- *)
(* Negation normal form.                                                     *)
(* ------------------------------------------------------------------------- *)

fun nnf fm = toFormula (fromFormula fm);

(* ------------------------------------------------------------------------- *)
(* Simplifying with definitions.                                             *)
(* ------------------------------------------------------------------------- *)

datatype simplify =
    Simplify of
      {formula : (formula,formula) Map.map,
       andSet : (formula Set.set * formula) list,
       orSet : (formula Set.set * formula) list,
       xorSet : (formula Set.set * formula) list};

val simplifyEmpty =
    Simplify {formula = Map.new compare, andSet = [], orSet = [], xorSet = []};

local
  fun simpler fm s =
      Set.size s <> 1 orelse
      case Set.pick s of
        True => false
      | False => false
      | Literal _ => false
      | _ => true;

  fun addSet set_defs body_def =
      let
        fun def_body_size (body,_) = Set.size body

        val body_size = def_body_size body_def

        val (body,_) = body_def

        fun add acc [] = List.revAppend (acc,[body_def])
          | add acc (l as (bd as (b,_)) :: bds) =
            case Int.compare (def_body_size bd, body_size) of
              LESS => List.revAppend (acc, body_def :: l)
            | EQUAL => if Set.equal b body then List.revAppend (acc,l)
                       else add (bd :: acc) bds
            | GREATER => add (bd :: acc) bds
      in
        add [] set_defs
      end;

  fun add simp (body,False) = add simp (negate body, True)
    | add simp (True,_) = simp
    | add (Simplify {formula,andSet,orSet,xorSet}) (And (_,_,s), def) =
      let
        val andSet = addSet andSet (s,def)
        and orSet = addSet orSet (negateSet s, negate def)
      in
        Simplify
          {formula = formula,
           andSet = andSet, orSet = orSet, xorSet = xorSet}
      end
    | add (Simplify {formula,andSet,orSet,xorSet}) (Or (_,_,s), def) =
      let
        val orSet = addSet orSet (s,def)
        and andSet = addSet andSet (negateSet s, negate def)
      in
        Simplify
          {formula = formula,
           andSet = andSet, orSet = orSet, xorSet = xorSet}
      end
    | add simp (Xor (_,_,p,s), def) =
      let
        val simp = addXorSet simp (s, applyPolarity p def)
      in
        case def of
          True =>
          let
            fun addXorLiteral (fm as Literal _, simp) =
                let
                  val s = Set.delete s fm
                in
                  if not (simpler fm s) then simp
                  else addXorSet simp (s, applyPolarity (not p) fm)
                end
              | addXorLiteral (_,simp) = simp
          in
            Set.foldl addXorLiteral simp s
          end
        | _ => simp
      end
    | add (simp as Simplify {formula,andSet,orSet,xorSet}) (body,def) =
      if Map.inDomain body formula then simp
      else
        let
          val formula = Map.insert formula (body,def)
          val formula = Map.insert formula (negate body, negate def)
        in
          Simplify
            {formula = formula,
             andSet = andSet, orSet = orSet, xorSet = xorSet}
        end

  and addXorSet (simp as Simplify {formula,andSet,orSet,xorSet}) (s,def) =
      if Set.size s = 1 then add simp (Set.pick s, def)
      else
        let
          val xorSet = addSet xorSet (s,def)
        in
          Simplify
            {formula = formula,
             andSet = andSet, orSet = orSet, xorSet = xorSet}
        end;
in
  fun simplifyAdd simp fm = add simp (fm,True);
end;

local
  fun simplifySet set_defs set =
      let
        fun pred (s,_) = Set.subset s set
      in
        case List.find pred set_defs of
          NONE => NONE
        | SOME (s,f) => SOME (Set.add (Set.difference set s) f)
      end;
in
  fun simplify (Simplify {formula,andSet,orSet,xorSet}) =
      let
        fun simp fm = simp_top (simp_sub fm)

        and simp_top (changed_fm as (_, And (_,_,s))) =
            (case simplifySet andSet s of
               NONE => changed_fm
             | SOME s => simp_top (true, AndSet s))
          | simp_top (changed_fm as (_, Or (_,_,s))) =
            (case simplifySet orSet s of
               NONE => changed_fm
             | SOME s => simp_top (true, OrSet s))
          | simp_top (changed_fm as (_, Xor (_,_,p,s))) =
            (case simplifySet xorSet s of
               NONE => changed_fm
             | SOME s => simp_top (true, XorPolaritySet (p,s)))
          | simp_top (changed_fm as (_,fm)) =
            (case Map.peek formula fm of
               NONE => changed_fm
             | SOME fm => simp_top (true,fm))

        and simp_sub fm =
            case fm of
              And (_,_,s) =>
              let
                val l = Set.transform simp s
                val changed = List.exists fst l
                val fm = if changed then AndList (map snd l) else fm
              in
                (changed,fm)
              end
            | Or (_,_,s) =>
              let
                val l = Set.transform simp s
                val changed = List.exists fst l
                val fm = if changed then OrList (map snd l) else fm
              in
                (changed,fm)
              end
            | Xor (_,_,p,s) =>
              let
                val l = Set.transform simp s
                val changed = List.exists fst l
                val fm = if changed then XorPolarityList (p, map snd l) else fm
              in
                (changed,fm)
              end
            | Exists (_,_,n,f) =>
              let
                val (changed,f) = simp f
                val fm = if changed then ExistsSet (n,f) else fm
              in
                (changed,fm)
              end
            | Forall (_,_,n,f) =>
              let
                val (changed,f) = simp f
                val fm = if changed then ForallSet (n,f) else fm
              in
                (changed,fm)
              end
            | _ => (false,fm);
      in
        fn fm => snd (simp fm)
      end;
end;

(*TRACE2
val simplify = fn simp => fn fm =>
    let
      val fm' = simplify simp fm
      val () = if compare (fm,fm') = EQUAL then ()
               else (Parser.ppTrace pp "Normalize.simplify: fm" fm;
                     Parser.ppTrace pp "Normalize.simplify: fm'" fm')
    in
      fm'
    end;
*)

(* ------------------------------------------------------------------------- *)
(* Basic conjunctive normal form.                                            *)
(* ------------------------------------------------------------------------- *)

val newSkolemFunction =
    let
      val counter : int NameMap.map Unsynchronized.ref = Unsynchronized.ref (NameMap.new ())
    in
      fn n => CRITICAL (fn () =>
      let
        val Unsynchronized.ref m = counter
        val i = Option.getOpt (NameMap.peek m n, 0)
        val () = counter := NameMap.insert m (n, i + 1)
      in
        "skolem_" ^ n ^ (if i = 0 then "" else "_" ^ Int.toString i)
      end)
    end;

fun skolemize fv bv fm =
    let
      val fv = NameSet.transform Term.Var fv
               
      fun mk (v,s) = Subst.insert s (v, Term.Fn (newSkolemFunction v, fv))
    in
      subst (NameSet.foldl mk Subst.empty bv) fm
    end;

local
  fun rename avoid fv bv fm =
      let
        val captured = NameSet.intersect avoid bv
      in
        if NameSet.null captured then fm
        else
          let
            fun ren (v,(a,s)) =
                let
                  val v' = Term.variantPrime a v
                in
                  (NameSet.add a v', Subst.insert s (v, Term.Var v'))
                end
              
            val avoid = NameSet.union (NameSet.union avoid fv) bv

            val (_,sub) = NameSet.foldl ren (avoid,Subst.empty) captured
          in
            subst sub fm
          end
      end;

  fun cnf avoid fm =
(*TRACE5
      let
        val fm' = cnf' avoid fm
        val () = Parser.ppTrace pp "Normalize.cnf: fm" fm
        val () = Parser.ppTrace pp "Normalize.cnf: fm'" fm'
      in
        fm'
      end
  and cnf' avoid fm =
*)
      case fm of
        True => True
      | False => False
      | Literal _ => fm
      | And (_,_,s) => AndList (Set.transform (cnf avoid) s)
      | Or (_,_,s) => pushOrList (snd (Set.foldl cnfOr (avoid,[]) s))
      | Xor _ => cnf avoid (pushXor fm)
      | Exists (fv,_,n,f) => cnf avoid (skolemize fv n f)
      | Forall (fv,_,n,f) => cnf avoid (rename avoid fv n f)

  and cnfOr (fm,(avoid,acc)) =
      let
        val fm = cnf avoid fm
      in
        (NameSet.union (freeVars fm) avoid, fm :: acc)
      end;
in
  val basicCnf = cnf NameSet.empty;
end;

(* ------------------------------------------------------------------------- *)
(* Finding the formula definition that minimizes the number of clauses.      *)
(* ------------------------------------------------------------------------- *)

local
  type best = real * formula option;

  fun minBreak countClauses fm best =
      case fm of
        True => best
      | False => best
      | Literal _ => best
      | And (_,_,s) =>
        minBreakSet countClauses countAnd2 countTrue AndSet s best
      | Or (_,_,s) =>
        minBreakSet countClauses countOr2 countFalse OrSet s best
      | Xor (_,_,_,s) =>
        minBreakSet countClauses countXor2 countFalse XorSet s best
      | Exists (_,_,_,f) => minBreak countClauses f best
      | Forall (_,_,_,f) => minBreak countClauses f best
                            
  and minBreakSet countClauses count2 count0 mkSet fmSet best =
      let
        fun cumulatives fms =
            let
              fun fwd (fm,(c1,s1,l)) =
                  let
                    val c1' = count2 (count fm, c1)
                    and s1' = Set.add s1 fm
                  in
                    (c1', s1', (c1,s1,fm) :: l)
                  end

              fun bwd ((c1,s1,fm),(c2,s2,l)) =
                  let
                    val c2' = count2 (count fm, c2)
                    and s2' = Set.add s2 fm
                  in
                    (c2', s2', (c1,s1,fm,c2,s2) :: l)
                  end

              val (c1,_,fms) = foldl fwd (count0,empty,[]) fms
              val (c2,_,fms) = foldl bwd (count0,empty,[]) fms

              val _ = countEqualish c1 c2 orelse raise Bug "cumulativeCounts"
            in
              fms
            end

        fun breakSing ((c1,_,fm,c2,_),best) =
            let
              val cFms = count2 (c1,c2)
              fun countCls cFm = countClauses (count2 (cFms,cFm))
            in
              minBreak countCls fm best
            end

        val breakSet1 =
            let
              fun break c1 s1 fm c2 (best as (bcl,_)) =
                  if Set.null s1 then best
                  else
                    let
                      val cDef = countDefinition (count2 (c1, count fm))
                      val cFm = count2 (countLiteral,c2)
                      val cl = positive cDef + countClauses cFm
                      val better = cl < bcl - 0.5
                    in
                      if better then (cl, SOME (mkSet (Set.add s1 fm)))
                      else best
                    end
            in
              fn ((c1,s1,fm,c2,s2),best) =>
                 break c1 s1 fm c2 (break c2 s2 fm c1 best)
            end

        val fms = Set.toList fmSet

        fun breakSet measure best =
            let
              val fms = sortMap (measure o count) Real.compare fms
            in
              foldl breakSet1 best (cumulatives fms)
            end

        val best = foldl breakSing best (cumulatives fms)
        val best = breakSet positive best
        val best = breakSet negative best
        val best = breakSet countClauses best
      in
        best
      end
in
  fun minimumDefinition fm =
      let
        val countClauses = positive
        val cl = countClauses (count fm)
      in
        if cl < 1.5 then NONE
        else
          let
            val (cl',def) = minBreak countClauses fm (cl,NONE)
(*TRACE1
            val () =
                case def of
                  NONE => ()
                | SOME d =>
                  Parser.ppTrace pp ("defCNF: before = " ^ Real.toString cl ^
                                     ", after = " ^ Real.toString cl' ^
                                     ", definition") d
*)
          in
            def
          end
      end;
end;

(* ------------------------------------------------------------------------- *)
(* Conjunctive normal form.                                                  *)
(* ------------------------------------------------------------------------- *)

val newDefinitionRelation =
    let
      val counter : int Unsynchronized.ref = Unsynchronized.ref 0
    in
      fn () => CRITICAL (fn () =>
      let
        val Unsynchronized.ref i = counter
        val () = counter := i + 1
      in
        "defCNF_" ^ Int.toString i
      end)
    end;

fun newDefinition def =
    let
      val fv = freeVars def
      val atm = (newDefinitionRelation (), NameSet.transform Term.Var fv)
      val lit = Literal (fv,(true,atm))
    in
      Xor2 (lit,def)
    end;

local
  fun def_cnf acc [] = acc
    | def_cnf acc ((prob,simp,fms) :: probs) =
      def_cnf_problem acc prob simp fms probs

  and def_cnf_problem acc prob _ [] probs = def_cnf (prob :: acc) probs
    | def_cnf_problem acc prob simp (fm :: fms) probs =
      def_cnf_formula acc prob simp (simplify simp fm) fms probs

  and def_cnf_formula acc prob simp fm fms probs =
      case fm of
        True => def_cnf_problem acc prob simp fms probs
      | False => def_cnf acc probs
      | And (_,_,s) => def_cnf_problem acc prob simp (Set.toList s @ fms) probs
      | Exists (fv,_,n,f) =>
        def_cnf_formula acc prob simp (skolemize fv n f) fms probs
      | Forall (_,_,_,f) => def_cnf_formula acc prob simp f fms probs
      | _ =>
        case minimumDefinition fm of
          NONE =>
          let
            val prob = fm :: prob
            and simp = simplifyAdd simp fm
          in
            def_cnf_problem acc prob simp fms probs
          end
        | SOME def =>
          let
            val def_fm = newDefinition def
            and fms = fm :: fms
          in
            def_cnf_formula acc prob simp def_fm fms probs
          end;

  fun cnf_prob prob = toFormula (AndList (map basicCnf prob));
in
  fun cnf fm =
      let
        val fm = fromFormula fm
(*TRACE2
        val () = Parser.ppTrace pp "Normalize.cnf: fm" fm
*)
        val probs = def_cnf [] [([],simplifyEmpty,[fm])]
      in
        map cnf_prob probs
      end;
end;

end
end;

(**** Original file: Model.sig ****)

(* ========================================================================= *)
(* RANDOM FINITE MODELS                                                      *)
(* Copyright (c) 2003-2007 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Model =
sig

(* ------------------------------------------------------------------------- *)
(* The parts of the model that are fixed.                                    *)
(* Note: a model of size N has integer elements 0...N-1.                     *)
(* ------------------------------------------------------------------------- *)

type fixed =
     {size : int} ->
     {functions : (Metis.Term.functionName * int list) -> int option,
      relations : (Metis.Atom.relationName * int list) -> bool option}

val fixedMerge : fixed -> fixed -> fixed  (* Prefers the second fixed *)

val fixedMergeList : fixed list -> fixed

val fixedPure : fixed  (* : = *)

val fixedBasic : fixed  (* id fst snd #1 #2 #3 <> *)

val fixedModulo : fixed  (* <numerals> suc pre ~ + - * exp div mod *)
                         (* is_0 divides even odd *)

val fixedOverflowNum : fixed  (* <numerals> suc pre + - * exp div mod *)
                              (* is_0 <= < >= > divides even odd *)

val fixedOverflowInt : fixed  (* <numerals> suc pre + - * exp div mod *)
                              (* is_0 <= < >= > divides even odd *)

val fixedSet : fixed  (* empty univ union intersect compl card in subset *)

(* ------------------------------------------------------------------------- *)
(* A type of random finite models.                                           *)
(* ------------------------------------------------------------------------- *)

type parameters = {size : int, fixed : fixed}

type model

val new : parameters -> model

val size : model -> int

(* ------------------------------------------------------------------------- *)
(* Valuations.                                                               *)
(* ------------------------------------------------------------------------- *)

type valuation = int Metis.NameMap.map

val valuationEmpty : valuation

val valuationRandom : {size : int} -> Metis.NameSet.set -> valuation

val valuationFold :
    {size : int} -> Metis.NameSet.set -> (valuation * 'a -> 'a) -> 'a -> 'a

(* ------------------------------------------------------------------------- *)
(* Interpreting terms and formulas in the model.                             *)
(* ------------------------------------------------------------------------- *)

val interpretTerm : model -> valuation -> Metis.Term.term -> int

val interpretAtom : model -> valuation -> Metis.Atom.atom -> bool

val interpretFormula : model -> valuation -> Metis.Formula.formula -> bool

val interpretLiteral : model -> valuation -> Metis.Literal.literal -> bool

val interpretClause : model -> valuation -> Metis.Thm.clause -> bool

(* ------------------------------------------------------------------------- *)
(* Check whether random groundings of a formula are true in the model.       *)
(* Note: if it's cheaper, a systematic check will be performed instead.      *)
(* ------------------------------------------------------------------------- *)

val checkAtom :
    {maxChecks : int} -> model -> Metis.Atom.atom -> {T : int, F : int}

val checkFormula :
    {maxChecks : int} -> model -> Metis.Formula.formula -> {T : int, F : int}

val checkLiteral :
    {maxChecks : int} -> model -> Metis.Literal.literal -> {T : int, F : int}

val checkClause :
    {maxChecks : int} -> model -> Metis.Thm.clause -> {T : int, F : int}

end

(**** Original file: Model.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* RANDOM FINITE MODELS                                                      *)
(* Copyright (c) 2003-2007 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Model :> Model =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun intExp x y = exp op* x y 1;

fun natFromString "" = NONE
  | natFromString "0" = SOME 0
  | natFromString s =
    case charToInt (String.sub (s,0)) of
      NONE => NONE
    | SOME 0 => NONE
    | SOME d =>
      let
        fun parse 0 _ acc = SOME acc
          | parse n i acc =
            case charToInt (String.sub (s,i)) of
              NONE => NONE
            | SOME d => parse (n - 1) (i + 1) (10 * acc + d)
      in
        parse (size s - 1) 1 d
      end;

fun projection (_,[]) = NONE
  | projection ("#1", x :: _) = SOME x
  | projection ("#2", _ :: x :: _) = SOME x
  | projection ("#3", _ :: _ :: x :: _) = SOME x
  | projection (func,args) =
    let
      val f = size func
      and n = length args

      val p =
          if f < 2 orelse n <= 3 orelse String.sub (func,0) <> #"#" then NONE
          else if f = 2 then
            (case charToInt (String.sub (func,1)) of
               NONE => NONE
             | p as SOME d => if d <= 3 then NONE else p)
          else if (n < intExp 10 (f - 2) handle Overflow => true) then NONE
          else
            (natFromString (String.extract (func,1,NONE))
             handle Overflow => NONE)
    in
      case p of
        NONE => NONE
      | SOME k => if k > n then NONE else SOME (List.nth (args, k - 1))
    end;

(* ------------------------------------------------------------------------- *)
(* The parts of the model that are fixed.                                    *)
(* Note: a model of size N has integer elements 0...N-1.                     *)
(* ------------------------------------------------------------------------- *)

type fixedModel =
     {functions : (Term.functionName * int list) -> int option,
      relations : (Atom.relationName * int list) -> bool option};

type fixed = {size : int} -> fixedModel

fun fixedMerge fixed1 fixed2 parm =
    let
      val {functions = f1, relations = r1} = fixed1 parm
      and {functions = f2, relations = r2} = fixed2 parm

      fun functions x = case f2 x of NONE => f1 x | s => s

      fun relations x = case r2 x of NONE => r1 x | s => s
    in
      {functions = functions, relations = relations}
    end;

fun fixedMergeList [] = raise Bug "fixedMergeList: empty"
  | fixedMergeList (f :: l) = foldl (uncurry fixedMerge) f l;

fun fixedPure {size = _} =
    let
      fun functions (":",[x,_]) = SOME x
        | functions _ = NONE

      fun relations (rel,[x,y]) =
          if (rel,2) = Atom.eqRelation then SOME (x = y) else NONE
        | relations _ = NONE
    in
      {functions = functions, relations = relations}
    end;

fun fixedBasic {size = _} =
    let
      fun functions ("id",[x]) = SOME x
        | functions ("fst",[x,_]) = SOME x
        | functions ("snd",[_,x]) = SOME x
        | functions func_args = projection func_args

      fun relations ("<>",[x,y]) = SOME (x <> y)
        | relations _ = NONE
    in
      {functions = functions, relations = relations}
    end;

fun fixedModulo {size = N} =
    let
      fun mod_N k = k mod N

      val one = mod_N 1
                
      fun mult (x,y) = mod_N (x * y)

      fun divides_N 0 = false
        | divides_N x = N mod x = 0

      val even_N = divides_N 2

      fun functions (numeral,[]) =
          Option.map mod_N (natFromString numeral handle Overflow => NONE)
        | functions ("suc",[x]) = SOME (if x = N - 1 then 0 else x + 1)
        | functions ("pre",[x]) = SOME (if x = 0 then N - 1 else x - 1)
        | functions ("~",[x]) = SOME (if x = 0 then 0 else N - x)
        | functions ("+",[x,y]) = SOME (mod_N (x + y))
        | functions ("-",[x,y]) = SOME (if x < y then N + x - y else x - y)
        | functions ("*",[x,y]) = SOME (mult (x,y))
        | functions ("exp",[x,y]) = SOME (exp mult x y one)
        | functions ("div",[x,y]) = if divides_N y then SOME (x div y) else NONE
        | functions ("mod",[x,y]) = if divides_N y then SOME (x mod y) else NONE
        | functions _ = NONE

      fun relations ("is_0",[x]) = SOME (x = 0)
        | relations ("divides",[x,y]) =
          if x = 0 then SOME (y = 0)
          else if divides_N x then SOME (y mod x = 0) else NONE
        | relations ("even",[x]) = if even_N then SOME (x mod 2 = 0) else NONE
        | relations ("odd",[x]) = if even_N then SOME (x mod 2 = 1) else NONE
        | relations _ = NONE
    in
      {functions = functions, relations = relations}
    end;

local
  datatype onum = ONeg | ONum of int | OInf;

  val zero = ONum 0
  and one = ONum 1
  and two = ONum 2;

  fun suc (ONum x) = ONum (x + 1)
    | suc v = v;

  fun pre (ONum 0) = ONeg
    | pre (ONum x) = ONum (x - 1)
    | pre v = v;

  fun neg ONeg = NONE
    | neg (n as ONum 0) = SOME n
    | neg _ = SOME ONeg;

  fun add ONeg ONeg = SOME ONeg
    | add ONeg (ONum y) = if y = 0 then SOME ONeg else NONE
    | add ONeg OInf = NONE
    | add (ONum x) ONeg = if x = 0 then SOME ONeg else NONE
    | add (ONum x) (ONum y) = SOME (ONum (x + y))
    | add (ONum _) OInf = SOME OInf
    | add OInf ONeg = NONE
    | add OInf (ONum _) = SOME OInf
    | add OInf OInf = SOME OInf;

  fun sub ONeg ONeg = NONE
    | sub ONeg (ONum _) = SOME ONeg
    | sub ONeg OInf = SOME ONeg
    | sub (ONum _) ONeg = NONE
    | sub (ONum x) (ONum y) = SOME (if x < y then ONeg else ONum (x - y))
    | sub (ONum _) OInf = SOME ONeg
    | sub OInf ONeg = SOME OInf
    | sub OInf (ONum y) = if y = 0 then SOME OInf else NONE
    | sub OInf OInf = NONE;

  fun mult ONeg ONeg = NONE
    | mult ONeg (ONum y) = SOME (if y = 0 then zero else ONeg)
    | mult ONeg OInf = SOME ONeg
    | mult (ONum x) ONeg = SOME (if x = 0 then zero else ONeg)
    | mult (ONum x) (ONum y) = SOME (ONum (x * y))
    | mult (ONum x) OInf = SOME (if x = 0 then zero else OInf)
    | mult OInf ONeg = SOME ONeg
    | mult OInf (ONum y) = SOME (if y = 0 then zero else OInf)
    | mult OInf OInf = SOME OInf;

  fun exp ONeg ONeg = NONE
    | exp ONeg (ONum y) =
      if y = 0 then SOME one else if y mod 2 = 0 then NONE else SOME ONeg
    | exp ONeg OInf = NONE
    | exp (ONum x) ONeg = NONE
    | exp (ONum x) (ONum y) = SOME (ONum (intExp x y) handle Overflow => OInf)
    | exp (ONum x) OInf =
      SOME (if x = 0 then zero else if x = 1 then one else OInf)
    | exp OInf ONeg = NONE
    | exp OInf (ONum y) = SOME (if y = 0 then one else OInf)
    | exp OInf OInf = SOME OInf;

  fun odiv ONeg ONeg = NONE
    | odiv ONeg (ONum y) = if y = 1 then SOME ONeg else NONE
    | odiv ONeg OInf = NONE
    | odiv (ONum _) ONeg = NONE
    | odiv (ONum x) (ONum y) = if y = 0 then NONE else SOME (ONum (x div y))
    | odiv (ONum _) OInf = SOME zero
    | odiv OInf ONeg = NONE
    | odiv OInf (ONum y) = if y = 1 then SOME OInf else NONE
    | odiv OInf OInf = NONE;

  fun omod ONeg ONeg = NONE
    | omod ONeg (ONum y) = if y = 1 then SOME zero else NONE
    | omod ONeg OInf = NONE
    | omod (ONum _) ONeg = NONE
    | omod (ONum x) (ONum y) = if y = 0 then NONE else SOME (ONum (x mod y))
    | omod (x as ONum _) OInf = SOME x
    | omod OInf ONeg = NONE
    | omod OInf (ONum y) = if y = 1 then SOME OInf else NONE
    | omod OInf OInf = NONE;

  fun le ONeg ONeg = NONE
    | le ONeg (ONum y) = SOME true
    | le ONeg OInf = SOME true
    | le (ONum _) ONeg = SOME false
    | le (ONum x) (ONum y) = SOME (x <= y)
    | le (ONum _) OInf = SOME true
    | le OInf ONeg = SOME false
    | le OInf (ONum _) = SOME false
    | le OInf OInf = NONE;

  fun lt x y = Option.map not (le y x);
  
  fun ge x y = le y x;
  
  fun gt x y = lt y x;
  
  fun divides ONeg ONeg = NONE
    | divides ONeg (ONum y) = if y = 0 then SOME true else NONE
    | divides ONeg OInf = NONE
    | divides (ONum x) ONeg =
      if x = 0 then SOME false else if x = 1 then SOME true else NONE
    | divides (ONum x) (ONum y) = SOME (Useful.divides x y)
    | divides (ONum x) OInf =
      if x = 0 then SOME false else if x = 1 then SOME true else NONE
    | divides OInf ONeg = NONE
    | divides OInf (ONum y) = SOME (y = 0)
    | divides OInf OInf = NONE;
  
  fun even n = divides two n;
  
  fun odd n = Option.map not (even n);

  fun fixedOverflow mk_onum dest_onum =
      let
        fun partial_dest_onum NONE = NONE
          | partial_dest_onum (SOME n) = dest_onum n

        fun functions (numeral,[]) =
            (case (natFromString numeral handle Overflow => NONE) of
               NONE => NONE
             | SOME n => dest_onum (ONum n))
          | functions ("suc",[x]) = dest_onum (suc (mk_onum x))
          | functions ("pre",[x]) = dest_onum (pre (mk_onum x))
          | functions ("~",[x]) = partial_dest_onum (neg (mk_onum x))
          | functions ("+",[x,y]) =
            partial_dest_onum (add (mk_onum x) (mk_onum y))
          | functions ("-",[x,y]) =
            partial_dest_onum (sub (mk_onum x) (mk_onum y))
          | functions ("*",[x,y]) =
            partial_dest_onum (mult (mk_onum x) (mk_onum y))
          | functions ("exp",[x,y]) =
            partial_dest_onum (exp (mk_onum x) (mk_onum y))
          | functions ("div",[x,y]) =
            partial_dest_onum (odiv (mk_onum x) (mk_onum y))
          | functions ("mod",[x,y]) =
            partial_dest_onum (omod (mk_onum x) (mk_onum y))
          | functions _ = NONE
  
        fun relations ("is_0",[x]) = SOME (mk_onum x = zero)
          | relations ("<=",[x,y]) = le (mk_onum x) (mk_onum y)
          | relations ("<",[x,y]) = lt (mk_onum x) (mk_onum y)
          | relations (">=",[x,y]) = ge (mk_onum x) (mk_onum y)
          | relations (">",[x,y]) = gt (mk_onum x) (mk_onum y)
          | relations ("divides",[x,y]) = divides (mk_onum x) (mk_onum y)
          | relations ("even",[x]) = even (mk_onum x)
          | relations ("odd",[x]) = odd (mk_onum x)
          | relations _ = NONE
      in
        {functions = functions, relations = relations}
      end;
in
  fun fixedOverflowNum {size = N} =
      let
        val oinf = N - 1
  
        fun mk_onum x = if x = oinf then OInf else ONum x
  
        fun dest_onum ONeg = NONE
          | dest_onum (ONum x) = SOME (if x < oinf then x else oinf)
          | dest_onum OInf = SOME oinf
      in
        fixedOverflow mk_onum dest_onum
      end;

  fun fixedOverflowInt {size = N} =
      let
        val oinf = N - 2
        val oneg = N - 1
  
        fun mk_onum x =
            if x = oneg then ONeg else if x = oinf then OInf else ONum x
  
        fun dest_onum ONeg = SOME oneg
          | dest_onum (ONum x) = SOME (if x < oinf then x else oinf)
          | dest_onum OInf = SOME oinf
      in
        fixedOverflow mk_onum dest_onum
      end;
end;

fun fixedSet {size = N} =
    let
      val M =
          let
            fun f 0 acc = acc
              | f x acc = f (x div 2) (acc + 1)
          in
            f N 0
          end

      val univ = IntSet.fromList (interval 0 M)

      val mk_set =
          let
            fun f _ s 0 = s
              | f k s x =
                let
                  val s = if x mod 2 = 0 then s else IntSet.add s k
                in
                  f (k + 1) s (x div 2)
                end
          in
            f 0 IntSet.empty
          end

      fun dest_set s =
          let
            fun f 0 x = x
              | f k x =
                let
                  val k = k - 1
                in
                  f k (if IntSet.member k s then 2 * x + 1 else 2 * x)
                end

            val x = case IntSet.findr (K true) s of NONE => 0 | SOME k => f k 1
          in
            if x < N then SOME x else NONE
          end

      fun functions ("empty",[]) = dest_set IntSet.empty
        | functions ("univ",[]) = dest_set univ
        | functions ("union",[x,y]) =
          dest_set (IntSet.union (mk_set x) (mk_set y))
        | functions ("intersect",[x,y]) =
          dest_set (IntSet.intersect (mk_set x) (mk_set y))
        | functions ("compl",[x]) =
          dest_set (IntSet.difference univ (mk_set x))
        | functions ("card",[x]) = SOME (IntSet.size (mk_set x))
        | functions _ = NONE
  
      fun relations ("in",[x,y]) = SOME (IntSet.member (x mod M) (mk_set y))
        | relations ("subset",[x,y]) =
          SOME (IntSet.subset (mk_set x) (mk_set y))
        | relations _ = NONE
    in
      {functions = functions, relations = relations}
    end;

(* ------------------------------------------------------------------------- *)
(* A type of random finite models.                                           *)
(* ------------------------------------------------------------------------- *)

type parameters = {size : int, fixed : fixed};

datatype model =
    Model of
      {size : int,
       fixed : fixedModel,
       functions : (Term.functionName * int list, int) Map.map Unsynchronized.ref,
       relations : (Atom.relationName * int list, bool) Map.map Unsynchronized.ref};

local
  fun cmp ((n1,l1),(n2,l2)) =
      case String.compare (n1,n2) of
        LESS => LESS
      | EQUAL => lexCompare Int.compare (l1,l2)
      | GREATER => GREATER;
in
  fun new {size = N, fixed} =
      Model
        {size = N,
         fixed = fixed {size = N},
         functions = Unsynchronized.ref (Map.new cmp),
         relations = Unsynchronized.ref (Map.new cmp)};
end;

fun size (Model {size = s, ...}) = s;

(* ------------------------------------------------------------------------- *)
(* Valuations.                                                               *)
(* ------------------------------------------------------------------------- *)

type valuation = int NameMap.map;

val valuationEmpty : valuation = NameMap.new ();

fun valuationRandom {size = N} vs =
    let
      fun f (v,V) = NameMap.insert V (v, Portable.randomInt N)
    in
      NameSet.foldl f valuationEmpty vs
    end;

fun valuationFold {size = N} vs f =
    let
      val vs = NameSet.toList vs

      fun inc [] _ = NONE
        | inc (v :: l) V =
          case NameMap.peek V v of
            NONE => raise Bug "Model.valuationFold"
          | SOME k =>
            let
              val k = if k = N - 1 then 0 else k + 1
              val V = NameMap.insert V (v,k)
            in
              if k = 0 then inc l V else SOME V
            end

      val zero = foldl (fn (v,V) => NameMap.insert V (v,0)) valuationEmpty vs

      fun fold V acc =
          let
            val acc = f (V,acc)
          in
            case inc vs V of NONE => acc | SOME V => fold V acc
          end
    in
      fold zero
    end;

(* ------------------------------------------------------------------------- *)
(* Interpreting terms and formulas in the model.                             *)
(* ------------------------------------------------------------------------- *)

fun interpretTerm M V =
    let
      val Model {size = N, fixed, functions, ...} = M
      val {functions = fixed_functions, ...} = fixed

      fun interpret (Term.Var v) =
          (case NameMap.peek V v of
             NONE => raise Error "Model.interpretTerm: incomplete valuation"
           | SOME i => i)
        | interpret (tm as Term.Fn f_tms) =
          let
            val (f,tms) =
                case Term.stripComb tm of
                  (_,[]) => f_tms
                | (v as Term.Var _, tms) => (".", v :: tms)
                | (Term.Fn (f,tms), tms') => (f, tms @ tms')
            val elts = map interpret tms
            val f_elts = (f,elts)
            val Unsynchronized.ref funcs = functions
          in
            case Map.peek funcs f_elts of
              SOME k => k
            | NONE =>
              let
                val k =
                    case fixed_functions f_elts of
                      SOME k => k
                    | NONE => Portable.randomInt N

                val () = functions := Map.insert funcs (f_elts,k)
              in
                k
              end
          end;
    in
      interpret
    end;

fun interpretAtom M V (r,tms) =
    let
      val Model {fixed,relations,...} = M
      val {relations = fixed_relations, ...} = fixed

      val elts = map (interpretTerm M V) tms
      val r_elts = (r,elts)
      val Unsynchronized.ref rels = relations
    in
      case Map.peek rels r_elts of
        SOME b => b
      | NONE =>
        let
          val b =
              case fixed_relations r_elts of
                SOME b => b
              | NONE => Portable.randomBool ()

          val () = relations := Map.insert rels (r_elts,b)
        in
          b
        end
    end;

fun interpretFormula M =
    let
      val Model {size = N, ...} = M

      fun interpret _ Formula.True = true
        | interpret _ Formula.False = false
        | interpret V (Formula.Atom atm) = interpretAtom M V atm
        | interpret V (Formula.Not p) = not (interpret V p)
        | interpret V (Formula.Or (p,q)) = interpret V p orelse interpret V q
        | interpret V (Formula.And (p,q)) = interpret V p andalso interpret V q
        | interpret V (Formula.Imp (p,q)) =
          interpret V (Formula.Or (Formula.Not p, q))
        | interpret V (Formula.Iff (p,q)) = interpret V p = interpret V q
        | interpret V (Formula.Forall (v,p)) = interpret' V v p N
        | interpret V (Formula.Exists (v,p)) =
          interpret V (Formula.Not (Formula.Forall (v, Formula.Not p)))
      and interpret' _ _ _ 0 = true
        | interpret' V v p i =
          let
            val i = i - 1
            val V' = NameMap.insert V (v,i)
          in
            interpret V' p andalso interpret' V v p i
          end
    in
      interpret
    end;

fun interpretLiteral M V (true,atm) = interpretAtom M V atm
  | interpretLiteral M V (false,atm) = not (interpretAtom M V atm);

fun interpretClause M V cl = LiteralSet.exists (interpretLiteral M V) cl;

(* ------------------------------------------------------------------------- *)
(* Check whether random groundings of a formula are true in the model.       *)
(* Note: if it's cheaper, a systematic check will be performed instead.      *)
(* ------------------------------------------------------------------------- *)

local
  fun checkGen freeVars interpret {maxChecks} M x =
      let
        val Model {size = N, ...} = M
            
        fun score (V,{T,F}) =
            if interpret M V x then {T = T + 1, F = F} else {T = T, F = F + 1}

        val vs = freeVars x

        fun randomCheck acc = score (valuationRandom {size = N} vs, acc)

        val small =
            intExp N (NameSet.size vs) <= maxChecks handle Overflow => false
      in
        if small then valuationFold {size = N} vs score {T = 0, F = 0}
        else funpow maxChecks randomCheck {T = 0, F = 0}
      end;
in
  val checkAtom = checkGen Atom.freeVars interpretAtom;

  val checkFormula = checkGen Formula.freeVars interpretFormula;

  val checkLiteral = checkGen Literal.freeVars interpretLiteral;

  val checkClause = checkGen LiteralSet.freeVars interpretClause;
end;

end
end;

(**** Original file: Problem.sig ****)

(* ========================================================================= *)
(* SOME SAMPLE PROBLEMS TO TEST PROOF PROCEDURES                             *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Problem =
sig

(* ------------------------------------------------------------------------- *)
(* Problems.                                                                 *)
(* ------------------------------------------------------------------------- *)

type problem = Metis.Thm.clause list

val size : problem -> {clauses : int,
                       literals : int,
                       symbols : int,
                       typedSymbols : int}

val fromGoal : Metis.Formula.formula -> problem list

val toClauses : problem -> Metis.Formula.formula

val toString : problem -> string

(* ------------------------------------------------------------------------- *)
(* Categorizing problems.                                                    *)
(* ------------------------------------------------------------------------- *)

datatype propositional =
    Propositional
  | EffectivelyPropositional
  | NonPropositional

datatype equality =
    NonEquality
  | Equality
  | PureEquality

datatype horn =
    Trivial
  | Unit
  | DoubleHorn
  | Horn
  | NegativeHorn
  | NonHorn

type category =
     {propositional : propositional,
      equality : equality,
      horn : horn}

val categorize : problem -> category

val categoryToString : category -> string

end

(**** Original file: Problem.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* SOME SAMPLE PROBLEMS TO TEST PROOF PROCEDURES                             *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Problem :> Problem =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* Problems.                                                                 *)
(* ------------------------------------------------------------------------- *)

type problem = Thm.clause list;

fun size cls =
    {clauses = length cls,
     literals = foldl (fn (cl,n) => n + LiteralSet.size cl) 0 cls,
     symbols = foldl (fn (cl,n) => n + LiteralSet.symbols cl) 0 cls,
     typedSymbols = foldl (fn (cl,n) => n + LiteralSet.typedSymbols cl) 0 cls};

fun checkFormula {models,checks} exp fm =
    let
      fun check 0 = true
        | check n =
          let
            val N = 3 + Portable.randomInt 3
            val M = Model.new {size = N, fixed = Model.fixedPure}
            val {T,F} = Model.checkFormula {maxChecks = checks} M fm
          in
            (if exp then F = 0 else T = 0) andalso check (n - 1)
          end
    in
      check models
    end;

val checkGoal = checkFormula {models = 10, checks = 100} true;

val checkClauses = checkFormula {models = 10, checks = 100} false;

fun fromGoal goal =
    let
      fun fromLiterals fms = LiteralSet.fromList (map Literal.fromFormula fms)

      fun fromClause fm = fromLiterals (Formula.stripDisj fm)

      fun fromCnf fm = map fromClause (Formula.stripConj fm)

(*DEBUG
      val () = if checkGoal goal then ()
               else raise Error "goal failed the finite model test"
*)

      val refute = Formula.Not (Formula.generalize goal)

(*TRACE2
      val () = Parser.ppTrace Formula.pp "Problem.fromGoal: refute" refute
*)

      val cnfs = Normalize.cnf refute

(*
      val () =
          let
            fun check fm =
                let
(*TRACE2
                  val () = Parser.ppTrace Formula.pp "Problem.fromGoal: cnf" fm
*)
                in
                  if checkClauses fm then ()
                  else raise Error "cnf failed the finite model test"
                end
          in
            app check cnfs
          end
*)
    in
      map fromCnf cnfs
    end;

fun toClauses cls =
    let
      fun formulize cl =
          Formula.listMkDisj (LiteralSet.transform Literal.toFormula cl)
    in
      Formula.listMkConj (map formulize cls)
    end;

fun toString cls = Formula.toString (toClauses cls);

(* ------------------------------------------------------------------------- *)
(* Categorizing problems.                                                    *)
(* ------------------------------------------------------------------------- *)

datatype propositional =
    Propositional
  | EffectivelyPropositional
  | NonPropositional;

datatype equality =
    NonEquality
  | Equality
  | PureEquality;

datatype horn =
    Trivial
  | Unit
  | DoubleHorn
  | Horn
  | NegativeHorn
  | NonHorn;

type category =
     {propositional : propositional,
      equality : equality,
      horn : horn};

fun categorize cls =
    let
      val rels =
          let
            fun f (cl,set) = NameAritySet.union set (LiteralSet.relations cl)
          in
            List.foldl f NameAritySet.empty cls
          end

      val funs =
          let
            fun f (cl,set) = NameAritySet.union set (LiteralSet.functions cl)
          in
            List.foldl f NameAritySet.empty cls
          end

      val propositional =
          if NameAritySet.allNullary rels then Propositional
          else if NameAritySet.allNullary funs then EffectivelyPropositional
          else NonPropositional

      val equality =
          if not (NameAritySet.member Atom.eqRelation rels) then NonEquality
          else if NameAritySet.size rels = 1 then PureEquality
          else Equality

      val horn =
          if List.exists LiteralSet.null cls then Trivial
          else if List.all (fn cl => LiteralSet.size cl = 1) cls then Unit
          else 
            let
              fun pos cl = LiteralSet.count Literal.positive cl <= 1
              fun neg cl = LiteralSet.count Literal.negative cl <= 1
            in
              case (List.all pos cls, List.all neg cls) of
                (true,true) => DoubleHorn
              | (true,false) => Horn
              | (false,true) => NegativeHorn
              | (false,false) => NonHorn
            end
    in
      {propositional = propositional,
       equality = equality,
       horn = horn}
    end;

fun categoryToString {propositional,equality,horn} =
    (case propositional of
       Propositional => "propositional"
     | EffectivelyPropositional => "effectively propositional"
     | NonPropositional => "non-propositional") ^
    ", " ^
    (case equality of
       NonEquality => "non-equality"
     | Equality => "equality"
     | PureEquality => "pure equality") ^
    ", " ^
    (case horn of
       Trivial => "trivial"
     | Unit => "unit"
     | DoubleHorn => "horn (and negative horn)"
     | Horn => "horn"
     | NegativeHorn => "negative horn"
     | NonHorn => "non-horn");

end
end;

(**** Original file: TermNet.sig ****)

(* ========================================================================= *)
(* MATCHING AND UNIFICATION FOR SETS OF FIRST ORDER LOGIC TERMS              *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature TermNet =
sig

(* ------------------------------------------------------------------------- *)
(* A type of term sets that can be efficiently matched and unified.          *)
(* ------------------------------------------------------------------------- *)

type parameters = {fifo : bool}

type 'a termNet

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val new : parameters -> 'a termNet

val null : 'a termNet -> bool

val size : 'a termNet -> int

val insert : 'a termNet -> Metis.Term.term * 'a -> 'a termNet

val fromList : parameters -> (Metis.Term.term * 'a) list -> 'a termNet

val filter : ('a -> bool) -> 'a termNet -> 'a termNet

val toString : 'a termNet -> string

val pp : 'a Metis.Parser.pp -> 'a termNet Metis.Parser.pp

(* ------------------------------------------------------------------------- *)
(* Matching and unification queries.                                         *)
(*                                                                           *)
(* These function return OVER-APPROXIMATIONS!                                *)
(* Filter afterwards to get the precise set of satisfying values.            *)
(* ------------------------------------------------------------------------- *)

val match : 'a termNet -> Metis.Term.term -> 'a list

val matched : 'a termNet -> Metis.Term.term -> 'a list

val unify : 'a termNet -> Metis.Term.term -> 'a list

end

(**** Original file: TermNet.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* MATCHING AND UNIFICATION FOR SETS OF FIRST ORDER LOGIC TERMS              *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure TermNet :> TermNet =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* Quotient terms                                                            *)
(* ------------------------------------------------------------------------- *)

datatype qterm = VAR | FN of NameArity.nameArity * qterm list;

fun termToQterm (Term.Var _) = VAR
  | termToQterm (Term.Fn (f,l)) = FN ((f, length l), map termToQterm l);

local
  fun qm [] = true
    | qm ((VAR,_) :: rest) = qm rest
    | qm ((FN _, VAR) :: _) = false
    | qm ((FN (f,a), FN (g,b)) :: rest) = f = g andalso qm (zip a b @ rest);
in
  fun matchQtermQterm qtm qtm' = qm [(qtm,qtm')];
end;

local
  fun qm [] = true
    | qm ((VAR,_) :: rest) = qm rest
    | qm ((FN _, Term.Var _) :: _) = false
    | qm ((FN ((f,n),a), Term.Fn (g,b)) :: rest) =
      f = g andalso n = length b andalso qm (zip a b @ rest);
in
  fun matchQtermTerm qtm tm = qm [(qtm,tm)];
end;

local
  fun qn qsub [] = SOME qsub
    | qn qsub ((Term.Var v, qtm) :: rest) =
      (case NameMap.peek qsub v of
         NONE => qn (NameMap.insert qsub (v,qtm)) rest
       | SOME qtm' => if qtm = qtm' then qn qsub rest else NONE)
    | qn _ ((Term.Fn _, VAR) :: _) = NONE
    | qn qsub ((Term.Fn (f,a), FN ((g,n),b)) :: rest) =
      if f = g andalso length a = n then qn qsub (zip a b @ rest) else NONE;
in
  fun matchTermQterm qsub tm qtm = qn qsub [(tm,qtm)];
end;

local
  fun qv VAR x = x
    | qv x VAR = x
    | qv (FN (f,a)) (FN (g,b)) =
      let
        val _ = f = g orelse raise Error "TermNet.qv"
      in
        FN (f, zipwith qv a b)
      end;

  fun qu qsub [] = qsub
    | qu qsub ((VAR, _) :: rest) = qu qsub rest
    | qu qsub ((qtm, Term.Var v) :: rest) =
      let
        val qtm =
            case NameMap.peek qsub v of NONE => qtm | SOME qtm' => qv qtm qtm'
      in
        qu (NameMap.insert qsub (v,qtm)) rest
      end
    | qu qsub ((FN ((f,n),a), Term.Fn (g,b)) :: rest) =
      if f = g andalso n = length b then qu qsub (zip a b @ rest)
      else raise Error "TermNet.qu";
in
  fun unifyQtermQterm qtm qtm' = total (qv qtm) qtm';

  fun unifyQtermTerm qsub qtm tm = total (qu qsub) [(qtm,tm)];
end;

local
  fun qtermToTerm VAR = Term.Var ""
    | qtermToTerm (FN ((f,_),l)) = Term.Fn (f, map qtermToTerm l);
in
  val ppQterm = Parser.ppMap qtermToTerm Term.pp;
end;

(* ------------------------------------------------------------------------- *)
(* A type of term sets that can be efficiently matched and unified.          *)
(* ------------------------------------------------------------------------- *)

type parameters = {fifo : bool};

datatype 'a net =
    RESULT of 'a list
  | SINGLE of qterm * 'a net
  | MULTIPLE of 'a net option * 'a net NameArityMap.map;

datatype 'a termNet = NET of parameters * int * (int * (int * 'a) net) option;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

fun new parm = NET (parm,0,NONE);

local
  fun computeSize (RESULT l) = length l
    | computeSize (SINGLE (_,n)) = computeSize n
    | computeSize (MULTIPLE (vs,fs)) =
      NameArityMap.foldl
        (fn (_,n,acc) => acc + computeSize n)
        (case vs of SOME n => computeSize n | NONE => 0)
        fs;
in
  fun netSize NONE = NONE
    | netSize (SOME n) = SOME (computeSize n, n);
end;

fun size (NET (_,_,NONE)) = 0
  | size (NET (_, _, SOME (i,_))) = i;

fun null net = size net = 0;

fun singles qtms a = foldr SINGLE a qtms;

local
  fun pre NONE = (0,NONE)
    | pre (SOME (i,n)) = (i, SOME n);

  fun add (RESULT l) [] (RESULT l') = RESULT (l @ l')
    | add a (input1 as qtm :: qtms) (SINGLE (qtm',n)) =
      if qtm = qtm' then SINGLE (qtm, add a qtms n)
      else add a input1 (add n [qtm'] (MULTIPLE (NONE, NameArityMap.new ())))
    | add a (VAR :: qtms) (MULTIPLE (vs,fs)) =
      MULTIPLE (SOME (oadd a qtms vs), fs)
    | add a (FN (f,l) :: qtms) (MULTIPLE (vs,fs)) =
      let
        val n = NameArityMap.peek fs f
      in
        MULTIPLE (vs, NameArityMap.insert fs (f, oadd a (l @ qtms) n))
      end
    | add _ _ _ = raise Bug "TermNet.insert: Match"

  and oadd a qtms NONE = singles qtms a
    | oadd a qtms (SOME n) = add a qtms n;

  fun ins a qtm (i,n) = SOME (i + 1, oadd (RESULT [a]) [qtm] n);
in
  fun insert (NET (p,k,n)) (tm,a) =
      NET (p, k + 1, ins (k,a) (termToQterm tm) (pre n))
      handle Error _ => raise Bug "TermNet.insert: should never fail";
end;

fun fromList parm l = foldl (fn (tm_a,n) => insert n tm_a) (new parm) l;

fun filter pred =
    let
      fun filt (RESULT l) =
          (case List.filter (fn (_,a) => pred a) l of
             [] => NONE
           | l => SOME (RESULT l))
        | filt (SINGLE (qtm,n)) =
          (case filt n of
             NONE => NONE
           | SOME n => SOME (SINGLE (qtm,n)))
        | filt (MULTIPLE (vs,fs)) =
          let
            val vs = Option.mapPartial filt vs

            val fs = NameArityMap.mapPartial (fn (_,n) => filt n) fs
          in
            if not (Option.isSome vs) andalso NameArityMap.null fs then NONE
            else SOME (MULTIPLE (vs,fs))
          end
    in
      fn net as NET (_,_,NONE) => net
       | NET (p, k, SOME (_,n)) => NET (p, k, netSize (filt n))
    end
    handle Error _ => raise Bug "TermNet.filter: should never fail";

fun toString net = "TermNet[" ^ Int.toString (size net) ^ "]";

(* ------------------------------------------------------------------------- *)
(* Specialized fold operations to support matching and unification.          *)
(* ------------------------------------------------------------------------- *)

local
  fun norm (0 :: ks, (f as (_,n)) :: fs, qtms) =
      let
        val (a,qtms) = revDivide qtms n
      in
        addQterm (FN (f,a)) (ks,fs,qtms)
      end
    | norm stack = stack

  and addQterm qtm (ks,fs,qtms) =
      let
        val ks = case ks of [] => [] | k :: ks => (k - 1) :: ks
      in
        norm (ks, fs, qtm :: qtms)
      end

  and addFn (f as (_,n)) (ks,fs,qtms) = norm (n :: ks, f :: fs, qtms);
in
  val stackEmpty = ([],[],[]);
    
  val stackAddQterm = addQterm;

  val stackAddFn = addFn;

  fun stackValue ([],[],[qtm]) = qtm
    | stackValue _ = raise Bug "TermNet.stackValue";
end;

local
  fun fold _ acc [] = acc
    | fold inc acc ((0,stack,net) :: rest) =
      fold inc (inc (stackValue stack, net, acc)) rest
    | fold inc acc ((n, stack, SINGLE (qtm,net)) :: rest) =
      fold inc acc ((n - 1, stackAddQterm qtm stack, net) :: rest)
    | fold inc acc ((n, stack, MULTIPLE (v,fns)) :: rest) =
      let
        val n = n - 1

        val rest =
            case v of
              NONE => rest
            | SOME net => (n, stackAddQterm VAR stack, net) :: rest

        fun getFns (f as (_,k), net, x) =
            (k + n, stackAddFn f stack, net) :: x
      in
        fold inc acc (NameArityMap.foldr getFns rest fns)
      end
    | fold _ _ _ = raise Bug "TermNet.foldTerms.fold";
in
  fun foldTerms inc acc net = fold inc acc [(1,stackEmpty,net)];
end;

fun foldEqualTerms pat inc acc =
    let
      fun fold ([],net) = inc (pat,net,acc)
        | fold (pat :: pats, SINGLE (qtm,net)) =
          if pat = qtm then fold (pats,net) else acc
        | fold (VAR :: pats, MULTIPLE (v,_)) =
          (case v of NONE => acc | SOME net => fold (pats,net))
        | fold (FN (f,a) :: pats, MULTIPLE (_,fns)) =
          (case NameArityMap.peek fns f of
             NONE => acc
           | SOME net => fold (a @ pats, net))
        | fold _ = raise Bug "TermNet.foldEqualTerms.fold";
    in
      fn net => fold ([pat],net)
    end;

local
  fun fold _ acc [] = acc
    | fold inc acc (([],stack,net) :: rest) =
      fold inc (inc (stackValue stack, net, acc)) rest
    | fold inc acc ((VAR :: pats, stack, net) :: rest) =
      let
        fun harvest (qtm,n,l) = (pats, stackAddQterm qtm stack, n) :: l
      in
        fold inc acc (foldTerms harvest rest net)
      end
    | fold inc acc ((pat :: pats, stack, SINGLE (qtm,net)) :: rest) =
      (case unifyQtermQterm pat qtm of
         NONE => fold inc acc rest
       | SOME qtm =>
         fold inc acc ((pats, stackAddQterm qtm stack, net) :: rest))
    | fold
        inc acc
        (((pat as FN (f,a)) :: pats, stack, MULTIPLE (v,fns)) :: rest) =
      let
        val rest =
            case v of
              NONE => rest
            | SOME net => (pats, stackAddQterm pat stack, net) :: rest

        val rest =
            case NameArityMap.peek fns f of
              NONE => rest
            | SOME net => (a @ pats, stackAddFn f stack, net) :: rest
      in
        fold inc acc rest
      end
    | fold _ _ _ = raise Bug "TermNet.foldUnifiableTerms.fold";
in
  fun foldUnifiableTerms pat inc acc net =
      fold inc acc [([pat],stackEmpty,net)];
end;

(* ------------------------------------------------------------------------- *)
(* Matching and unification queries.                                         *)
(*                                                                           *)
(* These function return OVER-APPROXIMATIONS!                                *)
(* Filter afterwards to get the precise set of satisfying values.            *)
(* ------------------------------------------------------------------------- *)

local
  fun idwise ((m,_),(n,_)) = Int.compare (m,n);

  fun fifoize ({fifo, ...} : parameters) l = if fifo then sort idwise l else l;
in
  fun finally parm l = map snd (fifoize parm l);
end;

local
  fun mat acc [] = acc
    | mat acc ((RESULT l, []) :: rest) = mat (l @ acc) rest
    | mat acc ((SINGLE (qtm,n), tm :: tms) :: rest) =
      mat acc (if matchQtermTerm qtm tm then (n,tms) :: rest else rest)
    | mat acc ((MULTIPLE (vs,fs), tm :: tms) :: rest) =
      let
        val rest = case vs of NONE => rest | SOME n => (n,tms) :: rest

        val rest =
            case tm of
              Term.Var _ => rest
            | Term.Fn (f,l) =>
              case NameArityMap.peek fs (f, length l) of
                NONE => rest
              | SOME n => (n, l @ tms) :: rest
      in
        mat acc rest
      end
    | mat _ _ = raise Bug "TermNet.match: Match";
in
  fun match (NET (_,_,NONE)) _ = []
    | match (NET (p, _, SOME (_,n))) tm =
      finally p (mat [] [(n,[tm])])
      handle Error _ => raise Bug "TermNet.match: should never fail";
end;

local
  fun unseenInc qsub v tms (qtm,net,rest) =
      (NameMap.insert qsub (v,qtm), net, tms) :: rest;

  fun seenInc qsub tms (_,net,rest) = (qsub,net,tms) :: rest;

  fun mat acc [] = acc
    | mat acc ((_, RESULT l, []) :: rest) = mat (l @ acc) rest
    | mat acc ((qsub, SINGLE (qtm,net), tm :: tms) :: rest) =
      (case matchTermQterm qsub tm qtm of
         NONE => mat acc rest
       | SOME qsub => mat acc ((qsub,net,tms) :: rest))
    | mat acc ((qsub, net as MULTIPLE _, Term.Var v :: tms) :: rest) =
      (case NameMap.peek qsub v of
         NONE => mat acc (foldTerms (unseenInc qsub v tms) rest net)
       | SOME qtm => mat acc (foldEqualTerms qtm (seenInc qsub tms) rest net))
    | mat acc ((qsub, MULTIPLE (_,fns), Term.Fn (f,a) :: tms) :: rest) =
      let
        val rest =
            case NameArityMap.peek fns (f, length a) of
              NONE => rest
            | SOME net => (qsub, net, a @ tms) :: rest
      in
        mat acc rest
      end
    | mat _ _ = raise Bug "TermNet.matched.mat";
in
  fun matched (NET (_,_,NONE)) _ = []
    | matched (NET (parm, _, SOME (_,net))) tm =
      finally parm (mat [] [(NameMap.new (), net, [tm])])
      handle Error _ => raise Bug "TermNet.matched: should never fail";
end;

local
  fun inc qsub v tms (qtm,net,rest) =
      (NameMap.insert qsub (v,qtm), net, tms) :: rest;

  fun mat acc [] = acc
    | mat acc ((_, RESULT l, []) :: rest) = mat (l @ acc) rest
    | mat acc ((qsub, SINGLE (qtm,net), tm :: tms) :: rest) =
      (case unifyQtermTerm qsub qtm tm of
         NONE => mat acc rest
       | SOME qsub => mat acc ((qsub,net,tms) :: rest))
    | mat acc ((qsub, net as MULTIPLE _, Term.Var v :: tms) :: rest) =
      (case NameMap.peek qsub v of
         NONE => mat acc (foldTerms (inc qsub v tms) rest net)
       | SOME qtm => mat acc (foldUnifiableTerms qtm (inc qsub v tms) rest net))
    | mat acc ((qsub, MULTIPLE (v,fns), Term.Fn (f,a) :: tms) :: rest) =
      let
        val rest = case v of NONE => rest | SOME net => (qsub,net,tms) :: rest

        val rest =
            case NameArityMap.peek fns (f, length a) of
              NONE => rest
            | SOME net => (qsub, net, a @ tms) :: rest
      in
        mat acc rest
      end
    | mat _ _ = raise Bug "TermNet.unify.mat";
in
  fun unify (NET (_,_,NONE)) _ = []
    | unify (NET (parm, _, SOME (_,net))) tm =
      finally parm (mat [] [(NameMap.new (), net, [tm])])
      handle Error _ => raise Bug "TermNet.unify: should never fail";
end;

(* ------------------------------------------------------------------------- *)
(* Pretty printing.                                                          *)
(* ------------------------------------------------------------------------- *)

local
  fun inc (qtm, RESULT l, acc) =
      foldl (fn ((n,a),acc) => (n,(qtm,a)) :: acc) acc l
    | inc _ = raise Bug "TermNet.pp.inc";
      
  fun toList (NET (_,_,NONE)) = []
    | toList (NET (parm, _, SOME (_,net))) =
      finally parm (foldTerms inc [] net);
in
  fun pp ppA =
      Parser.ppMap toList (Parser.ppList (Parser.ppBinop " |->" ppQterm ppA));
end;

end
end;

(**** Original file: AtomNet.sig ****)

(* ========================================================================= *)
(* MATCHING AND UNIFICATION FOR SETS OF FIRST ORDER LOGIC ATOMS              *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature AtomNet =
sig

(* ------------------------------------------------------------------------- *)
(* A type of atom sets that can be efficiently matched and unified.          *)
(* ------------------------------------------------------------------------- *)

type parameters = {fifo : bool}

type 'a atomNet

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val new : parameters -> 'a atomNet

val size : 'a atomNet -> int

val insert : 'a atomNet -> Metis.Atom.atom * 'a -> 'a atomNet

val fromList : parameters -> (Metis.Atom.atom * 'a) list -> 'a atomNet

val filter : ('a -> bool) -> 'a atomNet -> 'a atomNet

val toString : 'a atomNet -> string

val pp : 'a Metis.Parser.pp -> 'a atomNet Metis.Parser.pp

(* ------------------------------------------------------------------------- *)
(* Matching and unification queries.                                         *)
(*                                                                           *)
(* These function return OVER-APPROXIMATIONS!                                *)
(* Filter afterwards to get the precise set of satisfying values.            *)
(* ------------------------------------------------------------------------- *)

val match : 'a atomNet -> Metis.Atom.atom -> 'a list

val matched : 'a atomNet -> Metis.Atom.atom -> 'a list

val unify : 'a atomNet -> Metis.Atom.atom -> 'a list

end

(**** Original file: AtomNet.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* MATCHING AND UNIFICATION FOR SETS OF FIRST ORDER LOGIC ATOMS              *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure AtomNet :> AtomNet =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun atomToTerm atom = Term.Fn atom;

fun termToAtom (Term.Var _) = raise Bug "AtomNet.termToAtom"
  | termToAtom (Term.Fn atom) = atom;

(* ------------------------------------------------------------------------- *)
(* A type of atom sets that can be efficiently matched and unified.          *)
(* ------------------------------------------------------------------------- *)

type parameters = TermNet.parameters;

type 'a atomNet = 'a TermNet.termNet;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val new = TermNet.new;

val size = TermNet.size;

fun insert net (atm,a) = TermNet.insert net (atomToTerm atm, a);

fun fromList parm l = foldl (fn (atm_a,n) => insert n atm_a) (new parm) l;

val filter = TermNet.filter;

fun toString net = "AtomNet[" ^ Int.toString (size net) ^ "]";

val pp = TermNet.pp;

(* ------------------------------------------------------------------------- *)
(* Matching and unification queries.                                         *)
(*                                                                           *)
(* These function return OVER-APPROXIMATIONS!                                *)
(* Filter afterwards to get the precise set of satisfying values.            *)
(* ------------------------------------------------------------------------- *)

fun match net atm = TermNet.match net (atomToTerm atm);

fun matched net atm = TermNet.matched net (atomToTerm atm);

fun unify net atm = TermNet.unify net (atomToTerm atm);

end
end;

(**** Original file: LiteralNet.sig ****)

(* ========================================================================= *)
(* MATCHING AND UNIFICATION FOR SETS OF FIRST ORDER LOGIC LITERALS           *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature LiteralNet =
sig

(* ------------------------------------------------------------------------- *)
(* A type of literal sets that can be efficiently matched and unified.       *)
(* ------------------------------------------------------------------------- *)

type parameters = {fifo : bool}

type 'a literalNet

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val new : parameters -> 'a literalNet

val size : 'a literalNet -> int

val profile : 'a literalNet -> {positive : int, negative : int}

val insert : 'a literalNet -> Metis.Literal.literal * 'a -> 'a literalNet

val fromList : parameters -> (Metis.Literal.literal * 'a) list -> 'a literalNet

val filter : ('a -> bool) -> 'a literalNet -> 'a literalNet

val toString : 'a literalNet -> string

val pp : 'a Metis.Parser.pp -> 'a literalNet Metis.Parser.pp

(* ------------------------------------------------------------------------- *)
(* Matching and unification queries.                                         *)
(*                                                                           *)
(* These function return OVER-APPROXIMATIONS!                                *)
(* Filter afterwards to get the precise set of satisfying values.            *)
(* ------------------------------------------------------------------------- *)

val match : 'a literalNet -> Metis.Literal.literal -> 'a list

val matched : 'a literalNet -> Metis.Literal.literal -> 'a list

val unify : 'a literalNet -> Metis.Literal.literal -> 'a list

end

(**** Original file: LiteralNet.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* MATCHING AND UNIFICATION FOR SETS OF FIRST ORDER LOGIC LITERALS           *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure LiteralNet :> LiteralNet =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* A type of literal sets that can be efficiently matched and unified.       *)
(* ------------------------------------------------------------------------- *)

type parameters = AtomNet.parameters;

type 'a literalNet =
    {positive : 'a AtomNet.atomNet,
     negative : 'a AtomNet.atomNet};

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

fun new parm = {positive = AtomNet.new parm, negative = AtomNet.new parm};

local
  fun pos ({positive,...} : 'a literalNet) = AtomNet.size positive;

  fun neg ({negative,...} : 'a literalNet) = AtomNet.size negative;
in
  fun size net = pos net + neg net;

  fun profile net = {positive = pos net, negative = neg net};
end;

fun insert {positive,negative} ((true,atm),a) =
    {positive = AtomNet.insert positive (atm,a), negative = negative}
  | insert {positive,negative} ((false,atm),a) =
    {positive = positive, negative = AtomNet.insert negative (atm,a)};

fun fromList parm l = foldl (fn (lit_a,n) => insert n lit_a) (new parm) l;

fun filter pred {positive,negative} =
    {positive = AtomNet.filter pred positive,
     negative = AtomNet.filter pred negative};

fun toString net = "LiteralNet[" ^ Int.toString (size net) ^ "]";

fun pp ppA =
    Parser.ppMap
      (fn {positive,negative} => (positive,negative))
      (Parser.ppBinop " + NEGATIVE" (AtomNet.pp ppA) (AtomNet.pp ppA));

(* ------------------------------------------------------------------------- *)
(* Matching and unification queries.                                         *)
(*                                                                           *)
(* These function return OVER-APPROXIMATIONS!                                *)
(* Filter afterwards to get the precise set of satisfying values.            *)
(* ------------------------------------------------------------------------- *)

fun match ({positive,...} : 'a literalNet) (true,atm) =
    AtomNet.match positive atm
  | match {negative,...} (false,atm) = AtomNet.match negative atm;

fun matched ({positive,...} : 'a literalNet) (true,atm) =
    AtomNet.matched positive atm
  | matched {negative,...} (false,atm) = AtomNet.matched negative atm;

fun unify ({positive,...} : 'a literalNet) (true,atm) =
    AtomNet.unify positive atm
  | unify {negative,...} (false,atm) = AtomNet.unify negative atm;

end
end;

(**** Original file: Subsume.sig ****)

(* ========================================================================= *)
(* SUBSUMPTION CHECKING FOR FIRST ORDER LOGIC CLAUSES                        *)
(* Copyright (c) 2002-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Subsume =
sig

(* ------------------------------------------------------------------------- *)
(* A type of clause sets that supports efficient subsumption checking.       *)
(* ------------------------------------------------------------------------- *)

type 'a subsume

val new : unit -> 'a subsume

val size : 'a subsume -> int

val insert : 'a subsume -> Metis.Thm.clause * 'a -> 'a subsume

val filter : ('a -> bool) -> 'a subsume -> 'a subsume

val pp : 'a subsume Metis.Parser.pp

val toString : 'a subsume -> string

(* ------------------------------------------------------------------------- *)
(* Subsumption checking.                                                     *)
(* ------------------------------------------------------------------------- *)

val subsumes :
    (Metis.Thm.clause * Metis.Subst.subst * 'a -> bool) -> 'a subsume -> Metis.Thm.clause ->
    (Metis.Thm.clause * Metis.Subst.subst * 'a) option

val isSubsumed : 'a subsume -> Metis.Thm.clause -> bool

val strictlySubsumes :  (* exclude subsuming clauses with more literals *)
    (Metis.Thm.clause * Metis.Subst.subst * 'a -> bool) -> 'a subsume -> Metis.Thm.clause ->
    (Metis.Thm.clause * Metis.Subst.subst * 'a) option

val isStrictlySubsumed : 'a subsume -> Metis.Thm.clause -> bool

(* ------------------------------------------------------------------------- *)
(* Single clause versions.                                                   *)
(* ------------------------------------------------------------------------- *)

val clauseSubsumes : Metis.Thm.clause -> Metis.Thm.clause -> Metis.Subst.subst option

val clauseStrictlySubsumes : Metis.Thm.clause -> Metis.Thm.clause -> Metis.Subst.subst option

end

(**** Original file: Subsume.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* SUBSUMPTION CHECKING FOR FIRST ORDER LOGIC CLAUSES                        *)
(* Copyright (c) 2002-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Subsume :> Subsume =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun findRest pred =
    let
      fun f _ [] = NONE
        | f ys (x :: xs) =
          if pred x then SOME (x, List.revAppend (ys,xs)) else f (x :: ys) xs
    in
      f []
    end;

local
  fun addSym (lit,acc) =
      case total Literal.sym lit of
        NONE => acc
      | SOME lit => lit :: acc
in
  fun clauseSym lits = List.foldl addSym lits lits;
end;

fun sortClause cl =
    let
      val lits = LiteralSet.toList cl
    in
      sortMap Literal.typedSymbols (revCompare Int.compare) lits
    end;

fun incompatible lit =
    let
      val lits = clauseSym [lit]
    in
      fn lit' => not (List.exists (can (Literal.unify Subst.empty lit')) lits)
    end;

(* ------------------------------------------------------------------------- *)
(* Clause ids and lengths.                                                   *)
(* ------------------------------------------------------------------------- *)

type clauseId = int;

type clauseLength = int;

local
  type idSet = (clauseId * clauseLength) Set.set;

  fun idCompare ((id1,len1),(id2,len2)) =
      case Int.compare (len1,len2) of
        LESS => LESS
      | EQUAL => Int.compare (id1,id2)
      | GREATER => GREATER;
in
  val idSetEmpty : idSet = Set.empty idCompare;

  fun idSetAdd (id_len,set) : idSet = Set.add set id_len;

  fun idSetAddMax max (id_len as (_,len), set) : idSet =
      if len <= max then Set.add set id_len else set;

  fun idSetIntersect set1 set2 : idSet = Set.intersect set1 set2;
end;

(* ------------------------------------------------------------------------- *)
(* A type of clause sets that supports efficient subsumption checking.       *)
(* ------------------------------------------------------------------------- *)

datatype 'a subsume =
    Subsume of
      {empty : (Thm.clause * Subst.subst * 'a) list,
       unit : (Literal.literal * Thm.clause * 'a)  LiteralNet.literalNet,
       nonunit :
         {nextId : clauseId,
          clauses : (Literal.literal list * Thm.clause * 'a) IntMap.map,
          fstLits : (clauseId * clauseLength) LiteralNet.literalNet,
          sndLits : (clauseId * clauseLength) LiteralNet.literalNet}};

fun new () =
    Subsume
      {empty = [],
       unit = LiteralNet.new {fifo = false},
       nonunit =
         {nextId = 0,
          clauses = IntMap.new (),
          fstLits = LiteralNet.new {fifo = false},
          sndLits = LiteralNet.new {fifo = false}}};

fun size (Subsume {empty, unit, nonunit = {clauses,...}}) =
    length empty + LiteralNet.size unit + IntMap.size clauses;
      
fun insert (Subsume {empty,unit,nonunit}) (cl',a) =
    case sortClause cl' of
      [] =>
      let
        val empty = (cl',Subst.empty,a) :: empty
      in
        Subsume {empty = empty, unit = unit, nonunit = nonunit}
      end
    | [lit] =>
      let
        val unit = LiteralNet.insert unit (lit,(lit,cl',a))
      in
        Subsume {empty = empty, unit = unit, nonunit = nonunit}
      end
    | fstLit :: (nonFstLits as sndLit :: otherLits) =>
      let
        val {nextId,clauses,fstLits,sndLits} = nonunit
        val id_length = (nextId, LiteralSet.size cl')
        val fstLits = LiteralNet.insert fstLits (fstLit,id_length)
        val (sndLit,otherLits) =
            case findRest (incompatible fstLit) nonFstLits of
              SOME sndLit_otherLits => sndLit_otherLits
            | NONE => (sndLit,otherLits)
        val sndLits = LiteralNet.insert sndLits (sndLit,id_length)
        val lits' = otherLits @ [fstLit,sndLit]
        val clauses = IntMap.insert clauses (nextId,(lits',cl',a))
        val nextId = nextId + 1
        val nonunit = {nextId = nextId, clauses = clauses,
                       fstLits = fstLits, sndLits = sndLits}
      in
        Subsume {empty = empty, unit = unit, nonunit = nonunit}
      end;

fun filter pred (Subsume {empty,unit,nonunit}) =
    let
      val empty = List.filter (pred o #3) empty

      val unit = LiteralNet.filter (pred o #3) unit

      val nonunit =
          let
            val {nextId,clauses,fstLits,sndLits} = nonunit
            val clauses' = IntMap.filter (pred o #3 o snd) clauses
          in
            if IntMap.size clauses = IntMap.size clauses' then nonunit
            else
              let
                fun predId (id,_) = IntMap.inDomain id clauses'
                val fstLits = LiteralNet.filter predId fstLits
                and sndLits = LiteralNet.filter predId sndLits
              in
                {nextId = nextId, clauses = clauses',
                 fstLits = fstLits, sndLits = sndLits}
              end
          end
    in
      Subsume {empty = empty, unit = unit, nonunit = nonunit}
    end;

fun toString subsume = "Subsume{" ^ Int.toString (size subsume) ^ "}";

fun pp p = Parser.ppMap toString Parser.ppString p;

(* ------------------------------------------------------------------------- *)
(* Subsumption checking.                                                     *)
(* ------------------------------------------------------------------------- *)

local
  fun matchLit lit' (lit,acc) =
      case total (Literal.match Subst.empty lit') lit of
        SOME sub => sub :: acc
      | NONE => acc;
in
  fun genClauseSubsumes pred cl' lits' cl a =
      let
        fun mkSubsl acc sub [] = SOME (sub, sortMap length Int.compare acc)
          | mkSubsl acc sub (lit' :: lits') =
            case List.foldl (matchLit lit') [] cl of
              [] => NONE
            | [sub'] =>
              (case total (Subst.union sub) sub' of
                 NONE => NONE
               | SOME sub => mkSubsl acc sub lits')
            | subs => mkSubsl (subs :: acc) sub lits'

        fun search [] = NONE
          | search ((sub,[]) :: others) =
            let
              val x = (cl',sub,a)
            in
              if pred x then SOME x else search others
            end
          | search ((_, [] :: _) :: others) = search others
          | search ((sub, (sub' :: subs) :: subsl) :: others) =
            let
              val others = (sub, subs :: subsl) :: others
            in
              case total (Subst.union sub) sub' of
                NONE => search others
              | SOME sub => search ((sub,subsl) :: others)
            end
      in
        case mkSubsl [] Subst.empty lits' of
          NONE => NONE
        | SOME sub_subsl => search [sub_subsl]
      end;
end;

local
  fun emptySubsumes pred empty = List.find pred empty;

  fun unitSubsumes pred unit =
      let
        fun subLit lit =
            let
              fun subUnit (lit',cl',a) =
                  case total (Literal.match Subst.empty lit') lit of
                    NONE => NONE
                  | SOME sub =>
                    let
                      val x = (cl',sub,a)
                    in
                      if pred x then SOME x else NONE
                    end
            in
              first subUnit (LiteralNet.match unit lit)
            end
      in
        first subLit
      end;

  fun nonunitSubsumes pred nonunit max cl =
      let
        val addId = case max of NONE => idSetAdd | SOME n => idSetAddMax n

        fun subLit lits (lit,acc) =
            List.foldl addId acc (LiteralNet.match lits lit)

        val {nextId = _, clauses, fstLits, sndLits} = nonunit

        fun subCl' (id,_) =
            let
              val (lits',cl',a) = IntMap.get clauses id
            in
              genClauseSubsumes pred cl' lits' cl a
            end

        val fstCands = List.foldl (subLit fstLits) idSetEmpty cl
        val sndCands = List.foldl (subLit sndLits) idSetEmpty cl
        val cands = idSetIntersect fstCands sndCands
      in
        Set.firstl subCl' cands
      end;

  fun genSubsumes pred (Subsume {empty,unit,nonunit}) max cl =
      case emptySubsumes pred empty of
        s as SOME _ => s
      | NONE =>
        if max = SOME 0 then NONE
        else
          let
            val cl = clauseSym (LiteralSet.toList cl)
          in
            case unitSubsumes pred unit cl of
              s as SOME _ => s
            | NONE =>
              if max = SOME 1 then NONE
              else nonunitSubsumes pred nonunit max cl
          end;
in
  fun subsumes pred subsume cl = genSubsumes pred subsume NONE cl;

  fun strictlySubsumes pred subsume cl =
      genSubsumes pred subsume (SOME (LiteralSet.size cl)) cl;
end;

(*TRACE4
val subsumes = fn pred => fn subsume => fn cl =>
    let
      val ppCl = LiteralSet.pp
      val ppSub = Subst.pp
      val () = Parser.ppTrace ppCl "Subsume.subsumes: cl" cl
      val result = subsumes pred subsume cl
      val () =
          case result of
            NONE => trace "Subsume.subsumes: not subsumed\n"
          | SOME (cl,sub,_) =>
            (Parser.ppTrace ppCl "Subsume.subsumes: subsuming cl" cl;
             Parser.ppTrace ppSub "Subsume.subsumes: subsuming sub" sub)
    in
      result
    end;

val strictlySubsumes = fn pred => fn subsume => fn cl =>
    let
      val ppCl = LiteralSet.pp
      val ppSub = Subst.pp
      val () = Parser.ppTrace ppCl "Subsume.strictlySubsumes: cl" cl
      val result = strictlySubsumes pred subsume cl
      val () =
          case result of
            NONE => trace "Subsume.subsumes: not subsumed\n"
          | SOME (cl,sub,_) =>
            (Parser.ppTrace ppCl "Subsume.subsumes: subsuming cl" cl;
             Parser.ppTrace ppSub "Subsume.subsumes: subsuming sub" sub)
    in
      result
    end;
*)

fun isSubsumed subs cl = Option.isSome (subsumes (K true) subs cl);

fun isStrictlySubsumed subs cl =
    Option.isSome (strictlySubsumes (K true) subs cl);

(* ------------------------------------------------------------------------- *)
(* Single clause versions.                                                   *)
(* ------------------------------------------------------------------------- *)

fun clauseSubsumes cl' cl =
    let
      val lits' = sortClause cl'
      and lits = clauseSym (LiteralSet.toList cl)
    in
      case genClauseSubsumes (K true) cl' lits' lits () of
        SOME (_,sub,()) => SOME sub
      | NONE => NONE
    end;

fun clauseStrictlySubsumes cl' cl =
    if LiteralSet.size cl' > LiteralSet.size cl then NONE
    else clauseSubsumes cl' cl;

end
end;

(**** Original file: KnuthBendixOrder.sig ****)

(* ========================================================================= *)
(* THE KNUTH-BENDIX TERM ORDERING                                            *)
(* Copyright (c) 2002-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature KnuthBendixOrder =
sig

(* ------------------------------------------------------------------------- *)
(* The weight of all constants must be at least 1, and there must be at most *)
(* one unary function with weight 0.                                         *)
(* ------------------------------------------------------------------------- *)

type kbo =
     {weight : Metis.Term.function -> int,
      precedence : Metis.Term.function * Metis.Term.function -> order}

val default : kbo

val compare : kbo -> Metis.Term.term * Metis.Term.term -> order option

end

(**** Original file: KnuthBendixOrder.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* KNUTH-BENDIX TERM ORDERING CONSTRAINTS                                    *)
(* Copyright (c) 2002-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure KnuthBendixOrder :> KnuthBendixOrder =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun firstNotEqual f l =
    case List.find op<> l of
      SOME (x,y) => f x y
    | NONE => raise Bug "firstNotEqual";

(* ------------------------------------------------------------------------- *)
(* The weight of all constants must be at least 1, and there must be at most *)
(* one unary function with weight 0.                                         *)
(* ------------------------------------------------------------------------- *)

type kbo =
     {weight : Term.function -> int,
      precedence : Term.function * Term.function -> order};

(* Default weight = uniform *)

val uniformWeight : Term.function -> int = K 1;

(* Default precedence = by arity *)

val arityPrecedence : Term.function * Term.function -> order =
    fn ((f1,n1),(f2,n2)) =>
       case Int.compare (n1,n2) of
         LESS => LESS
       | EQUAL => String.compare (f1,f2)
       | GREATER => GREATER;

(* The default order *)

val default = {weight = uniformWeight, precedence = arityPrecedence};

(* ------------------------------------------------------------------------- *)
(* Term weight-1 represented as a linear function of the weight-1 of the     *)
(* variables in the term (plus a constant).                                  *)
(*                                                                           *)
(* Note that the conditions on weight functions ensure that all weights are  *)
(* at least 1, so all weight-1s are at least 0.                              *)
(* ------------------------------------------------------------------------- *)

datatype weight = Weight of int NameMap.map * int;

val weightEmpty : int NameMap.map = NameMap.new ();

val weightZero = Weight (weightEmpty,0);

fun weightIsZero (Weight (m,c)) = c = 0 andalso NameMap.null m;

fun weightNeg (Weight (m,c)) = Weight (NameMap.transform ~ m, ~c);

local
  fun add (n1,n2) =
      let
        val n = n1 + n2
      in
        if n = 0 then NONE else SOME n
      end;
in
  fun weightAdd (Weight (m1,c1)) (Weight (m2,c2)) =
      Weight (NameMap.union add m1 m2, c1 + c2);
end;

fun weightSubtract w1 w2 = weightAdd w1 (weightNeg w2);

fun weightMult 0 _ = weightZero
  | weightMult 1 w = w
  | weightMult k (Weight (m,c)) =
    let
      fun mult n = k * n
    in
      Weight (NameMap.transform mult m, k * c)
    end;

fun weightTerm weight =
    let
      fun wt m c [] = Weight (m,c)
        | wt m c (Term.Var v :: tms) =
          let
            val n = Option.getOpt (NameMap.peek m v, 0)
          in
            wt (NameMap.insert m (v, n + 1)) (c + 1) tms
          end
        | wt m c (Term.Fn (f,a) :: tms) =
          wt m (c + weight (f, length a)) (a @ tms)
    in
      fn tm => wt weightEmpty ~1 [tm]
    end;

fun weightIsVar v (Weight (m,c)) =
    c = 0 andalso NameMap.size m = 1 andalso NameMap.peek m v = SOME 1;

fun weightConst (Weight (_,c)) = c;

fun weightVars (Weight (m,_)) = 
    NameMap.foldl (fn (v,_,s) => NameSet.add s v) NameSet.empty m;

val weightsVars =
    List.foldl (fn (w,s) => NameSet.union (weightVars w) s) NameSet.empty;

fun weightVarList w = NameSet.toList (weightVars w);

fun weightNumVars (Weight (m,_)) = NameMap.size m;

fun weightNumVarsWithPositiveCoeff (Weight (m,_)) =
    NameMap.foldl (fn (_,n,z) => if n > 0 then z + 1 else z) 0 m;

fun weightCoeff var (Weight (m,_)) = Option.getOpt (NameMap.peek m var, 0);

fun weightCoeffs varList w = map (fn var => weightCoeff var w) varList;

fun weightCoeffSum (Weight (m,_)) = NameMap.foldl (fn (_,n,z) => n + z) 0 m;

fun weightLowerBound (w as Weight (m,c)) =
    if NameMap.exists (fn (_,n) => n < 0) m then NONE else SOME c;

fun weightNoLowerBound w = not (Option.isSome (weightLowerBound w));

fun weightAlwaysPositive w =
    case weightLowerBound w of NONE => false | SOME n => n > 0;

fun weightUpperBound (w as Weight (m,c)) =
    if NameMap.exists (fn (_,n) => n > 0) m then NONE else SOME c;

fun weightNoUpperBound w = not (Option.isSome (weightUpperBound w));

fun weightAlwaysNegative w =
    case weightUpperBound w of NONE => false | SOME n => n < 0;

fun weightGcd (w as Weight (m,c)) =
    NameMap.foldl (fn (_,i,k) => gcd i k) (Int.abs c) m;

fun ppWeightList pp =
    let
      fun coeffToString n =
          if n < 0 then "~" ^ coeffToString (~n)
          else if n = 1 then ""
          else Int.toString n

      fun pp_tm pp ("",n) = Parser.ppInt pp n
        | pp_tm pp (v,n) = Parser.ppString pp (coeffToString n ^ v)
    in
      fn [] => Parser.ppInt pp 0
       | tms => Parser.ppSequence " +" pp_tm pp tms
    end;

fun ppWeight pp (Weight (m,c)) =
    let
      val l = NameMap.toList m
      val l = if c = 0 then l else l @ [("",c)]
    in
      ppWeightList pp l
    end;

val weightToString = Parser.toString ppWeight;

(* ------------------------------------------------------------------------- *)
(* The Knuth-Bendix term order.                                              *)
(* ------------------------------------------------------------------------- *)

datatype kboOrder = Less | Equal | Greater | SignOf of weight;

fun kboOrder {weight,precedence} =
    let
      fun weightDifference tm1 tm2 =
          let
            val w1 = weightTerm weight tm1
            and w2 = weightTerm weight tm2
          in
            weightSubtract w2 w1
          end

      fun weightLess tm1 tm2 =
          let
            val w = weightDifference tm1 tm2
          in
            if weightIsZero w then precedenceLess tm1 tm2
            else weightDiffLess w tm1 tm2
          end

      and weightDiffLess w tm1 tm2 =
          case weightLowerBound w of
            NONE => false
          | SOME 0 => precedenceLess tm1 tm2
          | SOME n => n > 0

      and precedenceLess (Term.Fn (f1,a1)) (Term.Fn (f2,a2)) =
          (case precedence ((f1, length a1), (f2, length a2)) of
             LESS => true
           | EQUAL => firstNotEqual weightLess (zip a1 a2)
           | GREATER => false)
        | precedenceLess _ _ = false

      fun weightDiffGreater w tm1 tm2 = weightDiffLess (weightNeg w) tm2 tm1

      fun weightCmp tm1 tm2 =
          let
            val w = weightDifference tm1 tm2
          in
            if weightIsZero w then precedenceCmp tm1 tm2
            else if weightDiffLess w tm1 tm2 then Less
            else if weightDiffGreater w tm1 tm2 then Greater
            else SignOf w
          end

      and precedenceCmp (Term.Fn (f1,a1)) (Term.Fn (f2,a2)) =
          (case precedence ((f1, length a1), (f2, length a2)) of
             LESS => Less
           | EQUAL => firstNotEqual weightCmp (zip a1 a2)
           | GREATER => Greater)
        | precedenceCmp _ _ = raise Bug "kboOrder.precendenceCmp"
    in
      fn (tm1,tm2) => if tm1 = tm2 then Equal else weightCmp tm1 tm2
    end;

fun compare kbo tm1_tm2 =
    case kboOrder kbo tm1_tm2 of
      Less => SOME LESS
    | Equal => SOME EQUAL
    | Greater => SOME GREATER
    | SignOf _ => NONE;

(*TRACE7
val compare = fn kbo => fn (tm1,tm2) =>
    let
      val () = Parser.ppTrace Term.pp "KnuthBendixOrder.compare: tm1" tm1
      val () = Parser.ppTrace Term.pp "KnuthBendixOrder.compare: tm2" tm2
      val result = compare kbo (tm1,tm2)
      val () =
          case result of
            NONE => trace "KnuthBendixOrder.compare: result = Incomparable\n"
          | SOME x =>
            Parser.ppTrace Parser.ppOrder "KnuthBendixOrder.compare: result" x
    in
      result
    end;
*)

end
end;

(**** Original file: Rewrite.sig ****)

(* ========================================================================= *)
(* ORDERED REWRITING FOR FIRST ORDER TERMS                                   *)
(* Copyright (c) 2003-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Rewrite =
sig

(* ------------------------------------------------------------------------- *)
(* A type of rewrite systems.                                                *)
(* ------------------------------------------------------------------------- *)

datatype orient = LeftToRight | RightToLeft

type reductionOrder = Metis.Term.term * Metis.Term.term -> order option

type equationId = int

type equation = Metis.Rule.equation

type rewrite

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val new : reductionOrder -> rewrite

val peek : rewrite -> equationId -> (equation * orient option) option

val size : rewrite -> int

val equations : rewrite -> equation list

val toString : rewrite -> string

val pp : rewrite Metis.Parser.pp

(* ------------------------------------------------------------------------- *)
(* Add equations into the system.                                            *)
(* ------------------------------------------------------------------------- *)

val add : rewrite -> equationId * equation -> rewrite

val addList : rewrite -> (equationId * equation) list -> rewrite

(* ------------------------------------------------------------------------- *)
(* Rewriting (the order must be a refinement of the rewrite order).          *)
(* ------------------------------------------------------------------------- *)

val rewrConv : rewrite -> reductionOrder -> Metis.Rule.conv

val rewriteConv : rewrite -> reductionOrder -> Metis.Rule.conv

val rewriteLiteralsRule :
    rewrite -> reductionOrder -> Metis.LiteralSet.set -> Metis.Rule.rule

val rewriteRule : rewrite -> reductionOrder -> Metis.Rule.rule

val rewrIdConv : rewrite -> reductionOrder -> equationId -> Metis.Rule.conv

val rewriteIdConv : rewrite -> reductionOrder -> equationId -> Metis.Rule.conv

val rewriteIdLiteralsRule :
    rewrite -> reductionOrder -> equationId -> Metis.LiteralSet.set -> Metis.Rule.rule

val rewriteIdRule : rewrite -> reductionOrder -> equationId -> Metis.Rule.rule

(* ------------------------------------------------------------------------- *)
(* Inter-reduce the equations in the system.                                 *)
(* ------------------------------------------------------------------------- *)

val reduce' : rewrite -> rewrite * equationId list

val reduce : rewrite -> rewrite

val isReduced : rewrite -> bool

(* ------------------------------------------------------------------------- *)
(* Rewriting as a derived rule.                                              *)
(* ------------------------------------------------------------------------- *)

val rewrite : equation list -> Metis.Thm.thm -> Metis.Thm.thm

val orderedRewrite : reductionOrder -> equation list -> Metis.Thm.thm -> Metis.Thm.thm

end

(**** Original file: Rewrite.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* ORDERED REWRITING FOR FIRST ORDER TERMS                                   *)
(* Copyright (c) 2003-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Rewrite :> Rewrite =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* A type of rewrite systems.                                                *)
(* ------------------------------------------------------------------------- *)

datatype orient = LeftToRight | RightToLeft;

type reductionOrder = Term.term * Term.term -> order option;

type equationId = int;

type equation = Rule.equation;

datatype rewrite =
    Rewrite of
      {order : reductionOrder,
       known : (equation * orient option) IntMap.map,
       redexes : (equationId * orient) TermNet.termNet,
       subterms : (equationId * bool * Term.path) TermNet.termNet,
       waiting : IntSet.set};

fun updateWaiting rw waiting =
    let
      val Rewrite {order, known, redexes, subterms, waiting = _} = rw
    in
      Rewrite
        {order = order, known = known, redexes = redexes,
         subterms = subterms, waiting = waiting}
    end;

fun deleteWaiting (rw as Rewrite {waiting,...}) id =
    updateWaiting rw (IntSet.delete waiting id);

(* ------------------------------------------------------------------------- *)
(* Basic operations                                                          *)
(* ------------------------------------------------------------------------- *)

fun new order =
    Rewrite
      {order = order,
       known = IntMap.new (),
       redexes = TermNet.new {fifo = false},
       subterms = TermNet.new {fifo = false},
       waiting = IntSet.empty};

fun peek (Rewrite {known,...}) id = IntMap.peek known id;

fun size (Rewrite {known,...}) = IntMap.size known;

fun equations (Rewrite {known,...}) =
    IntMap.foldr (fn (_,(eqn,_),eqns) => eqn :: eqns) [] known;

val pp = Parser.ppMap equations (Parser.ppList Rule.ppEquation);

(*DEBUG
local
  fun orientOptionToString ort =
      case ort of
        SOME LeftToRight => "-->"
      | SOME RightToLeft => "<--"
      | NONE => "<->";

  open Parser;

  fun ppEq p ((x_y,_),ort) =
      ppBinop (" " ^ orientOptionToString ort) Term.pp Term.pp p x_y;

  fun ppField f ppA p a =
      (beginBlock p Inconsistent 2;
       addString p (f ^ " =");
       addBreak p (1,0);
       ppA p a;
       endBlock p);

  val ppKnown =
      ppField "known" (ppMap IntMap.toList (ppList (ppPair ppInt ppEq)));

  val ppRedexes =
      ppField
        "redexes"
        (TermNet.pp
           (ppPair ppInt (ppMap (orientOptionToString o SOME) ppString)));

  val ppSubterms =
      ppField
        "subterms"
        (TermNet.pp
           (ppMap
              (fn (i,l,p) => (i, (if l then 0 else 1) :: p))
              (ppPair ppInt Term.ppPath)));

  val ppWaiting = ppField "waiting" (ppMap (IntSet.toList) (ppList ppInt));
in
  fun pp p (Rewrite {known,redexes,subterms,waiting,...}) =
      (beginBlock p Inconsistent 2;
       addString p "Rewrite";
       addBreak p (1,0);
       beginBlock p Inconsistent 1;
       addString p "{";
       ppKnown p known;
(*TRACE5
       addString p ",";
       addBreak p (1,0);
       ppRedexes p redexes;
       addString p ",";
       addBreak p (1,0);
       ppSubterms p subterms;
       addString p ",";
       addBreak p (1,0);
       ppWaiting p waiting;
*)
       endBlock p;
       addString p "}";
       endBlock p);
end;
*)

val toString = Parser.toString pp;

(* ------------------------------------------------------------------------- *)
(* Debug functions.                                                          *)
(* ------------------------------------------------------------------------- *)

fun termReducible order known id =
    let
      fun eqnRed ((l,r),_) tm =
          case total (Subst.match Subst.empty l) tm of
            NONE => false
          | SOME sub =>
            order (tm, Subst.subst (Subst.normalize sub) r) = SOME GREATER
      
      fun knownRed tm (eqnId,(eqn,ort)) =
          eqnId <> id andalso
          ((ort <> SOME RightToLeft andalso eqnRed eqn tm) orelse
           (ort <> SOME LeftToRight andalso eqnRed (Rule.symEqn eqn) tm))

      fun termRed tm = IntMap.exists (knownRed tm) known orelse subtermRed tm
      and subtermRed (Term.Var _) = false
        | subtermRed (Term.Fn (_,tms)) = List.exists termRed tms
    in
      termRed
    end;

fun literalReducible order known id lit =
    List.exists (termReducible order known id) (Literal.arguments lit);

fun literalsReducible order known id lits =
    LiteralSet.exists (literalReducible order known id) lits;

fun thmReducible order known id th =
    literalsReducible order known id (Thm.clause th);

(* ------------------------------------------------------------------------- *)
(* Add equations into the system.                                            *)
(* ------------------------------------------------------------------------- *)

fun orderToOrient (SOME EQUAL) = raise Error "Rewrite.orient: reflexive"
  | orderToOrient (SOME GREATER) = SOME LeftToRight
  | orderToOrient (SOME LESS) = SOME RightToLeft
  | orderToOrient NONE = NONE;

local
  fun ins redexes redex id ort = TermNet.insert redexes (redex,(id,ort));
in
  fun addRedexes id (((l,r),_),ort) redexes =
      case ort of
        SOME LeftToRight => ins redexes l id LeftToRight
      | SOME RightToLeft => ins redexes r id RightToLeft
      | NONE => ins (ins redexes l id LeftToRight) r id RightToLeft;
end;

fun add (rw as Rewrite {known,...}) (id,eqn) =
    if IntMap.inDomain id known then rw
    else
      let
        val Rewrite {order,redexes,subterms,waiting, ...} = rw
        val ort = orderToOrient (order (fst eqn))
        val known = IntMap.insert known (id,(eqn,ort))
        val redexes = addRedexes id (eqn,ort) redexes
        val waiting = IntSet.add waiting id
        val rw =
            Rewrite
              {order = order, known = known, redexes = redexes,
               subterms = subterms, waiting = waiting}
(*TRACE5
        val () = Parser.ppTrace pp "Rewrite.add: result" rw
*)
      in
        rw
      end;

val addList = foldl (fn (eqn,rw) => add rw eqn);

(* ------------------------------------------------------------------------- *)
(* Rewriting (the order must be a refinement of the rewrite order).          *)
(* ------------------------------------------------------------------------- *)

local
  fun reorder ((i,_),(j,_)) = Int.compare (j,i);
in
  fun matchingRedexes redexes tm = sort reorder (TermNet.match redexes tm);
end;

fun wellOriented NONE _ = true
  | wellOriented (SOME LeftToRight) LeftToRight = true
  | wellOriented (SOME RightToLeft) RightToLeft = true
  | wellOriented _ _ = false;

fun redexResidue LeftToRight ((l_r,_) : equation) = l_r
  | redexResidue RightToLeft ((l,r),_) = (r,l);

fun orientedEquation LeftToRight eqn = eqn
  | orientedEquation RightToLeft eqn = Rule.symEqn eqn;

fun rewrIdConv' order known redexes id tm =
    let
      fun rewr (id',lr) =
          let
            val _ = id <> id' orelse raise Error "same theorem"
            val (eqn,ort) = IntMap.get known id'
            val _ = wellOriented ort lr orelse raise Error "orientation"
            val (l,r) = redexResidue lr eqn
            val sub = Subst.normalize (Subst.match Subst.empty l tm)
            val tm' = Subst.subst sub r
            val _ = Option.isSome ort orelse
                    order (tm,tm') = SOME GREATER orelse
                    raise Error "order"
            val (_,th) = orientedEquation lr eqn
          in
            (tm', Thm.subst sub th)
          end
    in
      case first (total rewr) (matchingRedexes redexes tm) of
        NONE => raise Error "Rewrite.rewrIdConv: no matching rewrites"
      | SOME res => res
    end;

fun rewriteIdConv' order known redexes id =
    if IntMap.null known then Rule.allConv
    else Rule.repeatTopDownConv (rewrIdConv' order known redexes id);

fun mkNeqConv order lit =
    let
      val (l,r) = Literal.destNeq lit
    in
      case order (l,r) of
        NONE => raise Error "incomparable"
      | SOME LESS =>
        let
          val sub = Subst.fromList [("x",l),("y",r)]
          val th = Thm.subst sub Rule.symmetry
        in
          fn tm => if tm = r then (l,th) else raise Error "mkNeqConv: RL"
        end
      | SOME EQUAL => raise Error "irreflexive"
      | SOME GREATER =>
        let
          val th = Thm.assume lit
        in
          fn tm => if tm = l then (r,th) else raise Error "mkNeqConv: LR"
        end
    end;

datatype neqConvs = NeqConvs of Rule.conv LiteralMap.map;

val neqConvsEmpty = NeqConvs (LiteralMap.new ());

fun neqConvsNull (NeqConvs m) = LiteralMap.null m;

fun neqConvsAdd order (neq as NeqConvs m) lit =
    case total (mkNeqConv order) lit of
      NONE => NONE
    | SOME conv => SOME (NeqConvs (LiteralMap.insert m (lit,conv)));

fun mkNeqConvs order =
    let
      fun add (lit,(neq,lits)) =
          case neqConvsAdd order neq lit of
            SOME neq => (neq,lits)
          | NONE => (neq, LiteralSet.add lits lit)
    in
      LiteralSet.foldl add (neqConvsEmpty,LiteralSet.empty)
    end;

fun neqConvsDelete (NeqConvs m) lit = NeqConvs (LiteralMap.delete m lit);

fun neqConvsToConv (NeqConvs m) =
    Rule.firstConv (LiteralMap.foldr (fn (_,c,l) => c :: l) [] m);

fun neqConvsFoldl f b (NeqConvs m) =
    LiteralMap.foldl (fn (l,_,z) => f (l,z)) b m;

fun neqConvsRewrIdLiterule order known redexes id neq =
    if IntMap.null known andalso neqConvsNull neq then Rule.allLiterule
    else
      let
        val neq_conv = neqConvsToConv neq
        val rewr_conv = rewrIdConv' order known redexes id
        val conv = Rule.orelseConv neq_conv rewr_conv
        val conv = Rule.repeatTopDownConv conv
      in
        Rule.allArgumentsLiterule conv
      end;

fun rewriteIdEqn' order known redexes id (eqn as (l_r,th)) =
    let
      val (neq,_) = mkNeqConvs order (Thm.clause th)
      val literule = neqConvsRewrIdLiterule order known redexes id neq
      val (strongEqn,lit) =
          case Rule.equationLiteral eqn of
            NONE => (true, Literal.mkEq l_r)
          | SOME lit => (false,lit)
      val (lit',litTh) = literule lit
    in
      if lit = lit' then eqn
      else
        (Literal.destEq lit',
         if strongEqn then th
         else if not (Thm.negateMember lit litTh) then litTh
         else Thm.resolve lit th litTh)
    end
(*DEBUG
    handle Error err => raise Error ("Rewrite.rewriteIdEqn':\n" ^ err);
*)

fun rewriteIdLiteralsRule' order known redexes id lits th =
    let
      val mk_literule = neqConvsRewrIdLiterule order known redexes id

      fun rewr_neq_lit (lit, acc as (changed,neq,lits,th)) =
          let
            val neq = neqConvsDelete neq lit
            val (lit',litTh) = mk_literule neq lit
          in
            if lit = lit' then acc
            else
              let
                val th = Thm.resolve lit th litTh
              in
                case neqConvsAdd order neq lit' of
                  SOME neq => (true,neq,lits,th)
                | NONE => (changed, neq, LiteralSet.add lits lit', th)
              end
          end

      fun rewr_neq_lits neq lits th =
          let
            val (changed,neq,lits,th) =
                neqConvsFoldl rewr_neq_lit (false,neq,lits,th) neq
          in
            if changed then rewr_neq_lits neq lits th
            else (neq,lits,th)
          end

      val (neq,lits) = mkNeqConvs order lits

      val (neq,lits,th) = rewr_neq_lits neq lits th

      val rewr_literule = mk_literule neq

      fun rewr_lit (lit,th) =
          if Thm.member lit th then Rule.literalRule rewr_literule lit th
          else th
    in
      LiteralSet.foldl rewr_lit th lits
    end;

fun rewriteIdRule' order known redexes id th =
    rewriteIdLiteralsRule' order known redexes id (Thm.clause th) th;

(*DEBUG
val rewriteIdRule' = fn order => fn known => fn redexes => fn id => fn th =>
    let
(*TRACE6
      val () = Parser.ppTrace Thm.pp "Rewrite.rewriteIdRule': th" th
*)
      val result = rewriteIdRule' order known redexes id th
(*TRACE6
      val () = Parser.ppTrace Thm.pp "Rewrite.rewriteIdRule': result" result
*)
      val _ = not (thmReducible order known id result) orelse
              raise Bug "rewriteIdRule: should be normalized"
    in
      result
    end
    handle Error err => raise Error ("Rewrite.rewriteIdRule:\n" ^ err);
*)

fun rewrIdConv (Rewrite {known,redexes,...}) order =
    rewrIdConv' order known redexes;

fun rewrConv rewrite order = rewrIdConv rewrite order ~1;

fun rewriteIdConv (Rewrite {known,redexes,...}) order =
    rewriteIdConv' order known redexes;

fun rewriteConv rewrite order = rewriteIdConv rewrite order ~1;

fun rewriteIdLiteralsRule (Rewrite {known,redexes,...}) order =
    rewriteIdLiteralsRule' order known redexes;

fun rewriteLiteralsRule rewrite order =
    rewriteIdLiteralsRule rewrite order ~1;

fun rewriteIdRule (Rewrite {known,redexes,...}) order =
    rewriteIdRule' order known redexes;

fun rewriteRule rewrite order = rewriteIdRule rewrite order ~1;

(* ------------------------------------------------------------------------- *)
(* Inter-reduce the equations in the system.                                 *)
(* ------------------------------------------------------------------------- *)

fun addSubterms id (((l,r),_) : equation) subterms =
    let
      fun addSubterm b ((path,tm),net) = TermNet.insert net (tm,(id,b,path))

      val subterms = foldl (addSubterm true) subterms (Term.subterms l)
      val subterms = foldl (addSubterm false) subterms (Term.subterms r)
    in
      subterms
    end;

fun sameRedexes NONE _ _ = false
  | sameRedexes (SOME LeftToRight) (l0,_) (l,_) = l0 = l
  | sameRedexes (SOME RightToLeft) (_,r0) (_,r) = r0 = r;

fun redexResidues NONE (l,r) = [(l,r,false),(r,l,false)]
  | redexResidues (SOME LeftToRight) (l,r) = [(l,r,true)]
  | redexResidues (SOME RightToLeft) (l,r) = [(r,l,true)];

fun findReducibles order known subterms id =
    let
      fun checkValidRewr (l,r,ord) id' left path =
          let
            val (((x,y),_),_) = IntMap.get known id'
            val tm = Term.subterm (if left then x else y) path
            val sub = Subst.match Subst.empty l tm
          in
            if ord then ()
            else
              let
                val tm' = Subst.subst (Subst.normalize sub) r
              in
                if order (tm,tm') = SOME GREATER then ()
                else raise Error "order"
              end
          end
            
      fun addRed lr ((id',left,path),todo) =
          if id <> id' andalso not (IntSet.member id' todo) andalso
             can (checkValidRewr lr id' left) path
          then IntSet.add todo id'
          else todo
               
      fun findRed (lr as (l,_,_), todo) =
          List.foldl (addRed lr) todo (TermNet.matched subterms l)
    in
      List.foldl findRed
    end;

fun reduce1 new id (eqn0,ort0) (rpl,spl,todo,rw,changed) =
    let
      val (eq0,_) = eqn0
      val Rewrite {order,known,redexes,subterms,waiting} = rw
      val eqn as (eq,_) = rewriteIdEqn' order known redexes id eqn0
      val identical = eq = eq0
      val same_redexes = identical orelse sameRedexes ort0 eq0 eq
      val rpl = if same_redexes then rpl else IntSet.add rpl id
      val spl = if new orelse identical then spl else IntSet.add spl id
      val changed =
          if not new andalso identical then changed else IntSet.add changed id
      val ort =
          if same_redexes then SOME ort0 else total orderToOrient (order eq)
    in
      case ort of
        NONE =>
        let
          val known = IntMap.delete known id
          val rw =
              Rewrite
                {order = order, known = known, redexes = redexes,
                 subterms = subterms, waiting = waiting}
        in
          (rpl,spl,todo,rw,changed)
        end
      | SOME ort =>
        let
          val todo =
              if not new andalso same_redexes then todo
              else
                findReducibles
                  order known subterms id todo (redexResidues ort eq)
          val known =
              if identical then known else IntMap.insert known (id,(eqn,ort))
          val redexes =
              if same_redexes then redexes
              else addRedexes id (eqn,ort) redexes
          val subterms =
              if new orelse not identical then addSubterms id eqn subterms
              else subterms
          val rw =
              Rewrite
                {order = order, known = known, redexes = redexes,
                 subterms = subterms, waiting = waiting}
        in
          (rpl,spl,todo,rw,changed)
        end
    end;

fun pick known set =
    let
      fun oriented id =
          case IntMap.peek known id of
            SOME (x as (_, SOME _)) => SOME (id,x)
          | _ => NONE

      fun any id =
          case IntMap.peek known id of SOME x => SOME (id,x) | _ => NONE
    in
      case IntSet.firstl oriented set of
        x as SOME _ => x
      | NONE => IntSet.firstl any set
    end;

local
  fun cleanRedexes known redexes rpl =
      if IntSet.null rpl then redexes
      else
        let
          fun filt (id,_) = not (IntSet.member id rpl)

          fun addReds (id,reds) =
              case IntMap.peek known id of
                NONE => reds
              | SOME eqn_ort => addRedexes id eqn_ort reds
                               
          val redexes = TermNet.filter filt redexes
          val redexes = IntSet.foldl addReds redexes rpl
        in
          redexes
        end;

  fun cleanSubterms known subterms spl =
      if IntSet.null spl then subterms
      else
        let
          fun filt (id,_,_) = not (IntSet.member id spl)

          fun addSubtms (id,subtms) =
              case IntMap.peek known id of
                NONE => subtms
              | SOME (eqn,_) => addSubterms id eqn subtms
                               
          val subterms = TermNet.filter filt subterms
          val subterms = IntSet.foldl addSubtms subterms spl
        in
          subterms
        end;
in
  fun rebuild rpl spl rw =
      let
(*TRACE5
        val ppPl = Parser.ppMap IntSet.toList (Parser.ppList Parser.ppInt)
        val () = Parser.ppTrace ppPl "Rewrite.rebuild: rpl" rpl
        val () = Parser.ppTrace ppPl "Rewrite.rebuild: spl" spl
*)
        val Rewrite {order,known,redexes,subterms,waiting} = rw
        val redexes = cleanRedexes known redexes rpl
        val subterms = cleanSubterms known subterms spl
      in
        Rewrite
          {order = order, known = known, redexes = redexes,
           subterms = subterms, waiting = waiting}
      end;
end;

fun reduceAcc (rpl, spl, todo, rw as Rewrite {known,waiting,...}, changed) =
    case pick known todo of
      SOME (id,eqn_ort) =>
      let
        val todo = IntSet.delete todo id
      in
        reduceAcc (reduce1 false id eqn_ort (rpl,spl,todo,rw,changed))
      end
    | NONE =>
      case pick known waiting of
        SOME (id,eqn_ort) =>
        let
          val rw = deleteWaiting rw id
        in
          reduceAcc (reduce1 true id eqn_ort (rpl,spl,todo,rw,changed))
        end
      | NONE => (rebuild rpl spl rw, IntSet.toList changed);

fun isReduced (Rewrite {waiting,...}) = IntSet.null waiting;

fun reduce' rw =
    if isReduced rw then (rw,[])
    else reduceAcc (IntSet.empty,IntSet.empty,IntSet.empty,rw,IntSet.empty);

(*DEBUG
val reduce' = fn rw =>
    let
(*TRACE4
      val () = Parser.ppTrace pp "Rewrite.reduce': rw" rw
*)
      val Rewrite {known,order,...} = rw
      val result as (Rewrite {known = known', ...}, _) = reduce' rw
(*TRACE4
      val ppResult = Parser.ppPair pp (Parser.ppList Parser.ppInt)
      val () = Parser.ppTrace ppResult "Rewrite.reduce': result" result
*)
      val ths = map (fn (id,((_,th),_)) => (id,th)) (IntMap.toList known')
      val _ =
          not (List.exists (uncurry (thmReducible order known')) ths) orelse
          raise Bug "Rewrite.reduce': not fully reduced"
    in
      result
    end
    handle Error err => raise Bug ("Rewrite.reduce': shouldn't fail\n" ^ err);
*)

fun reduce rw = fst (reduce' rw);

(* ------------------------------------------------------------------------- *)
(* Rewriting as a derived rule.                                              *)
(* ------------------------------------------------------------------------- *)

local
  fun addEqn (id_eqn,rw) = add rw id_eqn;
in
  fun orderedRewrite order ths =
    let
      val rw = foldl addEqn (new order) (enumerate ths)
    in
      rewriteRule rw order
    end;
end;

val rewrite = orderedRewrite (K (SOME GREATER));

end
end;

(**** Original file: Units.sig ****)

(* ========================================================================= *)
(* A STORE FOR UNIT THEOREMS                                                 *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Units =
sig

(* ------------------------------------------------------------------------- *)
(* A type of unit store.                                                     *)
(* ------------------------------------------------------------------------- *)

type unitThm = Metis.Literal.literal * Metis.Thm.thm

type units

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val empty : units

val size : units -> int

val toString : units -> string

val pp : units Metis.Parser.pp

(* ------------------------------------------------------------------------- *)
(* Add units into the store.                                                 *)
(* ------------------------------------------------------------------------- *)

val add : units -> unitThm -> units

val addList : units -> unitThm list -> units

(* ------------------------------------------------------------------------- *)
(* Matching.                                                                 *)
(* ------------------------------------------------------------------------- *)

val match : units -> Metis.Literal.literal -> (unitThm * Metis.Subst.subst) option

(* ------------------------------------------------------------------------- *)
(* Reducing by repeated matching and resolution.                             *)
(* ------------------------------------------------------------------------- *)

val reduce : units -> Metis.Rule.rule

end

(**** Original file: Units.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* A STORE FOR UNIT THEOREMS                                                 *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Units :> Units =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* A type of unit store.                                                     *)
(* ------------------------------------------------------------------------- *)

type unitThm = Literal.literal * Thm.thm;

datatype units = Units of unitThm LiteralNet.literalNet;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val empty = Units (LiteralNet.new {fifo = false});

fun size (Units net) = LiteralNet.size net;

fun toString units = "U{" ^ Int.toString (size units) ^ "}";

val pp = Parser.ppMap toString Parser.ppString;

(* ------------------------------------------------------------------------- *)
(* Add units into the store.                                                 *)
(* ------------------------------------------------------------------------- *)

fun add (units as Units net) (uTh as (lit,th)) =
    let
      val net = LiteralNet.insert net (lit,uTh)
    in
      case total Literal.sym lit of
        NONE => Units net
      | SOME (lit' as (pol,_)) =>
        let
          val th' = (if pol then Rule.symEq else Rule.symNeq) lit th
          val net = LiteralNet.insert net (lit',(lit',th'))
        in
          Units net
        end
    end;

val addList = foldl (fn (th,u) => add u th);

(* ------------------------------------------------------------------------- *)
(* Matching.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun match (Units net) lit =
    let
      fun check (uTh as (lit',_)) =
          case total (Literal.match Subst.empty lit') lit of
            NONE => NONE
          | SOME sub => SOME (uTh,sub)
    in
      first check (LiteralNet.match net lit)
    end;

(* ------------------------------------------------------------------------- *)
(* Reducing by repeated matching and resolution.                             *)
(* ------------------------------------------------------------------------- *)

fun reduce units =
    let
      fun red1 (lit,news_th) =
          case total Literal.destIrrefl lit of
            SOME tm =>
            let
              val (news,th) = news_th
              val th = Thm.resolve lit th (Thm.refl tm)
            in
              (news,th)
            end
          | NONE =>
            let
              val lit' = Literal.negate lit
            in
              case match units lit' of
                NONE => news_th
              | SOME ((_,rth),sub) =>
                let
                  val (news,th) = news_th
                  val rth = Thm.subst sub rth
                  val th = Thm.resolve lit th rth
                  val new = LiteralSet.delete (Thm.clause rth) lit'
                  val news = LiteralSet.union new news
                in
                  (news,th)
                end
            end

      fun red (news,th) =
          if LiteralSet.null news then th
          else red (LiteralSet.foldl red1 (LiteralSet.empty,th) news)
    in
      fn th => Rule.removeSym (red (Thm.clause th, th))
    end;

end
end;

(**** Original file: Clause.sig ****)

(* ========================================================================= *)
(* CLAUSE = ID + THEOREM                                                     *)
(* Copyright (c) 2002-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Clause =
sig

(* ------------------------------------------------------------------------- *)
(* A type of clause.                                                         *)
(* ------------------------------------------------------------------------- *)

datatype literalOrder =
    NoLiteralOrder
  | UnsignedLiteralOrder
  | PositiveLiteralOrder

type parameters =
     {ordering : Metis.KnuthBendixOrder.kbo,
      orderLiterals : literalOrder,
      orderTerms : bool}

type clauseId = int

type clauseInfo = {parameters : parameters, id : clauseId, thm : Metis.Thm.thm}

type clause

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val default : parameters

val newId : unit -> clauseId

val mk : clauseInfo -> clause

val dest : clause -> clauseInfo

val id : clause -> clauseId

val thm : clause -> Metis.Thm.thm

val equalThms : clause -> clause -> bool

val literals : clause -> Metis.Thm.clause

val isTautology : clause -> bool

val isContradiction : clause -> bool

(* ------------------------------------------------------------------------- *)
(* The term ordering is used to cut down inferences.                         *)
(* ------------------------------------------------------------------------- *)

val largestLiterals : clause -> Metis.LiteralSet.set

val largestEquations :
    clause -> (Metis.Literal.literal * Metis.Rewrite.orient * Metis.Term.term) list

val largestSubterms :
    clause -> (Metis.Literal.literal * Metis.Term.path * Metis.Term.term) list

val allSubterms : clause -> (Metis.Literal.literal * Metis.Term.path * Metis.Term.term) list

(* ------------------------------------------------------------------------- *)
(* Subsumption.                                                              *)
(* ------------------------------------------------------------------------- *)

val subsumes : clause Metis.Subsume.subsume -> clause -> bool

(* ------------------------------------------------------------------------- *)
(* Simplifying rules: these preserve the clause id.                          *)
(* ------------------------------------------------------------------------- *)

val freshVars : clause -> clause

val simplify : clause -> clause option

val reduce : Metis.Units.units -> clause -> clause

val rewrite : Metis.Rewrite.rewrite -> clause -> clause

(* ------------------------------------------------------------------------- *)
(* Inference rules: these generate new clause ids.                           *)
(* ------------------------------------------------------------------------- *)

val factor : clause -> clause list

val resolve : clause * Metis.Literal.literal -> clause * Metis.Literal.literal -> clause

val paramodulate :
    clause * Metis.Literal.literal * Metis.Rewrite.orient * Metis.Term.term ->
    clause * Metis.Literal.literal * Metis.Term.path * Metis.Term.term -> clause

(* ------------------------------------------------------------------------- *)
(* Pretty printing.                                                          *)
(* ------------------------------------------------------------------------- *)

val showId : bool Unsynchronized.ref

val pp : clause Metis.Parser.pp

end

(**** Original file: Clause.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* CLAUSE = ID + THEOREM                                                     *)
(* Copyright (c) 2002-2004 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Clause :> Clause =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

val newId =
    let
      val r = Unsynchronized.ref 0
    in
      fn () => CRITICAL (fn () =>
        case r of Unsynchronized.ref n => let val () = r := n + 1 in n end)
    end;

(* ------------------------------------------------------------------------- *)
(* A type of clause.                                                         *)
(* ------------------------------------------------------------------------- *)

datatype literalOrder =
    NoLiteralOrder
  | UnsignedLiteralOrder
  | PositiveLiteralOrder;

type parameters =
     {ordering : KnuthBendixOrder.kbo,
      orderLiterals : literalOrder,
      orderTerms : bool};

type clauseId = int;

type clauseInfo = {parameters : parameters, id : clauseId, thm : Thm.thm};

datatype clause = Clause of clauseInfo;

(* ------------------------------------------------------------------------- *)
(* Pretty printing.                                                          *)
(* ------------------------------------------------------------------------- *)

val showId = Unsynchronized.ref false;

local
  val ppIdThm = Parser.ppPair Parser.ppInt Thm.pp;
in
  fun pp p (Clause {id,thm,...}) =
      if !showId then ppIdThm p (id,thm) else Thm.pp p thm;
end;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val default : parameters = 
    {ordering = KnuthBendixOrder.default,
     orderLiterals = UnsignedLiteralOrder, (*LCP: changed from PositiveLiteralOrder*)
     orderTerms = true};

fun mk info = Clause info

fun dest (Clause info) = info;

fun id (Clause {id = i, ...}) = i;

fun thm (Clause {thm = th, ...}) = th;

fun equalThms cl cl' = Thm.equal (thm cl) (thm cl');

fun new parameters thm =
    Clause {parameters = parameters, id = newId (), thm = thm};

fun literals cl = Thm.clause (thm cl);

fun isTautology (Clause {thm,...}) = Thm.isTautology thm;

fun isContradiction (Clause {thm,...}) = Thm.isContradiction thm;

(* ------------------------------------------------------------------------- *)
(* The term ordering is used to cut down inferences.                         *)
(* ------------------------------------------------------------------------- *)

fun strictlyLess ordering x_y =
    case KnuthBendixOrder.compare ordering x_y of
      SOME LESS => true
    | _ => false;

fun isLargerTerm ({ordering,orderTerms,...} : parameters) l_r =
    not orderTerms orelse not (strictlyLess ordering l_r);

local
  fun atomToTerms atm =
      case total Atom.destEq atm of
        NONE => [Term.Fn atm]
      | SOME (l,r) => [l,r];

  fun notStrictlyLess ordering (xs,ys) =
      let
        fun less x = List.exists (fn y => strictlyLess ordering (x,y)) ys
      in
        not (List.all less xs)
      end;
in
  fun isLargerLiteral ({ordering,orderLiterals,...} : parameters) lits =
      case orderLiterals of
        NoLiteralOrder => K true
      | UnsignedLiteralOrder =>
        let
          fun addLit ((_,atm),acc) = atomToTerms atm @ acc

          val tms = LiteralSet.foldl addLit [] lits
        in
          fn (_,atm') => notStrictlyLess ordering (atomToTerms atm', tms)
        end
      | PositiveLiteralOrder =>
        case LiteralSet.findl (K true) lits of
          NONE => K true
        | SOME (pol,_) =>
          let
            fun addLit ((p,atm),acc) =
                if p = pol then atomToTerms atm @ acc else acc

            val tms = LiteralSet.foldl addLit [] lits
          in
            fn (pol',atm') =>
               if pol <> pol' then pol
               else notStrictlyLess ordering (atomToTerms atm', tms)
          end;
end;

fun largestLiterals (Clause {parameters,thm,...}) =
    let
      val litSet = Thm.clause thm
      val isLarger = isLargerLiteral parameters litSet
      fun addLit (lit,s) = if isLarger lit then LiteralSet.add s lit else s
    in
      LiteralSet.foldr addLit LiteralSet.empty litSet
    end;

(*TRACE6
val largestLiterals = fn cl =>
    let
      val ppResult = LiteralSet.pp
      val () = Parser.ppTrace pp "Clause.largestLiterals: cl" cl
      val result = largestLiterals cl
      val () = Parser.ppTrace ppResult "Clause.largestLiterals: result" result
    in
      result
    end;
*)

fun largestEquations (cl as Clause {parameters,...}) =
    let
      fun addEq lit ort (l_r as (l,_)) acc =
          if isLargerTerm parameters l_r then (lit,ort,l) :: acc else acc

      fun addLit (lit,acc) =
          case total Literal.destEq lit of
            NONE => acc
          | SOME (l,r) =>
            let
              val acc = addEq lit Rewrite.RightToLeft (r,l) acc
              val acc = addEq lit Rewrite.LeftToRight (l,r) acc
            in
              acc
            end
    in
      LiteralSet.foldr addLit [] (largestLiterals cl)
    end;

local
  fun addLit (lit,acc) =
      let
        fun addTm ((path,tm),acc) = (lit,path,tm) :: acc
      in
        foldl addTm acc (Literal.nonVarTypedSubterms lit)
      end;
in
  fun largestSubterms cl = LiteralSet.foldl addLit [] (largestLiterals cl);

  fun allSubterms cl = LiteralSet.foldl addLit [] (literals cl);
end;

(* ------------------------------------------------------------------------- *)
(* Subsumption.                                                              *)
(* ------------------------------------------------------------------------- *)

fun subsumes (subs : clause Subsume.subsume) cl =
    Subsume.isStrictlySubsumed subs (literals cl);

(* ------------------------------------------------------------------------- *)
(* Simplifying rules: these preserve the clause id.                          *)
(* ------------------------------------------------------------------------- *)

fun freshVars (Clause {parameters,id,thm}) =
    Clause {parameters = parameters, id = id, thm = Rule.freshVars thm};

fun simplify (Clause {parameters,id,thm}) =
    case Rule.simplify thm of
      NONE => NONE
    | SOME thm => SOME (Clause {parameters = parameters, id = id, thm = thm});

fun reduce units (Clause {parameters,id,thm}) =
    Clause {parameters = parameters, id = id, thm = Units.reduce units thm};

fun rewrite rewr (cl as Clause {parameters,id,thm}) =
    let
      fun simp th =
          let
            val {ordering,...} = parameters
            val cmp = KnuthBendixOrder.compare ordering
          in
            Rewrite.rewriteIdRule rewr cmp id th
          end

(*TRACE4
      val () = Parser.ppTrace Rewrite.pp "Clause.rewrite: rewr" rewr
      val () = Parser.ppTrace Parser.ppInt "Clause.rewrite: id" id
      val () = Parser.ppTrace pp "Clause.rewrite: cl" cl
*)

      val thm =
          case Rewrite.peek rewr id of
            NONE => simp thm
          | SOME ((_,thm),_) => if Rewrite.isReduced rewr then thm else simp thm

      val result = Clause {parameters = parameters, id = id, thm = thm}

(*TRACE4
      val () = Parser.ppTrace pp "Clause.rewrite: result" result
*)
    in
      result
    end
(*DEBUG
    handle Error err => raise Error ("Clause.rewrite:\n" ^ err);
*)

(* ------------------------------------------------------------------------- *)
(* Inference rules: these generate new clause ids.                           *)
(* ------------------------------------------------------------------------- *)

fun factor (cl as Clause {parameters,thm,...}) =
    let
      val lits = largestLiterals cl

      fun apply sub = new parameters (Thm.subst sub thm)
    in
      map apply (Rule.factor' lits)
    end;

(*TRACE5
val factor = fn cl =>
    let
      val () = Parser.ppTrace pp "Clause.factor: cl" cl
      val result = factor cl
      val () = Parser.ppTrace (Parser.ppList pp) "Clause.factor: result" result
    in
      result
    end;
*)

fun resolve (cl1,lit1) (cl2,lit2) =
    let
(*TRACE5
      val () = Parser.ppTrace pp "Clause.resolve: cl1" cl1
      val () = Parser.ppTrace Literal.pp "Clause.resolve: lit1" lit1
      val () = Parser.ppTrace pp "Clause.resolve: cl2" cl2
      val () = Parser.ppTrace Literal.pp "Clause.resolve: lit2" lit2
*)
      val Clause {parameters, thm = th1, ...} = cl1
      and Clause {thm = th2, ...} = cl2
      val sub = Literal.unify Subst.empty lit1 (Literal.negate lit2)
(*TRACE5
      val () = Parser.ppTrace Subst.pp "Clause.resolve: sub" sub
*)
      val lit1 = Literal.subst sub lit1
      val lit2 = Literal.negate lit1
      val th1 = Thm.subst sub th1
      and th2 = Thm.subst sub th2
      val _ = isLargerLiteral parameters (Thm.clause th1) lit1 orelse
(*TRACE5
              (trace "Clause.resolve: th1 violates ordering\n"; false) orelse
*)
              raise Error "resolve: clause1: ordering constraints"
      val _ = isLargerLiteral parameters (Thm.clause th2) lit2 orelse
(*TRACE5
              (trace "Clause.resolve: th2 violates ordering\n"; false) orelse
*)
              raise Error "resolve: clause2: ordering constraints"
      val th = Thm.resolve lit1 th1 th2
(*TRACE5
      val () = Parser.ppTrace Thm.pp "Clause.resolve: th" th
*)
      val cl = Clause {parameters = parameters, id = newId (), thm = th}
(*TRACE5
      val () = Parser.ppTrace pp "Clause.resolve: cl" cl
*)
    in
      cl
    end;

fun paramodulate (cl1,lit1,ort,tm1) (cl2,lit2,path,tm2) =
    let
(*TRACE5
      val () = Parser.ppTrace pp "Clause.paramodulate: cl1" cl1
      val () = Parser.ppTrace Literal.pp "Clause.paramodulate: lit1" lit1
      val () = Parser.ppTrace pp "Clause.paramodulate: cl2" cl2
      val () = Parser.ppTrace Literal.pp "Clause.paramodulate: lit2" lit2
*)
      val Clause {parameters, thm = th1, ...} = cl1
      and Clause {thm = th2, ...} = cl2
      val sub = Subst.unify Subst.empty tm1 tm2
      val lit1 = Literal.subst sub lit1
      and lit2 = Literal.subst sub lit2
      and th1 = Thm.subst sub th1
      and th2 = Thm.subst sub th2
      val _ = isLargerLiteral parameters (Thm.clause th1) lit1 orelse
(*TRACE5
              (trace "Clause.paramodulate: cl1 ordering\n"; false) orelse
*)
              raise Error "paramodulate: with clause: ordering constraints"
      val _ = isLargerLiteral parameters (Thm.clause th2) lit2 orelse
(*TRACE5
              (trace "Clause.paramodulate: cl2 ordering\n"; false) orelse
*)
              raise Error "paramodulate: into clause: ordering constraints"
      val eqn = (Literal.destEq lit1, th1)
      val eqn as (l_r,_) =
          case ort of
            Rewrite.LeftToRight => eqn
          | Rewrite.RightToLeft => Rule.symEqn eqn
      val _ = isLargerTerm parameters l_r orelse
(*TRACE5
              (trace "Clause.paramodulate: eqn ordering\n"; false) orelse
*)
              raise Error "paramodulate: equation: ordering constraints"
      val th = Rule.rewrRule eqn lit2 path th2
(*TRACE5
      val () = Parser.ppTrace Thm.pp "Clause.paramodulate: th" th
*)
    in
      Clause {parameters = parameters, id = newId (), thm = th}
    end;

end
end;

(**** Original file: Active.sig ****)

(* ========================================================================= *)
(* THE ACTIVE SET OF CLAUSES                                                 *)
(* Copyright (c) 2002-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Active =
sig

(* ------------------------------------------------------------------------- *)
(* A type of active clause sets.                                             *)
(* ------------------------------------------------------------------------- *)

type simplify = {subsume : bool, reduce : bool, rewrite : bool}

type parameters =
     {clause : Metis.Clause.parameters,
      prefactor : simplify,
      postfactor : simplify}

type active

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val default : parameters

val size : active -> int

val saturated : active -> Metis.Clause.clause list

(* ------------------------------------------------------------------------- *)
(* Create a new active clause set and initialize clauses.                    *)
(* ------------------------------------------------------------------------- *)

val new : parameters -> Metis.Thm.thm list -> active * Metis.Clause.clause list

(* ------------------------------------------------------------------------- *)
(* Add a clause into the active set and deduce all consequences.             *)
(* ------------------------------------------------------------------------- *)

val add : active -> Metis.Clause.clause -> active * Metis.Clause.clause list

(* ------------------------------------------------------------------------- *)
(* Pretty printing.                                                          *)
(* ------------------------------------------------------------------------- *)

val pp : active Metis.Parser.pp

end

(**** Original file: Active.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* THE ACTIVE SET OF CLAUSES                                                 *)
(* Copyright (c) 2002-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Active :> Active =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

local
  fun allFactors red =
      let
        fun allClause cl = List.all red (cl :: Clause.factor cl)
      in
        List.all allClause
      end;

  fun allResolutions red =
      let
        fun allClause2 cl_lit cl =
            let
              fun allLiteral2 lit =
                  case total (Clause.resolve cl_lit) (cl,lit) of
                    NONE => true
                  | SOME cl => allFactors red [cl]
            in
              LiteralSet.all allLiteral2 (Clause.literals cl)
            end

        fun allClause1 allCls cl =
            let
              val cl = Clause.freshVars cl

              fun allLiteral1 lit = List.all (allClause2 (cl,lit)) allCls
            in
              LiteralSet.all allLiteral1 (Clause.literals cl)
            end
      in
        fn [] => true
         | allCls as cl :: cls =>
           allClause1 allCls cl andalso allResolutions red cls
      end;

  fun allParamodulations red cls =
      let
        fun allClause2 cl_lit_ort_tm cl =
            let
              fun allLiteral2 lit =
                  let
                    val para = Clause.paramodulate cl_lit_ort_tm

                    fun allSubterms (path,tm) =
                        case total para (cl,lit,path,tm) of
                          NONE => true
                        | SOME cl => allFactors red [cl]
                  in
                    List.all allSubterms (Literal.nonVarTypedSubterms lit)
                  end
            in
              LiteralSet.all allLiteral2 (Clause.literals cl)
            end

        fun allClause1 cl =
            let
              val cl = Clause.freshVars cl

              fun allLiteral1 lit =
                  let
                    fun allCl2 x = List.all (allClause2 x) cls
                  in
                    case total Literal.destEq lit of
                      NONE => true
                    | SOME (l,r) =>
                      allCl2 (cl,lit,Rewrite.LeftToRight,l) andalso
                      allCl2 (cl,lit,Rewrite.RightToLeft,r)
                  end
            in
              LiteralSet.all allLiteral1 (Clause.literals cl)
            end
      in
        List.all allClause1 cls
      end;

  fun redundant {subsume,reduce,rewrite} =
      let
        fun simp cl =
            case Clause.simplify cl of
              NONE => true
            | SOME cl =>
              Subsume.isStrictlySubsumed subsume (Clause.literals cl) orelse
              let
                val cl' = cl
                val cl' = Clause.reduce reduce cl'
                val cl' = Clause.rewrite rewrite cl'
              in
                not (Clause.equalThms cl cl') andalso simp cl'
              end
      in
        simp
      end;
in
  fun isSaturated ordering subs cls =
      let
(*TRACE2
        val ppCls = Parser.ppList Clause.pp
        val () = Parser.ppTrace ppCls "Active.checkSaturated: clauses" cls
*)
        val red = Units.empty
        val rw = Rewrite.new (KnuthBendixOrder.compare ordering)
        val red = redundant {subsume = subs, reduce = red, rewrite = rw}
      in
        allFactors red cls andalso
        allResolutions red cls andalso
        allParamodulations red cls
      end;

  fun checkSaturated ordering subs cls =
      if isSaturated ordering subs cls then () else raise Bug "unsaturated";
end;

(* ------------------------------------------------------------------------- *)
(* A type of active clause sets.                                             *)
(* ------------------------------------------------------------------------- *)

type simplify = {subsume : bool, reduce : bool, rewrite : bool};

type parameters =
     {clause : Clause.parameters,
      prefactor : simplify,
      postfactor : simplify};

datatype active =
    Active of
      {parameters : parameters,
       clauses : Clause.clause IntMap.map,
       units : Units.units,
       rewrite : Rewrite.rewrite,
       subsume : Clause.clause Subsume.subsume,
       literals : (Clause.clause * Literal.literal) LiteralNet.literalNet,
       equations :
         (Clause.clause * Literal.literal * Rewrite.orient * Term.term)
         TermNet.termNet,
       subterms :
         (Clause.clause * Literal.literal * Term.path * Term.term)
         TermNet.termNet,
       allSubterms : (Clause.clause * Term.term) TermNet.termNet};

fun getSubsume (Active {subsume = s, ...}) = s;

fun setRewrite active rewrite =
    let
      val Active
            {parameters,clauses,units,subsume,literals,equations,
             subterms,allSubterms,...} = active
    in
      Active
        {parameters = parameters, clauses = clauses, units = units,
         rewrite = rewrite, subsume = subsume, literals = literals,
         equations = equations, subterms = subterms, allSubterms = allSubterms}
    end;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val maxSimplify : simplify = {subsume = true, reduce = true, rewrite = true};

val default : parameters =
    {clause = Clause.default,
     prefactor = maxSimplify,
     postfactor = maxSimplify};

fun empty parameters =
    let
      val {clause,...} = parameters
      val {ordering,...} = clause
    in
      Active
        {parameters = parameters,
         clauses = IntMap.new (),
         units = Units.empty,
         rewrite = Rewrite.new (KnuthBendixOrder.compare ordering),
         subsume = Subsume.new (),
         literals = LiteralNet.new {fifo = false},
         equations = TermNet.new {fifo = false},
         subterms = TermNet.new {fifo = false},
         allSubterms = TermNet.new {fifo = false}}
    end;

fun size (Active {clauses,...}) = IntMap.size clauses;

fun clauses (Active {clauses = cls, ...}) =
    let
      fun add (_,cl,acc) = cl :: acc
    in
      IntMap.foldr add [] cls
    end;

fun saturated active =
    let
      fun remove (cl,(cls,subs)) =
          let
            val lits = Clause.literals cl
          in
            if Subsume.isStrictlySubsumed subs lits then (cls,subs)
            else (cl :: cls, Subsume.insert subs (lits,()))
          end

      val cls = clauses active
      val (cls,_) = foldl remove ([], Subsume.new ()) cls
      val (cls,subs) = foldl remove ([], Subsume.new ()) cls

(*DEBUG
      val Active {parameters,...} = active
      val {clause,...} = parameters
      val {ordering,...} = clause
      val () = checkSaturated ordering subs cls
*)
    in
      cls
    end;

(* ------------------------------------------------------------------------- *)
(* Pretty printing.                                                          *)
(* ------------------------------------------------------------------------- *)

val pp =
    let
      fun toStr active = "Active{" ^ Int.toString (size active) ^ "}"
    in
      Parser.ppMap toStr Parser.ppString
    end;

(*DEBUG
local
  open Parser;

  fun ppField f ppA p a =
      (beginBlock p Inconsistent 2;
       addString p (f ^ " =");
       addBreak p (1,0);
       ppA p a;
       endBlock p);

  val ppClauses =
      ppField "clauses"
        (Parser.ppMap IntMap.toList
           (Parser.ppList (Parser.ppPair Parser.ppInt Clause.pp)));

  val ppRewrite = ppField "rewrite" Rewrite.pp;

  val ppSubterms =
      ppField "subterms"
        (TermNet.pp
           (Parser.ppMap (fn (c,l,p,t) => ((Clause.id c, l, p), t))
              (Parser.ppPair
                 (Parser.ppTriple Parser.ppInt Literal.pp Term.ppPath)
                 Term.pp)));
in
  fun pp p (Active {clauses,rewrite,subterms,...}) =
      (beginBlock p Inconsistent 2;
       addString p "Active";
       addBreak p (1,0);
       beginBlock p Inconsistent 1;
       addString p "{";
       ppClauses p clauses;
       addString p ",";
       addBreak p (1,0);
       ppRewrite p rewrite;
(*TRACE5
       addString p ",";
       addBreak p (1,0);
       ppSubterms p subterms;
*)
       endBlock p;
       addString p "}";
       endBlock p);
end;
*)

val toString = Parser.toString pp;

(* ------------------------------------------------------------------------- *)
(* Simplify clauses.                                                         *)
(* ------------------------------------------------------------------------- *)

fun simplify simp units rewr subs =
    let
      val {subsume = s, reduce = r, rewrite = w} = simp

      fun rewrite cl =
          let
            val cl' = Clause.rewrite rewr cl
          in
            if Clause.equalThms cl cl' then SOME cl else Clause.simplify cl'
          end
    in
      fn cl =>
         case Clause.simplify cl of
           NONE => NONE
         | SOME cl =>
           case (if w then rewrite cl else SOME cl) of
             NONE => NONE
           | SOME cl =>
             let
               val cl = if r then Clause.reduce units cl else cl
             in
               if s andalso Clause.subsumes subs cl then NONE else SOME cl
             end
    end;

(*DEBUG
val simplify = fn simp => fn units => fn rewr => fn subs => fn cl =>
    let
      fun traceCl s = Parser.ppTrace Clause.pp ("Active.simplify: " ^ s)
(*TRACE4
      val ppClOpt = Parser.ppOption Clause.pp
      val () = traceCl "cl" cl
*)
      val cl' = simplify simp units rewr subs cl
(*TRACE4
      val () = Parser.ppTrace ppClOpt "Active.simplify: cl'" cl'
*)
      val () =
          case cl' of
            NONE => ()
          | SOME cl' =>
            case
              (case simplify simp units rewr subs cl' of
                 NONE => SOME ("away", K ())
               | SOME cl'' =>
                 if Clause.equalThms cl' cl'' then NONE
                 else SOME ("further", fn () => traceCl "cl''" cl'')) of
              NONE => ()
            | SOME (e,f) =>
              let
                val () = traceCl "cl" cl
                val () = traceCl "cl'" cl'
                val () = f ()
              in
                raise
                  Bug
                    ("Active.simplify: clause should have been simplified "^e)
              end
    in
      cl'
    end;
*)

fun simplifyActive simp active =
    let
      val Active {units,rewrite,subsume,...} = active
    in
      simplify simp units rewrite subsume
    end;

(* ------------------------------------------------------------------------- *)
(* Add a clause into the active set.                                         *)
(* ------------------------------------------------------------------------- *)

fun addUnit units cl =
    let
      val th = Clause.thm cl
    in
      case total Thm.destUnit th of
        SOME lit => Units.add units (lit,th)
      | NONE => units
    end;

fun addRewrite rewrite cl =
    let
      val th = Clause.thm cl
    in
      case total Thm.destUnitEq th of
        SOME l_r => Rewrite.add rewrite (Clause.id cl, (l_r,th))
      | NONE => rewrite
    end;

fun addSubsume subsume cl = Subsume.insert subsume (Clause.literals cl, cl);

fun addLiterals literals cl =
    let
      fun add (lit as (_,atm), literals) =
          if Atom.isEq atm then literals
          else LiteralNet.insert literals (lit,(cl,lit))
    in
      LiteralSet.foldl add literals (Clause.largestLiterals cl)
    end;

fun addEquations equations cl =
    let
      fun add ((lit,ort,tm),equations) =
          TermNet.insert equations (tm,(cl,lit,ort,tm))
    in
      foldl add equations (Clause.largestEquations cl)
    end;

fun addSubterms subterms cl =
    let
      fun add ((lit,path,tm),subterms) =
          TermNet.insert subterms (tm,(cl,lit,path,tm))
    in
      foldl add subterms (Clause.largestSubterms cl)
    end;

fun addAllSubterms allSubterms cl =
    let
      fun add ((_,_,tm),allSubterms) =
          TermNet.insert allSubterms (tm,(cl,tm))
    in
      foldl add allSubterms (Clause.allSubterms cl)
    end;

fun addClause active cl =
    let
      val Active
            {parameters,clauses,units,rewrite,subsume,literals,
             equations,subterms,allSubterms} = active
      val clauses = IntMap.insert clauses (Clause.id cl, cl)
      and subsume = addSubsume subsume cl
      and literals = addLiterals literals cl
      and equations = addEquations equations cl
      and subterms = addSubterms subterms cl
      and allSubterms = addAllSubterms allSubterms cl
    in
      Active
        {parameters = parameters, clauses = clauses, units = units,
         rewrite = rewrite, subsume = subsume, literals = literals,
         equations = equations, subterms = subterms,
         allSubterms = allSubterms}
    end;

fun addFactorClause active cl =
    let
      val Active
            {parameters,clauses,units,rewrite,subsume,literals,
             equations,subterms,allSubterms} = active
      val units = addUnit units cl
      and rewrite = addRewrite rewrite cl
    in
      Active
        {parameters = parameters, clauses = clauses, units = units,
         rewrite = rewrite, subsume = subsume, literals = literals,
         equations = equations, subterms = subterms, allSubterms = allSubterms}
    end;

(* ------------------------------------------------------------------------- *)
(* Derive (unfactored) consequences of a clause.                             *)
(* ------------------------------------------------------------------------- *)

fun deduceResolution literals cl (lit as (_,atm), acc) =
    let
      fun resolve (cl_lit,acc) =
          case total (Clause.resolve cl_lit) (cl,lit) of
            SOME cl' => cl' :: acc
          | NONE => acc
(*TRACE4
      val () = Parser.ppTrace Literal.pp "Active.deduceResolution: lit" lit
*)
    in
      if Atom.isEq atm then acc
      else foldl resolve acc (LiteralNet.unify literals (Literal.negate lit))
    end;

fun deduceParamodulationWith subterms cl ((lit,ort,tm),acc) =
    let
      fun para (cl_lit_path_tm,acc) =
          case total (Clause.paramodulate (cl,lit,ort,tm)) cl_lit_path_tm of
            SOME cl' => cl' :: acc
          | NONE => acc
    in
      foldl para acc (TermNet.unify subterms tm)
    end;

fun deduceParamodulationInto equations cl ((lit,path,tm),acc) =
    let
      fun para (cl_lit_ort_tm,acc) =
          case total (Clause.paramodulate cl_lit_ort_tm) (cl,lit,path,tm) of
            SOME cl' => cl' :: acc
          | NONE => acc
    in
      foldl para acc (TermNet.unify equations tm)
    end;

fun deduce active cl =
    let
      val Active {parameters,literals,equations,subterms,...} = active

      val lits = Clause.largestLiterals cl
      val eqns = Clause.largestEquations cl
      val subtms =
          if TermNet.null equations then [] else Clause.largestSubterms cl

      val acc = []
      val acc = LiteralSet.foldl (deduceResolution literals cl) acc lits
      val acc = foldl (deduceParamodulationWith subterms cl) acc eqns
      val acc = foldl (deduceParamodulationInto equations cl) acc subtms
    in
      rev acc
    end;

(* ------------------------------------------------------------------------- *)
(* Extract clauses from the active set that can be simplified.               *)
(* ------------------------------------------------------------------------- *)

local
  fun clause_rewritables active =
      let
        val Active {clauses,rewrite,...} = active

        fun rewr (id,cl,ids) =
            let
              val cl' = Clause.rewrite rewrite cl
            in
              if Clause.equalThms cl cl' then ids else IntSet.add ids id
            end
      in
        IntMap.foldr rewr IntSet.empty clauses
      end;

  fun orderedRedexResidues (((l,r),_),ort) =
      case ort of
        NONE => []
      | SOME Rewrite.LeftToRight => [(l,r,true)]
      | SOME Rewrite.RightToLeft => [(r,l,true)];

  fun unorderedRedexResidues (((l,r),_),ort) =
      case ort of
        NONE => [(l,r,false),(r,l,false)]
      | SOME _ => [];

  fun rewrite_rewritables active rewr_ids =
      let
        val Active {parameters,rewrite,clauses,allSubterms,...} = active
        val {clause = {ordering,...}, ...} = parameters
        val order = KnuthBendixOrder.compare ordering

        fun addRewr (id,acc) =
            if IntMap.inDomain id clauses then IntSet.add acc id else acc

        fun addReduce ((l,r,ord),acc) =
            let
              fun isValidRewr tm =
                  case total (Subst.match Subst.empty l) tm of
                    NONE => false
                  | SOME sub =>
                    ord orelse
                    let
                      val tm' = Subst.subst (Subst.normalize sub) r
                    in
                      order (tm,tm') = SOME GREATER
                    end
                    
              fun addRed ((cl,tm),acc) =
                  let
(*TRACE5
                    val () = Parser.ppTrace Clause.pp "Active.addRed: cl" cl
                    val () = Parser.ppTrace Term.pp "Active.addRed: tm" tm
*)
                    val id = Clause.id cl
                  in
                    if IntSet.member id acc then acc
                    else if not (isValidRewr tm) then acc
                    else IntSet.add acc id
                  end

(*TRACE5
              val () = Parser.ppTrace Term.pp "Active.addReduce: l" l
              val () = Parser.ppTrace Term.pp "Active.addReduce: r" r
              val () = Parser.ppTrace Parser.ppBool "Active.addReduce: ord" ord
*)
            in
              List.foldl addRed acc (TermNet.matched allSubterms l)
            end
              
        fun addEquation redexResidues (id,acc) =
            case Rewrite.peek rewrite id of
              NONE => acc
            | SOME eqn_ort => List.foldl addReduce acc (redexResidues eqn_ort)

        val addOrdered = addEquation orderedRedexResidues

        val addUnordered = addEquation unorderedRedexResidues

        val ids = IntSet.empty
        val ids = List.foldl addRewr ids rewr_ids
        val ids = List.foldl addOrdered ids rewr_ids
        val ids = List.foldl addUnordered ids rewr_ids
      in
        ids
      end;

  fun choose_clause_rewritables active ids = size active <= length ids

  fun rewritables active ids =
      if choose_clause_rewritables active ids then clause_rewritables active
      else rewrite_rewritables active ids;

(*DEBUG
  val rewritables = fn active => fn ids =>
      let
        val clause_ids = clause_rewritables active
        val rewrite_ids = rewrite_rewritables active ids

        val () =
            if IntSet.equal rewrite_ids clause_ids then ()
            else
              let
                val ppIdl = Parser.ppList Parser.ppInt
                val ppIds = Parser.ppMap IntSet.toList ppIdl
                val () = Parser.ppTrace pp "Active.rewritables: active" active
                val () = Parser.ppTrace ppIdl "Active.rewritables: ids" ids
                val () = Parser.ppTrace ppIds
                           "Active.rewritables: clause_ids" clause_ids
                val () = Parser.ppTrace ppIds
                           "Active.rewritables: rewrite_ids" rewrite_ids
              in
                raise Bug "Active.rewritables: ~(rewrite_ids SUBSET clause_ids)"
              end
      in
        if choose_clause_rewritables active ids then clause_ids else rewrite_ids
      end;
*)

  fun delete active ids =
      if IntSet.null ids then active
      else
        let
          fun idPred id = not (IntSet.member id ids)
                          
          fun clausePred cl = idPred (Clause.id cl)
                              
          val Active
                {parameters,clauses,units,rewrite,subsume,literals,
                 equations,subterms,allSubterms} = active

          val clauses = IntMap.filter (idPred o fst) clauses
          and subsume = Subsume.filter clausePred subsume
          and literals = LiteralNet.filter (clausePred o #1) literals
          and equations = TermNet.filter (clausePred o #1) equations
          and subterms = TermNet.filter (clausePred o #1) subterms
          and allSubterms = TermNet.filter (clausePred o fst) allSubterms
        in
          Active
            {parameters = parameters, clauses = clauses, units = units,
             rewrite = rewrite, subsume = subsume, literals = literals,
             equations = equations, subterms = subterms,
             allSubterms = allSubterms}
        end;
in
  fun extract_rewritables (active as Active {clauses,rewrite,...}) =
      if Rewrite.isReduced rewrite then (active,[])
      else
        let
(*TRACE3
          val () = trace "Active.extract_rewritables: inter-reducing\n"
*)
          val (rewrite,ids) = Rewrite.reduce' rewrite
          val active = setRewrite active rewrite
          val ids = rewritables active ids
          val cls = IntSet.transform (IntMap.get clauses) ids
(*TRACE3
          val ppCls = Parser.ppList Clause.pp
          val () = Parser.ppTrace ppCls "Active.extract_rewritables: cls" cls
*)
        in
          (delete active ids, cls)
        end
(*DEBUG
        handle Error err =>
          raise Bug ("Active.extract_rewritables: shouldn't fail\n" ^ err);
*)
end;

(* ------------------------------------------------------------------------- *)
(* Factor clauses.                                                           *)
(* ------------------------------------------------------------------------- *)

local
  fun prefactor_simplify active subsume =
      let
        val Active {parameters,units,rewrite,...} = active
        val {prefactor,...} = parameters
      in
        simplify prefactor units rewrite subsume
      end;

  fun postfactor_simplify active subsume =
      let
        val Active {parameters,units,rewrite,...} = active
        val {postfactor,...} = parameters
      in
        simplify postfactor units rewrite subsume
      end;

  val sort_utilitywise =
      let
        fun utility cl =
            case LiteralSet.size (Clause.literals cl) of
              0 => ~1
            | 1 => if Thm.isUnitEq (Clause.thm cl) then 0 else 1
            | n => n
      in
        sortMap utility Int.compare
      end;

  fun factor_add (cl, active_subsume_acc as (active,subsume,acc)) =
      case postfactor_simplify active subsume cl of
        NONE => active_subsume_acc
      | SOME cl =>
        let
          val active = addFactorClause active cl
          and subsume = addSubsume subsume cl
          and acc = cl :: acc
        in
          (active,subsume,acc)
        end;

  fun factor1 (cl, active_subsume_acc as (active,subsume,_)) =
      case prefactor_simplify active subsume cl of
        NONE => active_subsume_acc
      | SOME cl =>
        let
          val cls = sort_utilitywise (cl :: Clause.factor cl)
        in
          foldl factor_add active_subsume_acc cls
        end;

  fun factor' active acc [] = (active, rev acc)
    | factor' active acc cls =
      let
        val cls = sort_utilitywise cls
        val subsume = getSubsume active
        val (active,_,acc) = foldl factor1 (active,subsume,acc) cls
        val (active,cls) = extract_rewritables active
      in
        factor' active acc cls
      end;
in
  fun factor active cls = factor' active [] cls;
end;

(*TRACE4
val factor = fn active => fn cls =>
    let
      val ppCls = Parser.ppList Clause.pp
      val () = Parser.ppTrace ppCls "Active.factor: cls" cls
      val (active,cls') = factor active cls
      val () = Parser.ppTrace ppCls "Active.factor: cls'" cls'
    in
      (active,cls')
    end;
*)

(* ------------------------------------------------------------------------- *)
(* Create a new active clause set and initialize clauses.                    *)
(* ------------------------------------------------------------------------- *)

fun new parameters ths =
    let
      val {clause,...} = parameters

      fun mk_clause th =
          Clause.mk {parameters = clause, id = Clause.newId (), thm = th}

      val cls = map mk_clause ths
    in
      factor (empty parameters) cls
    end;

(* ------------------------------------------------------------------------- *)
(* Add a clause into the active set and deduce all consequences.             *)
(* ------------------------------------------------------------------------- *)

fun add active cl =
    case simplifyActive maxSimplify active cl of
      NONE => (active,[])
    | SOME cl' =>
      if Clause.isContradiction cl' then (active,[cl'])
      else if not (Clause.equalThms cl cl') then factor active [cl']
      else
        let
(*TRACE3
          val () = Parser.ppTrace Clause.pp "Active.add: cl" cl
*)
          val active = addClause active cl
          val cl = Clause.freshVars cl
          val cls = deduce active cl
          val (active,cls) = factor active cls
(*TRACE2
          val ppCls = Parser.ppList Clause.pp
          val () = Parser.ppTrace ppCls "Active.add: cls" cls
*)
        in
          (active,cls)
        end;

end
end;

(**** Original file: Waiting.sig ****)

(* ========================================================================= *)
(* THE WAITING SET OF CLAUSES                                                *)
(* Copyright (c) 2002-2007 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Waiting =
sig

(* ------------------------------------------------------------------------- *)
(* A type of waiting sets of clauses.                                        *)
(* ------------------------------------------------------------------------- *)

type parameters =
     {symbolsWeight : real,
      literalsWeight : real,
      modelsWeight : real,
      modelChecks : int,
      models : Metis.Model.parameters list}

type waiting

type distance

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val default : parameters

val new : parameters -> Metis.Clause.clause list -> waiting

val size : waiting -> int

val pp : waiting Metis.Parser.pp

(* ------------------------------------------------------------------------- *)
(* Adding new clauses.                                                       *)
(* ------------------------------------------------------------------------- *)

val add : waiting -> distance * Metis.Clause.clause list -> waiting

(* ------------------------------------------------------------------------- *)
(* Removing the lightest clause.                                             *)
(* ------------------------------------------------------------------------- *)

val remove : waiting -> ((distance * Metis.Clause.clause) * waiting) option

end

(**** Original file: Waiting.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* THE WAITING SET OF CLAUSES                                                *)
(* Copyright (c) 2002-2007 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Waiting :> Waiting =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* A type of waiting sets of clauses.                                        *)
(* ------------------------------------------------------------------------- *)

(* The parameter type controls the heuristics for clause selection.          *)
(* Increasing any of the *Weight parameters will favour clauses with low     *)
(* values of that field.                                                     *)

(* Note that there is an extra parameter of inference distance from the      *)
(* starting axioms (a.k.a. time) which has a fixed weight of 1, so all       *)
(* the other parameters should be set relative to this baseline.             *)

(* The first two parameters, symbolsWeight and literalsWeight, control the   *)
(* time:weight ratio, i.e., whether to favour clauses derived in a few       *)
(* steps from the axioms (time) or whether to favour small clauses (weight). *)
(* Small can be a combination of low number of symbols (the symbolWeight     *)
(* parameter) or literals (the literalsWeight parameter).                    *)

(* modelsWeight controls the semantic guidance. Increasing this parameter    *)
(* favours clauses that return false more often when interpreted             *)
(* modelChecks times over the given list of models.                          *)

type parameters =
     {symbolsWeight : real,
      literalsWeight : real,
      modelsWeight : real,
      modelChecks : int,
      models : Model.parameters list};

type distance = real;

type weight = real;

datatype waiting =
    Waiting of
      {parameters : parameters,
       clauses : (weight * (distance * Clause.clause)) Heap.heap,
       models : Model.model list};

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val default : parameters =
     {symbolsWeight = 1.0,
      literalsWeight = 0.0,
      modelsWeight = 0.0,
      modelChecks = 20,
      models = []};

fun size (Waiting {clauses,...}) = Heap.size clauses;

val pp =
    Parser.ppMap
      (fn w => "Waiting{" ^ Int.toString (size w) ^ "}")
      Parser.ppString;

(*DEBUG
val pp =
    Parser.ppMap
      (fn Waiting {clauses,...} =>
          map (fn (w,(_,cl)) => (w, Clause.id cl, cl)) (Heap.toList clauses))
      (Parser.ppList (Parser.ppTriple Parser.ppReal Parser.ppInt Clause.pp));
*)

(* ------------------------------------------------------------------------- *)
(* Clause weights.                                                           *)
(* ------------------------------------------------------------------------- *)

local
  fun clauseSymbols cl = Real.fromInt (LiteralSet.typedSymbols cl);

  fun clauseLiterals cl = Real.fromInt (LiteralSet.size cl);

  fun clauseSat modelChecks models cl =
      let
        fun g {T,F} = (Real.fromInt T / Real.fromInt (T + F)) + 1.0
        fun f (m,z) = g (Model.checkClause {maxChecks = modelChecks} m cl) * z
      in
        foldl f 1.0 models
      end;

  fun priority cl = 1e~12 * Real.fromInt (Clause.id cl);
in
  fun clauseWeight (parm : parameters) models dist cl =
      let
(*TRACE3
        val () = Parser.ppTrace Clause.pp "Waiting.clauseWeight: cl" cl
*)
        val {symbolsWeight,literalsWeight,modelsWeight,modelChecks,...} = parm
        val lits = Clause.literals cl
        val symbolsW = Math.pow (clauseSymbols lits, symbolsWeight)
        val literalsW = Math.pow (clauseLiterals lits, literalsWeight)
        val modelsW = Math.pow (clauseSat modelChecks models lits, modelsWeight)
(*TRACE4
        val () = trace ("Waiting.clauseWeight: dist = " ^
                        Real.toString dist ^ "\n")
        val () = trace ("Waiting.clauseWeight: symbolsW = " ^
                        Real.toString symbolsW ^ "\n")
        val () = trace ("Waiting.clauseWeight: literalsW = " ^
                        Real.toString literalsW ^ "\n")
        val () = trace ("Waiting.clauseWeight: modelsW = " ^
                        Real.toString modelsW ^ "\n")
*)
        val weight = dist * symbolsW * literalsW * modelsW + priority cl
(*TRACE3
        val () = trace ("Waiting.clauseWeight: weight = " ^
                        Real.toString weight ^ "\n")
*)
      in
        weight
      end;
end;

(* ------------------------------------------------------------------------- *)
(* Adding new clauses.                                                       *)
(* ------------------------------------------------------------------------- *)

fun add waiting (_,[]) = waiting
  | add waiting (dist,cls) =
    let
(*TRACE3
      val () = Parser.ppTrace pp "Waiting.add: waiting" waiting
      val () = Parser.ppTrace (Parser.ppList Clause.pp) "Waiting.add: cls" cls
*)

      val Waiting {parameters,clauses,models} = waiting

      val dist = dist + Math.ln (Real.fromInt (length cls))

      val weight = clauseWeight parameters models dist

      fun f (cl,acc) = Heap.add acc (weight cl, (dist,cl))

      val clauses = foldl f clauses cls

      val waiting =
          Waiting {parameters = parameters, clauses = clauses, models = models}

(*TRACE3
      val () = Parser.ppTrace pp "Waiting.add: waiting" waiting
*)
    in
      waiting
    end;

local
  fun cmp ((w1,_),(w2,_)) = Real.compare (w1,w2);

  fun empty parameters =
      let
        val clauses = Heap.new cmp
        and models = map Model.new (#models parameters)
      in
        Waiting {parameters = parameters, clauses = clauses, models = models}
      end;
in
  fun new parameters cls = add (empty parameters) (0.0,cls);
end;

(* ------------------------------------------------------------------------- *)
(* Removing the lightest clause.                                             *)
(* ------------------------------------------------------------------------- *)

fun remove (Waiting {parameters,clauses,models}) =
    if Heap.null clauses then NONE
    else
      let
        val ((_,dcl),clauses) = Heap.remove clauses
        val waiting =
            Waiting
              {parameters = parameters, clauses = clauses, models = models}
      in
        SOME (dcl,waiting)
      end;

end
end;

(**** Original file: Resolution.sig ****)

(* ========================================================================= *)
(* THE RESOLUTION PROOF PROCEDURE                                            *)
(* Copyright (c) 2001-2007 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Resolution =
sig

(* ------------------------------------------------------------------------- *)
(* A type of resolution proof procedures.                                    *)
(* ------------------------------------------------------------------------- *)

type parameters =
     {active : Metis.Active.parameters,
      waiting : Metis.Waiting.parameters}

type resolution

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val default : parameters

val new : parameters -> Metis.Thm.thm list -> resolution

val active : resolution -> Metis.Active.active

val waiting : resolution -> Metis.Waiting.waiting

val pp : resolution Metis.Parser.pp

(* ------------------------------------------------------------------------- *)
(* The main proof loop.                                                      *)
(* ------------------------------------------------------------------------- *)

datatype decision =
    Contradiction of Metis.Thm.thm
  | Satisfiable of Metis.Thm.thm list

datatype state =
    Decided of decision
  | Undecided of resolution

val iterate : resolution -> state

val loop : resolution -> decision

end

(**** Original file: Resolution.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* THE RESOLUTION PROOF PROCEDURE                                            *)
(* Copyright (c) 2001-2007 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Resolution :> Resolution =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* Parameters.                                                               *)
(* ------------------------------------------------------------------------- *)

type parameters =
     {active : Active.parameters,
      waiting : Waiting.parameters};

datatype resolution =
    Resolution of
      {parameters : parameters,
       active : Active.active,
       waiting : Waiting.waiting};

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val default : parameters =
    {active = Active.default,
     waiting = Waiting.default};

fun new parameters ths =
    let
      val {active = activeParm, waiting = waitingParm} = parameters
      val (active,cls) = Active.new activeParm ths  (* cls = factored ths *)
      val waiting = Waiting.new waitingParm cls
    in
      Resolution {parameters = parameters, active = active, waiting = waiting}
    end;

fun active (Resolution {active = a, ...}) = a;

fun waiting (Resolution {waiting = w, ...}) = w;

val pp =
    Parser.ppMap
      (fn Resolution {active,waiting,...} =>
          "Resolution(" ^ Int.toString (Active.size active) ^
          "<-" ^ Int.toString (Waiting.size waiting) ^ ")")
      Parser.ppString;

(* ------------------------------------------------------------------------- *)
(* The main proof loop.                                                      *)
(* ------------------------------------------------------------------------- *)

datatype decision =
    Contradiction of Thm.thm
  | Satisfiable of Thm.thm list;

datatype state =
    Decided of decision
  | Undecided of resolution;

fun iterate resolution =
    let
      val Resolution {parameters,active,waiting} = resolution
(*TRACE2
      val () = Parser.ppTrace Active.pp "Resolution.iterate: active" active
      val () = Parser.ppTrace Waiting.pp "Resolution.iterate: waiting" waiting
*)
    in
      case Waiting.remove waiting of
        NONE =>
        Decided (Satisfiable (map Clause.thm (Active.saturated active)))
      | SOME ((d,cl),waiting) =>
        if Clause.isContradiction cl then
          Decided (Contradiction (Clause.thm cl))
        else
          let
(*TRACE1
            val () = Parser.ppTrace Clause.pp "Resolution.iterate: cl" cl
*)
            val (active,cls) = Active.add active cl
            val waiting = Waiting.add waiting (d,cls)
          in
            Undecided
              (Resolution
                 {parameters = parameters, active = active, waiting = waiting})
          end
    end;

fun loop resolution =
    case iterate resolution of
      Decided decision => decision
    | Undecided resolution => loop resolution;

end
end;

(**** Original file: Tptp.sig ****)

(* ========================================================================= *)
(* THE TPTP PROBLEM FILE FORMAT (TPTP v2)                                    *)
(* Copyright (c) 2001-2007 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Tptp =
sig

(* ------------------------------------------------------------------------- *)
(* Mapping TPTP functions and relations to different names.                  *)
(* ------------------------------------------------------------------------- *)

val functionMapping : {name : string, arity : int, tptp : string} list Unsynchronized.ref

val relationMapping : {name : string, arity : int, tptp : string} list Unsynchronized.ref

(* ------------------------------------------------------------------------- *)
(* TPTP literals.                                                            *)
(* ------------------------------------------------------------------------- *)

datatype literal =
    Boolean of bool
  | Literal of Metis.Literal.literal

val negate : literal -> literal

val literalFunctions : literal -> Metis.NameAritySet.set

val literalRelation : literal -> Metis.Atom.relation option

val literalFreeVars : literal -> Metis.NameSet.set

(* ------------------------------------------------------------------------- *)
(* TPTP formulas.                                                            *)
(* ------------------------------------------------------------------------- *)

datatype formula =
    CnfFormula of {name : string, role : string, clause : literal list}
  | FofFormula of {name : string, role : string, formula : Metis.Formula.formula}

val formulaFunctions : formula -> Metis.NameAritySet.set

val formulaRelations : formula -> Metis.NameAritySet.set

val formulaFreeVars : formula -> Metis.NameSet.set

val formulaIsConjecture : formula -> bool

val ppFormula : formula Metis.Parser.pp

val parseFormula : char Metis.Stream.stream -> formula Metis.Stream.stream

val formulaToString : formula -> string

val formulaFromString : string -> formula

(* ------------------------------------------------------------------------- *)
(* TPTP problems.                                                            *)
(* ------------------------------------------------------------------------- *)

datatype goal =
    Cnf of Metis.Problem.problem
  | Fof of Metis.Formula.formula

type problem = {comments : string list, formulas : formula list}

val read : {filename : string} -> problem

val write : {filename : string} -> problem -> unit

val hasConjecture : problem -> bool

val toGoal : problem -> goal

val fromProblem : Metis.Problem.problem -> problem

val prove : {filename : string} -> bool

(* ------------------------------------------------------------------------- *)
(* TSTP proofs.                                                              *)
(* ------------------------------------------------------------------------- *)

val ppProof : Metis.Proof.proof Metis.Parser.pp

val proofToString : Metis.Proof.proof -> string

end

(**** Original file: Tptp.sml ****)

structure Metis = struct open Metis
(* Metis-specific ML environment *)
nonfix ++ -- RL mem;
val explode = String.explode;
val implode = String.implode;
val print = TextIO.print;
val foldl = List.foldl;
val foldr = List.foldr;

(* ========================================================================= *)
(* THE TPTP PROBLEM FILE FORMAT (TPTP v2)                                    *)
(* Copyright (c) 2001-2007 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Tptp :> Tptp =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(* Constants.                                                                *)
(* ------------------------------------------------------------------------- *)

val ROLE_NEGATED_CONJECTURE = "negated_conjecture"
and ROLE_CONJECTURE = "conjecture";

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun isHdTlString hp tp s =
    let
      fun ct 0 = true
        | ct i = tp (String.sub (s,i)) andalso ct (i - 1)

      val n = size s
    in
      n > 0 andalso hp (String.sub (s,0)) andalso ct (n - 1)
    end;

(* ------------------------------------------------------------------------- *)
(* Mapping TPTP functions and relations to different names.                  *)
(* ------------------------------------------------------------------------- *)

val functionMapping = Unsynchronized.ref
    [(* Mapping TPTP functions to infix symbols *)
     {name = "*", arity = 2, tptp = "multiply"},
     {name = "/", arity = 2, tptp = "divide"},
     {name = "+", arity = 2, tptp = "add"},
     {name = "-", arity = 2, tptp = "subtract"},
     {name = "::", arity = 2, tptp = "cons"},
     {name = ",", arity = 2, tptp = "pair"},
     (* Expanding HOL symbols to TPTP alphanumerics *)
     {name = ":", arity = 2, tptp = "has_type"},
     {name = ".", arity = 2, tptp = "apply"},
     {name = "<=", arity = 0, tptp = "less_equal"}];

val relationMapping = Unsynchronized.ref
    [(* Mapping TPTP relations to infix symbols *)
     {name = "=", arity = 2, tptp = "="},
     {name = "==", arity = 2, tptp = "equalish"},
     {name = "<=", arity = 2, tptp = "less_equal"},
     {name = "<", arity = 2, tptp = "less_than"},
     (* Expanding HOL symbols to TPTP alphanumerics *)
     {name = "{}", arity = 1, tptp = "bool"}];

fun mappingToTptp x =
    let
      fun mk ({name,arity,tptp},m) = NameArityMap.insert m ((name,arity),tptp)
    in
      foldl mk (NameArityMap.new ()) x
    end;

fun mappingFromTptp x =
    let
      fun mk ({name,arity,tptp},m) = NameArityMap.insert m ((tptp,arity),name)
    in
      foldl mk (NameArityMap.new ()) x
    end;

fun findMapping mapping (name_arity as (n,_)) =
    Option.getOpt (NameArityMap.peek mapping name_arity, n);

fun mapTerm functionMap =
    let
      val mapName = findMapping functionMap

      fun mapTm (tm as Term.Var _) = tm
        | mapTm (Term.Fn (f,a)) = Term.Fn (mapName (f, length a), map mapTm a)
    in
      mapTm
    end;

fun mapAtom {functionMap,relationMap} (p,a) =
    (findMapping relationMap (p, length a), map (mapTerm functionMap) a);

fun mapFof maps =
    let
      open Formula

      fun form True = True
        | form False = False
        | form (Atom a) = Atom (mapAtom maps a)
        | form (Not p) = Not (form p)
        | form (And (p,q)) = And (form p, form q)
        | form (Or (p,q)) = Or (form p, form q)
        | form (Imp (p,q)) = Imp (form p, form q)
        | form (Iff (p,q)) = Iff (form p, form q)
        | form (Forall (v,p)) = Forall (v, form p)
        | form (Exists (v,p)) = Exists (v, form p)
    in
      form
    end;

(* ------------------------------------------------------------------------- *)
(* Comments.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun mkComment "" = "%"
  | mkComment line = "% " ^ line;

fun destComment "" = ""
  | destComment l =
    let
      val _ = String.sub (l,0) = #"%" orelse raise Error "destComment"
      val n = if size l >= 2 andalso String.sub (l,1) = #" " then 2 else 1
    in
      String.extract (l,n,NONE)
    end;

val isComment = can destComment;

(* ------------------------------------------------------------------------- *)
(* TPTP literals.                                                            *)
(* ------------------------------------------------------------------------- *)

datatype literal =
    Boolean of bool
  | Literal of Literal.literal;

fun negate (Boolean b) = (Boolean (not b))
  | negate (Literal l) = (Literal (Literal.negate l));

fun literalFunctions (Boolean _) = NameAritySet.empty
  | literalFunctions (Literal lit) = Literal.functions lit;

fun literalRelation (Boolean _) = NONE
  | literalRelation (Literal lit) = SOME (Literal.relation lit);

fun literalToFormula (Boolean true) = Formula.True
  | literalToFormula (Boolean false) = Formula.False
  | literalToFormula (Literal lit) = Literal.toFormula lit;

fun literalFromFormula Formula.True = Boolean true
  | literalFromFormula Formula.False = Boolean false
  | literalFromFormula fm = Literal (Literal.fromFormula fm);

fun literalFreeVars (Boolean _) = NameSet.empty
  | literalFreeVars (Literal lit) = Literal.freeVars lit;

fun literalSubst sub lit =
    case lit of
      Boolean _ => lit
    | Literal l => Literal (Literal.subst sub l);

fun mapLiteral maps lit =
    case lit of
      Boolean _ => lit
    | Literal (p,a) => Literal (p, mapAtom maps a);

fun destLiteral (Literal l) = l
  | destLiteral _ = raise Error "destLiteral";

(* ------------------------------------------------------------------------- *)
(* Printing formulas using TPTP syntax.                                      *)
(* ------------------------------------------------------------------------- *)

val ppVar = Parser.ppString;

local
  fun term pp (Term.Var v) = ppVar pp v
    | term pp (Term.Fn (c,[])) = Parser.addString pp c
    | term pp (Term.Fn (f,tms)) =
      (Parser.beginBlock pp Parser.Inconsistent 2;
       Parser.addString pp (f ^ "(");
       Parser.ppSequence "," term pp tms;
       Parser.addString pp ")";
       Parser.endBlock pp);
in
  fun ppTerm pp tm =
      (Parser.beginBlock pp Parser.Inconsistent 0;
       term pp tm;
       Parser.endBlock pp);
end;

fun ppAtom pp atm = ppTerm pp (Term.Fn atm);

local
  open Formula;

  fun fof pp (fm as And _) = assoc_binary pp ("&", stripConj fm)
    | fof pp (fm as Or _) = assoc_binary pp ("|", stripDisj fm)
    | fof pp (Imp a_b) = nonassoc_binary pp ("=>",a_b)
    | fof pp (Iff a_b) = nonassoc_binary pp ("<=>",a_b)
    | fof pp fm = unitary pp fm

  and nonassoc_binary pp (s,a_b) =
      Parser.ppBinop (" " ^ s) unitary unitary pp a_b

  and assoc_binary pp (s,l) = Parser.ppSequence (" " ^ s) unitary pp l

  and unitary pp fm =
      if isForall fm then quantified pp ("!", stripForall fm)
      else if isExists fm then quantified pp ("?", stripExists fm)
      else if atom pp fm then ()
      else if isNeg fm then
        let
          fun pr () = (Parser.addString pp "~"; Parser.addBreak pp (1,0))
          val (n,fm) = Formula.stripNeg fm
        in
          Parser.beginBlock pp Parser.Inconsistent 2;
          funpow n pr ();
          unitary pp fm;
          Parser.endBlock pp
        end
      else
        (Parser.beginBlock pp Parser.Inconsistent 1;
         Parser.addString pp "(";
         fof pp fm;
         Parser.addString pp ")";
         Parser.endBlock pp)

  and quantified pp (q,(vs,fm)) =
      (Parser.beginBlock pp Parser.Inconsistent 2;
       Parser.addString pp (q ^ " ");
       Parser.beginBlock pp Parser.Inconsistent (String.size q);
       Parser.addString pp "[";
       Parser.ppSequence "," ppVar pp vs;
       Parser.addString pp "] :";
       Parser.endBlock pp;
       Parser.addBreak pp (1,0);
       unitary pp fm;
       Parser.endBlock pp)
      
  and atom pp True = (Parser.addString pp "$true"; true)
    | atom pp False = (Parser.addString pp "$false"; true)
    | atom pp fm =
      case total destEq fm of
        SOME a_b => (Parser.ppBinop " =" ppTerm ppTerm pp a_b; true)
      | NONE =>
        case total destNeq fm of
          SOME a_b => (Parser.ppBinop " !=" ppTerm ppTerm pp a_b; true)
        | NONE => case fm of Atom atm => (ppAtom pp atm; true) | _ => false;
in
  fun ppFof pp fm =
      (Parser.beginBlock pp Parser.Inconsistent 0;
       fof pp fm;
       Parser.endBlock pp);
end;

(* ------------------------------------------------------------------------- *)
(* TPTP clauses.                                                             *)
(* ------------------------------------------------------------------------- *)

type clause = literal list;

val clauseFunctions =
    let
      fun funcs (lit,acc) = NameAritySet.union (literalFunctions lit) acc
    in
      foldl funcs NameAritySet.empty
    end;

val clauseRelations =
    let
      fun rels (lit,acc) =
          case literalRelation lit of
            NONE => acc
          | SOME r => NameAritySet.add acc r
    in
      foldl rels NameAritySet.empty
    end;

val clauseFreeVars =
    let
      fun fvs (lit,acc) = NameSet.union (literalFreeVars lit) acc
    in
      foldl fvs NameSet.empty
    end;

fun clauseSubst sub lits = map (literalSubst sub) lits;

fun mapClause maps lits = map (mapLiteral maps) lits;

fun clauseToFormula lits = Formula.listMkDisj (map literalToFormula lits);

fun clauseFromFormula fm = map literalFromFormula (Formula.stripDisj fm);

fun clauseFromLiteralSet cl =
    clauseFromFormula
      (Formula.listMkDisj (LiteralSet.transform Literal.toFormula cl));

fun clauseFromThm th = clauseFromLiteralSet (Thm.clause th);

val ppClause = Parser.ppMap clauseToFormula ppFof;

(* ------------------------------------------------------------------------- *)
(* TPTP formulas.                                                            *)
(* ------------------------------------------------------------------------- *)

datatype formula =
    CnfFormula of {name : string, role : string, clause : clause}
  | FofFormula of {name : string, role : string, formula : Formula.formula};

fun destCnfFormula (CnfFormula x) = x
  | destCnfFormula _ = raise Error "destCnfFormula";

val isCnfFormula = can destCnfFormula;

fun destFofFormula (FofFormula x) = x
  | destFofFormula _ = raise Error "destFofFormula";

val isFofFormula = can destFofFormula;

fun formulaFunctions (CnfFormula {clause,...}) = clauseFunctions clause
  | formulaFunctions (FofFormula {formula,...}) = Formula.functions formula;

fun formulaRelations (CnfFormula {clause,...}) = clauseRelations clause
  | formulaRelations (FofFormula {formula,...}) = Formula.relations formula;

fun formulaFreeVars (CnfFormula {clause,...}) = clauseFreeVars clause
  | formulaFreeVars (FofFormula {formula,...}) = Formula.freeVars formula;

fun mapFormula maps (CnfFormula {name,role,clause}) =
    CnfFormula {name = name, role = role, clause = mapClause maps clause}
  | mapFormula maps (FofFormula {name,role,formula}) =
    FofFormula {name = name, role = role, formula = mapFof maps formula};

val formulasFunctions =
    let
      fun funcs (fm,acc) = NameAritySet.union (formulaFunctions fm) acc
    in
      foldl funcs NameAritySet.empty
    end;

val formulasRelations =
    let
      fun rels (fm,acc) = NameAritySet.union (formulaRelations fm) acc
    in
      foldl rels NameAritySet.empty
    end;

fun formulaIsConjecture (CnfFormula {role,...}) = role = ROLE_NEGATED_CONJECTURE
  | formulaIsConjecture (FofFormula {role,...}) = role = ROLE_CONJECTURE;

local
  open Parser;

  infixr 8 ++
  infixr 7 >>
  infixr 6 ||

  datatype token =
      AlphaNum of string
    | Punct of char
    | Quote of string;

  fun isAlphaNum #"_" = true
    | isAlphaNum c = Char.isAlphaNum c;

  local
    val alphaNumToken = atLeastOne (some isAlphaNum) >> (AlphaNum o implode);

    val punctToken =
        let
          val punctChars = "<>=-*+/\\?@|!$%&#^:;~()[]{}.,"
        in
          some (Char.contains punctChars) >> Punct
        end;

    val quoteToken =
        let
          val escapeParser =
              exact #"'" >> singleton ||
              exact #"\\" >> singleton

          fun stopOn #"'" = true
            | stopOn #"\n" = true
            | stopOn _ = false

          val quotedParser =
              exact #"\\" ++ escapeParser >> op:: ||
              some (not o stopOn) >> singleton
        in
          exact #"'" ++ many quotedParser ++ exact #"'" >>
          (fn (_,(l,_)) => Quote (implode (List.concat l)))
        end;

    val lexToken = alphaNumToken || punctToken || quoteToken;

    val space = many (some Char.isSpace) >> K ();
  in
    val lexer = (space ++ lexToken ++ space) >> (fn ((),(tok,())) => tok);
  end;

  fun someAlphaNum p =
      maybe (fn AlphaNum s => if p s then SOME s else NONE | _ => NONE);

  fun alphaNumParser s = someAlphaNum (equal s) >> K ();

  fun isLower s = Char.isLower (String.sub (s,0));

  val lowerParser = someAlphaNum isLower;

  val upperParser = someAlphaNum (fn s => Char.isUpper (String.sub (s,0)));

  val stringParser = lowerParser || upperParser;

  val numberParser = someAlphaNum (List.all Char.isDigit o explode);

  fun somePunct p =
      maybe (fn Punct c => if p c then SOME c else NONE | _ => NONE);

  fun punctParser c = somePunct (equal c) >> K ();

  fun quoteParser p =
      let
        fun q s = if p s then s else "'" ^ s ^ "'"
      in
        maybe (fn Quote s => SOME (q s) | _ => NONE)
      end;

  local
    fun f [] = raise Bug "symbolParser"
      | f [x] = x
      | f (h :: t) = (h ++ f t) >> K ();
  in
    fun symbolParser s = f (map punctParser (explode s));
  end;

  val definedParser =
      punctParser #"$" ++ someAlphaNum (K true) >> (fn ((),s) => "$" ^ s);

  val systemParser =
      punctParser #"$" ++ punctParser #"$" ++ someAlphaNum (K true) >>
      (fn ((),((),s)) => "$$" ^ s);

  val nameParser = stringParser || numberParser || quoteParser (K false);

  val roleParser = lowerParser;

  local
    fun isProposition s = isHdTlString Char.isLower isAlphaNum s;
  in
    val propositionParser =
        someAlphaNum isProposition ||
        definedParser || systemParser || quoteParser isProposition;
  end;

  local
    fun isFunction s = isHdTlString Char.isLower isAlphaNum s;
  in
    val functionParser =
        someAlphaNum isFunction ||
        definedParser || systemParser || quoteParser isFunction;
  end;

  local
    fun isConstant s =
        isHdTlString Char.isLower isAlphaNum s orelse
        isHdTlString Char.isDigit Char.isDigit s;
  in
    val constantParser =
        someAlphaNum isConstant ||
        definedParser || systemParser || quoteParser isConstant;
  end;

  val varParser = upperParser;

  val varListParser =
      (punctParser #"[" ++ varParser ++
       many ((punctParser #"," ++ varParser) >> snd) ++
       punctParser #"]") >>
      (fn ((),(h,(t,()))) => h :: t);

  fun termParser input =
      ((functionArgumentsParser >> Term.Fn) ||
       nonFunctionArgumentsTermParser) input

  and functionArgumentsParser input =
      ((functionParser ++ punctParser #"(" ++ termParser ++
        many ((punctParser #"," ++ termParser) >> snd) ++
        punctParser #")") >>
       (fn (f,((),(t,(ts,())))) => (f, t :: ts))) input

  and nonFunctionArgumentsTermParser input =
      ((varParser >> Term.Var) ||
       (constantParser >> (fn n => Term.Fn (n,[])))) input

  val binaryAtomParser =
      ((punctParser #"=" ++ termParser) >>
       (fn ((),r) => fn l => Literal.mkEq (l,r))) ||
      ((symbolParser "!=" ++ termParser) >>
       (fn ((),r) => fn l => Literal.mkNeq (l,r)));

  val maybeBinaryAtomParser =
      optional binaryAtomParser >>
      (fn SOME f => (fn a => f (Term.Fn a))
        | NONE => (fn a => (true,a)));

  val literalAtomParser =
      ((functionArgumentsParser ++ maybeBinaryAtomParser) >>
       (fn (a,f) => f a)) ||
      ((nonFunctionArgumentsTermParser ++ binaryAtomParser) >>
       (fn (a,f) => f a)) ||
      (propositionParser >>
       (fn n => (true,(n,[]))));

  val atomParser =
      literalAtomParser >>
      (fn (pol,("$true",[])) => Boolean pol
        | (pol,("$false",[])) => Boolean (not pol)
        | (pol,("$equal",[a,b])) => Literal (pol, Atom.mkEq (a,b))
        | lit => Literal lit);

  val literalParser =
      ((punctParser #"~" ++ atomParser) >> (negate o snd)) ||
      atomParser;

  val disjunctionParser =
      (literalParser ++ many ((punctParser #"|" ++ literalParser) >> snd)) >>
      (fn (h,t) => h :: t);

  val clauseParser =
      ((punctParser #"(" ++ disjunctionParser ++ punctParser #")") >>
       (fn ((),(c,())) => c)) ||
      disjunctionParser;

(*
  An exact transcription of the fof_formula syntax from

    TPTP-v3.2.0/Documents/SyntaxBNF,

  fun fofFormulaParser input =
      (binaryFormulaParser || unitaryFormulaParser) input
  
  and binaryFormulaParser input =
      (nonAssocBinaryFormulaParser || assocBinaryFormulaParser) input

  and nonAssocBinaryFormulaParser input =
      ((unitaryFormulaParser ++ binaryConnectiveParser ++
        unitaryFormulaParser) >>
       (fn (f,(c,g)) => c (f,g))) input

  and binaryConnectiveParser input =
      ((symbolParser "<=>" >> K Formula.Iff) ||
       (symbolParser "=>" >> K Formula.Imp) ||
       (symbolParser "<=" >> K (fn (f,g) => Formula.Imp (g,f))) ||
       (symbolParser "<~>" >> K (Formula.Not o Formula.Iff)) ||
       (symbolParser "~|" >> K (Formula.Not o Formula.Or)) ||
       (symbolParser "~&" >> K (Formula.Not o Formula.And))) input

  and assocBinaryFormulaParser input =
      (orFormulaParser || andFormulaParser) input

  and orFormulaParser input =
      ((unitaryFormulaParser ++
        atLeastOne ((punctParser #"|" ++ unitaryFormulaParser) >> snd)) >>
       (fn (f,fs) => Formula.listMkDisj (f :: fs))) input

  and andFormulaParser input =
      ((unitaryFormulaParser ++
        atLeastOne ((punctParser #"&" ++ unitaryFormulaParser) >> snd)) >>
       (fn (f,fs) => Formula.listMkConj (f :: fs))) input

  and unitaryFormulaParser input =
      (quantifiedFormulaParser ||
       unaryFormulaParser ||
       ((punctParser #"(" ++ fofFormulaParser ++ punctParser #")") >>
        (fn ((),(f,())) => f)) ||
       (atomParser >>
        (fn Boolean b => Formula.mkBoolean b
          | Literal l => Literal.toFormula l))) input

  and quantifiedFormulaParser input =
      ((quantifierParser ++ varListParser ++ punctParser #":" ++
        unitaryFormulaParser) >>
       (fn (q,(v,((),f))) => q (v,f))) input

  and quantifierParser input =
      ((punctParser #"!" >> K Formula.listMkForall) ||
       (punctParser #"?" >> K Formula.listMkExists)) input

  and unaryFormulaParser input =
      ((unaryConnectiveParser ++ unitaryFormulaParser) >>
       (fn (c,f) => c f)) input

  and unaryConnectiveParser input =
      (punctParser #"~" >> K Formula.Not) input;
*)

(*
  This version is supposed to be equivalent to the spec version above,
  but uses closures to avoid reparsing prefixes.
*)

  fun fofFormulaParser input =
      ((unitaryFormulaParser ++ optional binaryFormulaParser) >>
       (fn (f,NONE) => f | (f, SOME t) => t f)) input
  
  and binaryFormulaParser input =
      (nonAssocBinaryFormulaParser || assocBinaryFormulaParser) input

  and nonAssocBinaryFormulaParser input =
      ((binaryConnectiveParser ++ unitaryFormulaParser) >>
       (fn (c,g) => fn f => c (f,g))) input

  and binaryConnectiveParser input =
      ((symbolParser "<=>" >> K Formula.Iff) ||
       (symbolParser "=>" >> K Formula.Imp) ||
       (symbolParser "<=" >> K (fn (f,g) => Formula.Imp (g,f))) ||
       (symbolParser "<~>" >> K (Formula.Not o Formula.Iff)) ||
       (symbolParser "~|" >> K (Formula.Not o Formula.Or)) ||
       (symbolParser "~&" >> K (Formula.Not o Formula.And))) input

  and assocBinaryFormulaParser input =
      (orFormulaParser || andFormulaParser) input

  and orFormulaParser input =
      (atLeastOne ((punctParser #"|" ++ unitaryFormulaParser) >> snd) >>
       (fn fs => fn f => Formula.listMkDisj (f :: fs))) input

  and andFormulaParser input =
      (atLeastOne ((punctParser #"&" ++ unitaryFormulaParser) >> snd) >>
       (fn fs => fn f => Formula.listMkConj (f :: fs))) input

  and unitaryFormulaParser input =
      (quantifiedFormulaParser ||
       unaryFormulaParser ||
       ((punctParser #"(" ++ fofFormulaParser ++ punctParser #")") >>
        (fn ((),(f,())) => f)) ||
       (atomParser >>
        (fn Boolean b => Formula.mkBoolean b
          | Literal l => Literal.toFormula l))) input

  and quantifiedFormulaParser input =
      ((quantifierParser ++ varListParser ++ punctParser #":" ++
        unitaryFormulaParser) >>
       (fn (q,(v,((),f))) => q (v,f))) input

  and quantifierParser input =
      ((punctParser #"!" >> K Formula.listMkForall) ||
       (punctParser #"?" >> K Formula.listMkExists)) input

  and unaryFormulaParser input =
      ((unaryConnectiveParser ++ unitaryFormulaParser) >>
       (fn (c,f) => c f)) input

  and unaryConnectiveParser input =
      (punctParser #"~" >> K Formula.Not) input;

  val cnfParser =
      (alphaNumParser "cnf" ++ punctParser #"(" ++
       nameParser ++ punctParser #"," ++
       roleParser ++ punctParser #"," ++
       clauseParser ++ punctParser #")" ++
       punctParser #".") >>
      (fn ((),((),(n,((),(r,((),(c,((),())))))))) =>
          CnfFormula {name = n, role = r, clause = c});

  val fofParser =
      (alphaNumParser "fof" ++ punctParser #"(" ++
       nameParser ++ punctParser #"," ++
       roleParser ++ punctParser #"," ++
       fofFormulaParser ++ punctParser #")" ++
       punctParser #".") >>
      (fn ((),((),(n,((),(r,((),(f,((),())))))))) =>
          FofFormula {name = n, role = r, formula = f});

  val formulaParser = cnfParser || fofParser;

  fun parseChars parser chars =
      let
        val tokens = Parser.everything (lexer >> singleton) chars
      in
        Parser.everything (parser >> singleton) tokens
      end;

  fun canParseString parser s =
      let
        val chars = Stream.fromString s
      in
        case Stream.toList (parseChars parser chars) of
          [_] => true
        | _ => false
      end
      handle NoParse => false;
in
  val parseFormula = parseChars formulaParser;

  val isTptpRelation = canParseString functionParser
  and isTptpProposition = canParseString propositionParser
  and isTptpFunction = canParseString functionParser
  and isTptpConstant = canParseString constantParser;
end;

fun formulaFromString s =
    case Stream.toList (parseFormula (Stream.fromList (explode s))) of
      [fm] => fm
    | _ => raise Parser.NoParse;

local
  local
    fun explodeAlpha s = List.filter Char.isAlpha (explode s);
  in
    fun normTptpName s n =
        case explodeAlpha n of
          [] => s
        | c :: cs => implode (Char.toLower c :: cs);

    fun normTptpVar s n =
        case explodeAlpha n of
          [] => s
        | c :: cs => implode (Char.toUpper c :: cs);
  end;

  fun normTptpFunc (n,0) = if isTptpConstant n then n else normTptpName "c" n
    | normTptpFunc (n,_) = if isTptpFunction n then n else normTptpName "f" n;

  fun normTptpRel (n,0) = if isTptpProposition n then n else normTptpName "p" n
    | normTptpRel (n,_) = if isTptpRelation n then n else normTptpName "r" n;

  fun mkMap set norm mapping =
      let
        val mapping = mappingToTptp mapping

        fun mk (n_r,(a,m)) =
            case NameArityMap.peek mapping n_r of
              SOME t => (a, NameArityMap.insert m (n_r,t))
            | NONE =>
              let
                val t = norm n_r
                val (n,_) = n_r
                val t = if t = n then n else Term.variantNum a t
              in
                (NameSet.add a t, NameArityMap.insert m (n_r,t))
              end

        val avoid =
            let
              fun mk ((n,r),s) =
                  let
                    val n = Option.getOpt (NameArityMap.peek mapping (n,r), n)
                  in
                    NameSet.add s n
                  end
            in
              NameAritySet.foldl mk NameSet.empty set
            end
      in
        snd (NameAritySet.foldl mk (avoid, NameArityMap.new ()) set)
      end;

  fun mkTptpVar a v = Term.variantNum a (normTptpVar "V" v);

  fun isTptpVar v = mkTptpVar NameSet.empty v = v;

  fun alphaFormula fm =
      let
        fun addVar v a s =
            let
              val v' = mkTptpVar a v
              val a = NameSet.add a v'
              and s = if v = v' then s else Subst.insert s (v, Term.Var v')
            in
              (v',(a,s))
            end

        fun initVar (v,(a,s)) = snd (addVar v a s)

        open Formula

        fun alpha _ _ True = True
          | alpha _ _ False = False
          | alpha _ s (Atom atm) = Atom (Atom.subst s atm)
          | alpha a s (Not p) = Not (alpha a s p)
          | alpha a s (And (p,q)) = And (alpha a s p, alpha a s q)
          | alpha a s (Or (p,q)) = Or (alpha a s p, alpha a s q)
          | alpha a s (Imp (p,q)) = Imp (alpha a s p, alpha a s q)
          | alpha a s (Iff (p,q)) = Iff (alpha a s p, alpha a s q)
          | alpha a s (Forall (v,p)) =
            let val (v,(a,s)) = addVar v a s in Forall (v, alpha a s p) end
          | alpha a s (Exists (v,p)) =
            let val (v,(a,s)) = addVar v a s in Exists (v, alpha a s p) end

        val fvs = formulaFreeVars fm
        val (avoid,fvs) = NameSet.partition isTptpVar fvs
        val (avoid,sub) = NameSet.foldl initVar (avoid,Subst.empty) fvs
(*TRACE5
        val () = Parser.ppTrace Subst.pp "Tptp.alpha: sub" sub
*)
      in
        case fm of
          CnfFormula {name,role,clause} =>
          CnfFormula {name = name, role = role, clause = clauseSubst sub clause}
        | FofFormula {name,role,formula} =>
          FofFormula {name = name, role = role, formula = alpha avoid sub formula}
      end;

  fun formulaToTptp maps fm = alphaFormula (mapFormula maps fm);
in
  fun formulasToTptp formulas =
      let
        val funcs = formulasFunctions formulas
        and rels = formulasRelations formulas
                   
        val functionMap = mkMap funcs normTptpFunc (!functionMapping)
        and relationMap = mkMap rels normTptpRel (!relationMapping)

        val maps = {functionMap = functionMap, relationMap = relationMap}
      in
        map (formulaToTptp maps) formulas
      end;
end;

fun formulasFromTptp formulas =
    let
      val functionMap = mappingFromTptp (!functionMapping)
      and relationMap = mappingFromTptp (!relationMapping)
                        
      val maps = {functionMap = functionMap, relationMap = relationMap}
    in
      map (mapFormula maps) formulas
    end;

local
  fun ppGen ppX pp (gen,name,role,x) =
      (Parser.beginBlock pp Parser.Inconsistent (size gen + 1);
       Parser.addString pp (gen ^ "(" ^ name ^ ",");
       Parser.addBreak pp (1,0);
       Parser.addString pp (role ^ ",");
       Parser.addBreak pp (1,0);
       Parser.beginBlock pp Parser.Consistent 1;
       Parser.addString pp "(";
       ppX pp x;
       Parser.addString pp ")";
       Parser.endBlock pp;
       Parser.addString pp ").";
       Parser.endBlock pp);
in
  fun ppFormula pp (CnfFormula {name,role,clause}) =
      ppGen ppClause pp ("cnf",name,role,clause)
    | ppFormula pp (FofFormula {name,role,formula}) =
      ppGen ppFof pp ("fof",name,role,formula);
end;

val formulaToString = Parser.toString ppFormula;

(* ------------------------------------------------------------------------- *)
(* TPTP problems.                                                            *)
(* ------------------------------------------------------------------------- *)

datatype goal =
    Cnf of Problem.problem
  | Fof of Formula.formula;

type problem = {comments : string list, formulas : formula list};

local
  fun stripComments acc strm =
      case strm of
        Stream.NIL => (rev acc, Stream.NIL)
      | Stream.CONS (line,rest) =>
        case total destComment line of
          SOME s => stripComments (s :: acc) (rest ())
        | NONE => (rev acc, Stream.filter (not o isComment) strm);
in
  fun read {filename} =
      let
        val lines = Stream.fromTextFile {filename = filename}

        val lines = Stream.map chomp lines

        val (comments,lines) = stripComments [] lines

        val chars = Stream.concat (Stream.map Stream.fromString lines)

        val formulas = Stream.toList (parseFormula chars)

        val formulas = formulasFromTptp formulas
      in
        {comments = comments, formulas = formulas}
      end;
end;

(* Quick testing
installPP Term.pp;
installPP Formula.pp;
val () = Term.isVarName := (fn s => Char.isUpper (String.sub (s,0)));
val TPTP_DIR = "/Users/Joe/ptr/tptp/tptp/";
val num1 = read {filename = TPTP_DIR ^ "NUM/NUM001-1.tptp"};
val lcl9 = read {filename = TPTP_DIR ^ "LCL/LCL009-1.tptp"};
val set11 = read {filename = TPTP_DIR ^ "SET/SET011+3.tptp"};
val swc128 = read {filename = TPTP_DIR ^ "SWC/SWC128-1.tptp"};
*)

local
  fun mkCommentLine comment = mkComment comment ^ "\n";

  fun formulaStream [] () = Stream.NIL
    | formulaStream (h :: t) () =
      Stream.CONS ("\n" ^ formulaToString h, formulaStream t);
in
  fun write {filename} {comments,formulas} =
      Stream.toTextFile
        {filename = filename}
        (Stream.append
           (Stream.map mkCommentLine (Stream.fromList comments))
           (formulaStream (formulasToTptp formulas)));
end;

(* ------------------------------------------------------------------------- *)
(* Converting TPTP problems to goal formulas.                                *)
(* ------------------------------------------------------------------------- *)

fun isCnfProblem ({formulas,...} : problem) =
    let
      val cnf = List.exists isCnfFormula formulas
      and fof = List.exists isFofFormula formulas
    in
      case (cnf,fof) of
        (false,false) => raise Error "TPTP problem has no formulas"
      | (true,true) => raise Error "TPTP problem has both cnf and fof formulas"
      | (cnf,_) => cnf
    end;

fun hasConjecture ({formulas,...} : problem) =
    List.exists formulaIsConjecture formulas;

local
  fun cnfFormulaToClause (CnfFormula {clause,...}) =
      if mem (Boolean true) clause then NONE
      else
        let
          val lits = List.mapPartial (total destLiteral) clause
        in
          SOME (LiteralSet.fromList lits)
        end
    | cnfFormulaToClause (FofFormula _) = raise Bug "cnfFormulaToClause";

  fun fofFormulaToGoal (FofFormula {formula,role,...}, {axioms,goals}) =
      let
        val fm = Formula.generalize formula
      in
        if role = ROLE_CONJECTURE then
          {axioms = axioms, goals = fm :: goals}
        else
          {axioms = fm :: axioms, goals = goals}
      end
    | fofFormulaToGoal (CnfFormula _, _) = raise Bug "fofFormulaToGoal";
in
  fun toGoal (prob as {formulas,...}) =
      if isCnfProblem prob then
        Cnf (List.mapPartial cnfFormulaToClause formulas)
      else
        Fof
        let
          val axioms_goals = {axioms = [], goals = []}
          val axioms_goals = List.foldl fofFormulaToGoal axioms_goals formulas
        in
          case axioms_goals of
            {axioms, goals = []} =>
            Formula.Imp (Formula.listMkConj axioms, Formula.False)
          | {axioms = [], goals} => Formula.listMkConj goals
          | {axioms,goals} =>
            Formula.Imp (Formula.listMkConj axioms, Formula.listMkConj goals)
        end;
end;

local
  fun fromClause cl n =
      let
        val name = "clause_" ^ Int.toString n
        val role = ROLE_NEGATED_CONJECTURE
        val clause = clauseFromLiteralSet cl
      in
        (CnfFormula {name = name, role = role, clause = clause}, n + 1)
      end;
in
  fun fromProblem prob =
      let
        val comments = []
        and (formulas,_) = maps fromClause prob 0
      in
        {comments = comments, formulas = formulas}
      end;
end;

local
  fun refute cls =
      let
        val res = Resolution.new Resolution.default (map Thm.axiom cls)
      in
        case Resolution.loop res of
          Resolution.Contradiction _ => true
        | Resolution.Satisfiable _ => false
      end;
in
  fun prove filename =
      let
        val tptp = read filename
        val problems =
            case toGoal tptp of
              Cnf prob => [prob]
            | Fof goal => Problem.fromGoal goal
      in
        List.all refute problems
      end;
end;

(* ------------------------------------------------------------------------- *)
(* TSTP proofs.                                                              *)
(* ------------------------------------------------------------------------- *)

local
  fun ppAtomInfo pp atm =
      case total Atom.destEq atm of
        SOME (a,b) => ppAtom pp ("$equal",[a,b])
      | NONE => ppAtom pp atm;

  fun ppLiteralInfo pp (pol,atm) =
      if pol then ppAtomInfo pp atm
      else
        (Parser.beginBlock pp Parser.Inconsistent 2;
         Parser.addString pp "~";
         Parser.addBreak pp (1,0);
         ppAtomInfo pp atm;
         Parser.endBlock pp);

  val ppAssumeInfo = Parser.ppBracket "(" ")" ppAtomInfo;

  val ppSubstInfo =
      Parser.ppMap
        Subst.toList
        (Parser.ppSequence ","
           (Parser.ppBracket "[" "]"
              (Parser.ppBinop "," ppVar (Parser.ppBracket "(" ")" ppTerm))));

  val ppResolveInfo = Parser.ppBracket "(" ")" ppAtomInfo;

  val ppReflInfo = Parser.ppBracket "(" ")" ppTerm;
        
  fun ppEqualityInfo pp (lit,path,res) =
      (Parser.ppBracket "(" ")" ppLiteralInfo pp lit;
       Parser.addString pp ",";
       Parser.addBreak pp (1,0);
       Term.ppPath pp path;
       Parser.addString pp ",";
       Parser.addBreak pp (1,0);
       Parser.ppBracket "(" ")" ppTerm pp res);

  fun ppInfInfo pp inf =
      case inf of
        Proof.Axiom _ => raise Bug "ppInfInfo"
      | Proof.Assume atm => ppAssumeInfo pp atm
      | Proof.Subst (sub,_) => ppSubstInfo pp sub
      | Proof.Resolve (res,_,_) => ppResolveInfo pp res
      | Proof.Refl tm => ppReflInfo pp tm
      | Proof.Equality x => ppEqualityInfo pp x;
in
  fun ppProof p prf =
      let
        fun thmString n = Int.toString n
                          
        val prf = enumerate prf

        fun ppThm p th =
            let
              val cl = Thm.clause th

              fun pred (_,(th',_)) = LiteralSet.equal (Thm.clause th') cl
            in
              case List.find pred prf of
                NONE => Parser.addString p "(?)"
              | SOME (n,_) => Parser.addString p (thmString n)
            end

        fun ppInf p inf =
            let
              val name = Thm.inferenceTypeToString (Proof.inferenceType inf)
              val name = String.map Char.toLower name
            in
              Parser.addString p (name ^ ",");
              Parser.addBreak p (1,0);
              Parser.ppBracket "[" "]" ppInfInfo p inf;
              case Proof.parents inf of
                [] => ()
              | ths =>
                (Parser.addString p ",";
                 Parser.addBreak p (1,0);
                 Parser.ppList ppThm p ths)
            end
              
        fun ppTaut p inf =
            (Parser.addString p "tautology,";
             Parser.addBreak p (1,0);
             Parser.ppBracket "[" "]" ppInf p inf)
             
        fun ppStepInfo p (n,(th,inf)) =
            let
              val is_axiom = case inf of Proof.Axiom _ => true | _ => false
              val name = thmString n
              val role =
                  if is_axiom then "axiom"
                  else if Thm.isContradiction th then "theorem"
                  else "plain"
              val cl = clauseFromThm th
            in
              Parser.addString p (name ^ ",");
              Parser.addBreak p (1,0);
              Parser.addString p (role ^ ",");
              Parser.addBreak p (1,0);
              Parser.ppBracket "(" ")" ppClause p cl;
              if is_axiom then ()
              else
                let
                  val is_tautology = null (Proof.parents inf)
                in
                  Parser.addString p ",";
                  Parser.addBreak p (1,0);
                  if is_tautology then
                    Parser.ppBracket "introduced(" ")" ppTaut p inf
                  else
                    Parser.ppBracket "inference(" ")" ppInf p inf
                end
            end

        fun ppStep p step =
            (Parser.ppBracket "cnf(" ")" ppStepInfo p step;
             Parser.addString p ".";
             Parser.addNewline p)
      in
        Parser.beginBlock p Parser.Consistent 0;
        app (ppStep p) prf;
        Parser.endBlock p
      end
(*DEBUG
      handle Error err => raise Bug ("Tptp.ppProof: shouldn't fail:\n" ^ err);
*)
end;

val proofToString = Parser.toString ppProof;

end
end;
print_depth 10;
