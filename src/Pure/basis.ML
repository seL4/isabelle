(*  Title:      Pure/NJ
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Basis Library emulation

Needed for Poly/ML and Standard ML of New Jersey version 0.93

Full compatibility cannot be obtained using a file: what about char constants?
*)

structure Bool =
  struct
  fun toString true  = "true"
    | toString false = "false"
  end;

structure Int =
  struct
  fun toString (i: int) = makestring i;
  fun max (x, y) = if x < y then y else x : int;
  fun min (x, y) = if x < y then x else y : int;
  end;

structure TextIO =
  struct
  type instream = instream
  and  outstream = outstream
  exception Io of {name: string, function: string, cause: exn}
  val stdIn 	= std_in
  val stdOut 	= std_out
  val openIn 	= open_in
  val openAppend = open_append
  val openOut 	= open_out
  val closeIn 	= close_in
  val closeOut 	= close_out
  val inputN 	= input
  val inputAll  = fn is => inputN (is, 999999)
  val inputLine = input_line
  val endOfStream = end_of_stream
  val output 	= output
  val flushOut 	= flush_out
  end;
