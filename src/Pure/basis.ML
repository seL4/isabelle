(*  Title:      Pure/basis.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Basis Library emulation.

Needed for Poly/ML and Standard ML of New Jersey version 0.93 to 1.08.

Full compatibility cannot be obtained using a file: what about char constants?
*)

exception Subscript;

structure Bool =
  struct
  fun toString true  = "true"
    | toString false = "false"
  end;


structure Option =
  struct
  exception Option

  datatype 'a option = NONE | SOME of 'a

  fun getOpt (SOME v, _) = v
    | getOpt (NONE,   a) = a

  fun isSome (SOME _) = true 
    | isSome NONE     = false

  fun valOf (SOME v) = v
    | valOf NONE     = raise Option
  end;


structure Int =
  struct
  fun toString (i: int) = makestring i;
  fun max (x, y) = if x < y then y else x : int;
  fun min (x, y) = if x < y then x else y : int;
  end;


structure List =
  struct
  exception Empty

  fun last []      = raise Empty
    | last [x]     = x
    | last (x::xs) = last xs;

  fun nth (xs, n) =
      let fun h []      _ = raise Subscript
	    | h (x::xs) n = if n=0 then x else h xs (n-1)
      in if n<0 then raise Subscript else h xs n end;

  fun drop (xs, n) =
      let fun h xs      0 = xs
	    | h []      n = raise Subscript
	    | h (x::xs) n = h xs (n-1)
      in if n<0 then raise Subscript else h xs n end;

  fun take (xs, n) =
      let fun h xs      0 = []
	    | h []      n = raise Subscript
	    | h (x::xs) n = x :: h xs (n-1)
      in if n<0 then raise Subscript else h xs n end;

  fun concat []      = []
    | concat (l::ls) = l @ concat ls;

  fun mapPartial f []      = []
    | mapPartial f (x::xs) = 
         (case f x of Option.NONE   => mapPartial f xs
                    | Option.SOME y => y :: mapPartial f xs);

  fun find _ []        = Option.NONE
    | find p (x :: xs) = if p x then Option.SOME x else find p xs;


  (*copy the list preserving elements that satisfy the predicate*)
  fun filter p [] = []
    | filter p (x :: xs) = if p x then x :: filter p xs else filter p xs;

  (*Partition list into elements that satisfy predicate and those that don't.
    Preserves order of elements in both lists.*)
  fun partition (p: 'a->bool) (ys: 'a list) : ('a list * 'a list) =
      let fun part ([], answer) = answer
	    | part (x::xs, (ys, ns)) = if p(x)
	      then  part (xs, (x::ys, ns))
	      else  part (xs, (ys, x::ns))
      in  part (rev ys, ([], []))  end;

  end;


structure ListPair =
  struct
  fun zip ([], [])      = []
    | zip (x::xs,y::ys) = (x,y) :: zip(xs,ys);

  fun unzip [] = ([],[])
    | unzip((x,y)::pairs) =
	  let val (xs,ys) = unzip pairs
	  in  (x::xs, y::ys)  end;

  fun map f ([], [])      = []
    | map f (x::xs,y::ys) = f(x,y) :: map f (xs,ys);

  fun exists p =
    let fun boolf ([], [])      = false
	  | boolf (x::xs,y::ys) = p(x,y) orelse boolf (xs,ys)
    in boolf end;

  fun all p =
    let fun boolf ([], [])      = true
	  | boolf (x::xs,y::ys) = p(x,y) andalso boolf (xs,ys)
    in boolf end;
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


fun print s = (output (std_out, s); flush_out std_out);
