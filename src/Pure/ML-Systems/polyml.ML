(*  Title:      Pure/ML-Systems/polyml.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Compatibility file for Poly/ML (versions 2.x, 3.x).
*)

open PolyML ExtendedIO;

use"basis.ML";


(*A conditional timing function: applies f to () and, if the flag is true,
  prints its runtime.*)

fun cond_timeit flag f =
  if flag then
    let val before = System.processtime()
        val result = f()
        val both = real(System.processtime() - before) / 10.0
    in  output(std_out, "Process time (incl GC): "^
                         makestring both ^ " secs\n");
        result
    end
  else f();


(*Interface for toplevel pretty printers, see also Pure/install_pp.ML*)

fun make_pp _ pprint (str, blk, brk, en) obj =
  pprint obj (str, fn ind => blk (ind, false), fn wd => brk (wd, 0),
    fn () => brk (99999, 0), en);


(*** File handling ***)

local

(*These are functions from library.ML *)
fun take_suffix _ [] = ([], [])
  | take_suffix pred (x :: xs) =
      (case take_suffix pred xs of
         ([], sffx) => if pred x then ([], x :: sffx)
                                 else ([x], sffx)
       | (prfx, sffx) => (x :: prfx, sffx));

fun apr (f,y) x = f(x,y);

fun seq (proc: 'a -> unit) : 'a list -> unit =
  let fun seqf [] = ()
        | seqf (x :: xs) = (proc x; seqf xs)
  in seqf end;

fun radixpand num : int list =
  let fun radix (n, tail) =
    if n < 10 then n :: tail else radix (n div 10, (n mod 10) :: tail)
  in radix (num, []) end;

fun radixstring num =
  let fun chrof n = chr (ord "0" + n);
  in implode (map chrof (radixpand num)) end;

in

(*Get time of last modification; if file doesn't exist return an empty string*)
fun file_info "" = ""
  | file_info name = radixstring (System.filedate name)  handle _ => "";


structure OS =
  struct
  structure FileSys =
    struct
    val chDir = PolyML.cd

    fun remove name =    (*Delete a file *)
      let val (is, os) = ExtendedIO.execute ("rm " ^ name)
      in close_in is; close_out os end;

    (*Get pathname of current working directory *)
    fun getDir () =
      let val (is, os) = ExtendedIO.execute ("pwd")
	  val (path, _) = take_suffix (apr(op=,"\n")) (*remove newline*)
			   (explode (ExtendedIO.input_line is)) 
      in close_in is; close_out os; implode path end;

    end
  end;



(*** ML command execution ***)

val use_string =
  let fun exec command =
    let val firstLine = ref true;

        fun getLine () =
          if !firstLine
          then (firstLine := false; command)
          else raise Io "use_string: buffer exhausted"
    in PolyML.compiler (getLine, fn s => output (std_out, s)) () end
  in seq exec end;

end;


(*** System command execution ***)

(*Execute an Unix command which doesn't take any input from stdin and
  sends its output to stdout.*)
fun execute command =
  let val (is, os) =  ExtendedIO.execute command;
      val result = input (is, 999999);
  in close_out os;
     close_in is;
     result
  end;
