(*  Title:      Pure/POLY
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Compatibility file for Poly/ML (AHL release 1.88)
*)

open PolyML ExtendedIO;


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


(*Save function: in Poly/ML, ignores filename and commits to present file*)

fun xML filename banner = commit();


(*Interface for toplevel pretty printers, see also Pure/install_pp.ML*)

fun make_pp _ pprint (str, blk, brk, en) obj =
  pprint obj (str, fn ind => blk (ind, false), fn wd => brk (wd, 0),
    fn () => brk (99999, 0), en);


(*** File handling ***)

(*Get a string containing the time of last modification, attributes, owner
  and size of file (but not the path) *)
fun file_info "" = ""
  | file_info name =
      let
          (*These are functions from library.ML *)
          fun take_suffix _ [] = ([], [])
            | take_suffix pred (x :: xs) =
                (case take_suffix pred xs of
                  ([], sffx) => if pred x then ([], x :: sffx) else ([x], sffx)
                | (prfx, sffx) => (x :: prfx, sffx));
          fun apr (f,y) x = f(x,y);

          val (is, os) = ExtendedIO.execute ("ls -l " ^ name)
          val (result, _) = take_suffix (apr(op<>," ")) 
                              (explode (ExtendedIO.input_line is))
             (*Remove the part after the last " " (i.e. the path/filename) *)
        in close_in is;
           close_out os;
           implode result
        end;

fun delete_file name = ExtendedIO.execute ("rm " ^ name);
