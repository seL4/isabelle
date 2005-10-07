(*  Title:      HOL/Tools/res_lib.ML
    Author:     Jia Meng, Cambridge University Computer Laboratory
    ID:         $Id$
    Copyright   2004 University of Cambridge

Some auxiliary functions frequently used by files in this directory.
*)

signature RES_LIB =
sig
val helper_path : string -> string -> string
val intOfPid : Posix.Process.pid -> Int.int
val pidOfInt : Int.int -> Posix.Process.pid
end;


structure ResLib : RES_LIB =
struct

(*Return the path to a "helper" like SPASS or tptp2X, first checking that
  it exists. --lcp *)  
fun helper_path evar base =
  case getenv evar of
      "" => error  ("Isabelle environment variable " ^ evar ^ " not defined")
    | home => 
        let val path = home ^ "/" ^ base
        in  if File.exists (File.unpack_platform_path path) then path 
	    else error ("Could not find the file " ^ path)
	end;  

(*** Converting between process ids and integers ***)

fun intOfPid pid = Word.toInt (Word.fromLargeWord (Posix.Process.pidToWord pid));

fun pidOfInt n = Posix.Process.wordToPid (Word.toLargeWord (Word.fromInt n));

end;
