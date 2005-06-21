(*  Title:      HOL/Tools/res_lib.ML
    Author:     Jia Meng, Cambridge University Computer Laboratory
    ID:         $Id$
    Copyright   2004 University of Cambridge

Some auxiliary functions frequently used by files in this directory.
*)

signature RES_LIB =
sig
val flat_noDup : ''a list list -> ''a list
val helper_path : string -> string -> string
val list2str_sep : string -> string list -> string
val list_to_string : string list -> string
val list_to_string' : string list -> string
val no_BDD : string -> string
val no_blanks : string -> string
val no_blanks_dots : string -> string
val no_blanks_dots_dashes : string -> string
val no_dots : string -> string
val no_rep_add : ''a -> ''a list -> ''a list
val no_rep_app : ''a list -> ''a list -> ''a list
val pair_ins : 'a -> 'b list -> ('a * 'b) list
val rm_rep : ''a list -> ''a list
val write_strs : TextIO.outstream -> TextIO.vector list -> unit
val writeln_strs : TextIO.outstream -> TextIO.vector list -> unit
end;


structure ResLib : RES_LIB =
struct

(* convert a list of strings into one single string; surrounded by brackets *)
fun list_to_string strings =
let
	fun str_of [s]      = s
	  | str_of (s1::ss) = s1 ^ "," ^ (str_of ss)
	  | str_of _        = ""
in
	"(" ^ str_of strings ^ ")"
end;

fun list_to_string' strings =
let
	fun str_of [s]      = s
	  | str_of (s1::ss) = s1 ^ "," ^ (str_of ss)
	  | str_of _        = ""
in
	"[" ^ str_of strings ^ "]"
end;

(* remove some chars (not allowed by TPTP format) from a string *)
fun no_blanks " " = "_"
  | no_blanks c   = c;

fun no_dots "." = "_dot_"
  | no_dots c   = c;

fun no_blanks_dots " " = "_"
  | no_blanks_dots "." = "_dot_"
  | no_blanks_dots c   = c;

fun no_blanks_dots_dashes " " = "_"
  | no_blanks_dots_dashes "." = "_dot_"
  | no_blanks_dots_dashes "'" = "_da_"
  | no_blanks_dots_dashes c   = c;

fun no_BDD cs =
	implode (map no_blanks_dots_dashes (explode cs));

fun no_rep_add x []     = [x]
  | no_rep_add x (y::z) = if x=y then y::z else y::(no_rep_add x z);

fun no_rep_app l1 []     = l1
  | no_rep_app l1 (x::y) = no_rep_app (no_rep_add x l1) y;

fun rm_rep []     = []
  | rm_rep (x::y) = if x mem y then rm_rep y else x::(rm_rep y);

fun flat_noDup []     = []
  | flat_noDup (x::y) = no_rep_app x (flat_noDup y);

fun list2str_sep delim []      = delim
  | list2str_sep delim (s::ss) = (s ^ delim) ^ (list2str_sep delim ss);

fun write_strs _   []      = ()
  | write_strs out (s::ss) = (TextIO.output (out, s); write_strs out ss);

fun writeln_strs _   []      = ()
  | writeln_strs out (s::ss) = (TextIO.output (out, s); TextIO.output (out, "\n"); writeln_strs out ss);

(* pair the first argument with each element in the second input list *)
fun pair_ins x []      = []
  | pair_ins x (y::ys) = (x, y) :: (pair_ins x ys);
  
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

end;
