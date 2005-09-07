(*  Title:      HOL/Tools/res_lib.ML
    Author:     Jia Meng, Cambridge University Computer Laboratory
    ID:         $Id$
    Copyright   2004 University of Cambridge

Some auxiliary functions frequently used by files in this directory.
*)

signature RES_LIB =
sig
val atomize_tac : int -> tactic
val flat_noDup : ''a list list -> ''a list
val helper_path : string -> string -> string
val list2str_sep : string -> string list -> string
val list_to_string : string list -> string
val list_to_string' : string list -> string
val no_rep_add : ''a -> ''a list -> ''a list
val no_rep_app : ''a list -> ''a list -> ''a list
val pair_ins : 'a -> 'b list -> ('a * 'b) list
val trim_ends : string -> string
val write_strs : TextIO.outstream -> TextIO.vector list -> unit
val writeln_strs : TextIO.outstream -> TextIO.vector list -> unit
end;


structure ResLib : RES_LIB =
struct

val atomize_tac =
 SUBGOAL
  (fn (prop,_) =>
    let val ts = Logic.strip_assums_hyp prop
        val atom = ObjectLogic.atomize_thm o forall_intr_vars
    in EVERY1
	[METAHYPS
	  (fn hyps => cut_facts_tac (map atom hyps) 1),
         REPEAT_DETERM_N (length ts) o (etac thin_rl)]
  end);

(*Remove both ends from the string (presumably quotation marks?)*)
fun trim_ends s = String.substring(s,1,String.size s - 2);


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

fun no_rep_add x []     = [x]
  | no_rep_add x (y::z) = if x=y then y::z else y::(no_rep_add x z);

fun no_rep_app l1 []     = l1
  | no_rep_app l1 (x::y) = no_rep_app (no_rep_add x l1) y;

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
