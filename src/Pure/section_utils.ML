(*  Title: 	Pure/section_utils.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Utilities for writing new theory sections.
*)

fun ap t u = t$u;
fun app t (u1,u2) = t $ u1 $ u2;

(*Make distinct individual variables a1, a2, a3, ..., an. *)
fun mk_frees a [] = []
  | mk_frees a (T::Ts) = Free(a,T) :: mk_frees (bump_string a) Ts;


(*Read an assumption in the given theory*)
fun assume_read thy a = Thm.assume (read_cterm (sign_of thy) (a,propT));

(*Read a term from string "b", with expected type T*)
fun readtm sign T b = 
    read_cterm sign (b,T) |> term_of
    handle ERROR => error ("The error(s) above occurred for " ^ b);

(*From HOL/ex/meson.ML: raises exception if no rules apply -- unlike RL*)
fun tryres (th, rl::rls) = (th RS rl handle THM _ => tryres(th,rls))
  | tryres (th, []) = raise THM("tryres", 0, [th]);

fun gen_make_elim elim_rls rl = 
      standard (tryres (rl, elim_rls @ [revcut_rl]));

(** String manipulation **)

(*Skipping initial blanks, find the first identifier*)	(* FIXME *)
fun scan_to_id s = 
    s |> Symbol.explode
    |> Scan.error (Scan.finite Symbol.eof
      (!! (fn _ => "Expected to find an identifier in " ^ s)
        (Scan.any Symbol.is_blank |-- Syntax.scan_id)))
    |> #1;

fun is_backslash c = c = "\\";

(*Apply string escapes to a quoted string; see Def of Standard ML, page 3
  Does not handle the \ddd form;  no error checking*)
fun escape [] = []
  | escape cs = (case take_prefix (not o is_backslash) cs of
	 (front, []) => front
       | (front, _::"n"::rest) => front @ ("\n" :: escape rest)
       | (front, _::"t"::rest) => front @ ("\t" :: escape rest)
       | (front, _::"^"::c::rest) => front @ (chr(ord(c)-64) :: escape rest)
       | (front, _::"\""::rest) => front @ ("\"" :: escape rest)
       | (front, _::"\\"::rest) => front @ ("\\" :: escape rest)
       | (front, b::c::rest) => 
	   if Symbol.is_blank c   (*remove any further blanks and the following \ *)
	   then front @ escape (tl (snd (take_prefix Symbol.is_blank rest)))
	   else error ("Unrecognized string escape: " ^ implode(b::c::rest)));

(*Remove the first and last charaters -- presumed to be quotes*)
val trim = implode o escape o rev o tl o rev o tl o Symbol.explode;
