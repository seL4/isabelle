(*  Title:      TFL/utils
    ID:         $Id$
    Author:     Konrad Slind, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

Basic utilities
*)

signature Utils_sig =
sig
  exception ERR of {module:string,func:string, mesg:string}

  val can   : ('a -> 'b) -> 'a -> bool
  val holds : ('a -> bool) -> 'a -> bool
  val C : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c

  val itlist : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val rev_itlist : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val end_itlist : ('a -> 'a -> 'a) -> 'a list -> 'a
  val itlist2 :('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
  val pluck : ('a -> bool) -> 'a list -> 'a * 'a list
  val zip3 : 'a list -> 'b list -> 'c list -> ('a*'b*'c) list
  val take  : ('a -> 'b) -> int * 'a list -> 'b list
  val sort  : ('a -> 'a -> bool) -> 'a list -> 'a list

end;

