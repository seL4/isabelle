(*  Title: 	HOL/Lex/Chopper.thy
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1995 TUM

A 'chopper' is a function which returns
  1. a chopped up prefix of the input string
  2. together with the remaining suffix.

It is a longest_prefix_chopper if it
  1. chops up as much of the input as possible and
  2. chops it up into the longest substrings possible.

A chopper is parametrized by a language ('a list => bool),
i.e. a set of strings.
*)

Chopper = Prefix +

types   'a chopper = "'a list => 'a list list * 'a list"

consts
  is_longest_prefix_chopper :: "['a list => bool, 'a chopper] => bool"

defs
  is_longest_prefix_chopper_def
    "is_longest_prefix_chopper L chopper == !xs.   \
\	 (!zs. chopper(xs) = ([],zs) --> \
\	       zs=xs & (!ys. ys ~= [] & ys <= xs --> ~L(ys))) &  \
\ 	 (!ys yss zs. chopper(xs) = (ys#yss,zs) -->                \
\	    ys ~= [] & L(ys) & xs=ys@flat(yss)@zs &   \
\           chopper(flat(yss)@zs) = (yss,zs) &     \
\           (!as. as <= xs & ys <= as & ys ~= as --> ~L(as)))"
end
