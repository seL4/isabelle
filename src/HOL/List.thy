(*  Title:      HOL/List.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

Definition of type 'a list as a datatype. This allows primrec to work.

*)

List = Arith +

datatype 'a list = "[]" ("[]") | "#" 'a ('a list) (infixr 65)

consts

  "@"	    :: "['a list, 'a list] => 'a list"		(infixr 65)
  drop      :: "[nat, 'a list] => 'a list"
  filter    :: "['a => bool, 'a list] => 'a list"
  flat      :: "'a list list => 'a list"
  foldl     :: "[['b,'a] => 'b, 'b, 'a list] => 'b"
  hd        :: "'a list => 'a"
  length    :: "'a list => nat"
  list_all  :: "('a => bool) => ('a list => bool)"
  map       :: "('a=>'b) => ('a list => 'b list)"
  mem       :: "['a, 'a list] => bool"			(infixl 55)
  nth       :: "[nat, 'a list] => 'a"
  take      :: "[nat, 'a list] => 'a list"
  tl,ttl    :: "'a list => 'a list"
  rev       :: "'a list => 'a list"

syntax
  (* list Enumeration *)
  "@list"   :: "args => 'a list"                        ("[(_)]")

  (* Special syntax for list_all and filter *)
  "@Alls"	:: "[idt, 'a list, bool] => bool"	("(2Alls _:_./ _)" 10)
  "@filter"	:: "[idt, 'a list, bool] => 'a list"	("(1[_:_ ./ _])")

translations
  "[x, xs]"     == "x#[xs]"
  "[x]"         == "x#[]"

  "[x:xs . P]"	== "filter (%x.P) xs"
  "Alls x:xs.P"	== "list_all (%x.P) xs"

primrec hd list
  hd_Nil  "hd([]) = (@x.False)"
  hd_Cons "hd(x#xs) = x"
primrec tl list
  tl_Nil  "tl([]) = (@x.False)"
  tl_Cons "tl(x#xs) = xs"
primrec ttl list
  (* a "total" version of tl: *)
  ttl_Nil  "ttl([]) = []"
  ttl_Cons "ttl(x#xs) = xs"
primrec "op mem" list
  mem_Nil  "x mem [] = False"
  mem_Cons "x mem (y#ys) = (if y=x then True else x mem ys)"
primrec list_all list
  list_all_Nil  "list_all P [] = True"
  list_all_Cons "list_all P (x#xs) = (P(x) & list_all P xs)"
primrec map list
  map_Nil  "map f [] = []"
  map_Cons "map f (x#xs) = f(x)#map f xs"
primrec "op @" list
  append_Nil  "[] @ ys = ys"
  append_Cons "(x#xs)@ys = x#(xs@ys)"
primrec rev list
  rev_Nil  "rev([]) = []"
  rev_Cons "rev(x#xs) = rev(xs) @ [x]"
primrec filter list
  filter_Nil  "filter P [] = []"
  filter_Cons "filter P (x#xs) = (if P x then x#filter P xs else filter P xs)"
primrec foldl list
  foldl_Nil  "foldl f a [] = a"
  foldl_Cons "foldl f a (x#xs) = foldl f (f a x) xs"
primrec length list
  length_Nil  "length([]) = 0"
  length_Cons "length(x#xs) = Suc(length(xs))"
primrec flat list
  flat_Nil  "flat([]) = []"
  flat_Cons "flat(x#xs) = x @ flat(xs)"
defs
  drop_def "drop n == nat_rec n (%xs.xs)   \
\	                (%m r xs. case xs of [] => [] | y#ys => r ys)"
  take_def "take n == nat_rec n (%xs.[])   \
\	                (%m r xs. case xs of [] => [] | y#ys => y # r ys)"
  nth_def  "nth(n) == nat_rec n hd (%m r xs. r(tl(xs)))"
end
