(*  Title:      HOL/List.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen

The datatype of finite lists.
*)

List = Divides +

datatype 'a list = "[]" ("[]") | "#" 'a ('a list) (infixr 65)

consts
  "@"         :: ['a list, 'a list] => 'a list            (infixr 65)
  filter      :: ['a => bool, 'a list] => 'a list
  concat      :: 'a list list => 'a list
  foldl       :: [['b,'a] => 'b, 'b, 'a list] => 'b
  hd          :: 'a list => 'a
  length      :: 'a list => nat
  set_of_list :: 'a list => 'a set
  list_all    :: ('a => bool) => ('a list => bool)
  map         :: ('a=>'b) => ('a list => 'b list)
  mem         :: ['a, 'a list] => bool                    (infixl 55)
  nth         :: [nat, 'a list] => 'a
  take, drop  :: [nat, 'a list] => 'a list
  takeWhile,
  dropWhile   :: ('a => bool) => 'a list => 'a list
  tl,ttl      :: 'a list => 'a list
  rev         :: 'a list => 'a list

syntax
  (* list Enumeration *)
  "@list"     :: args => 'a list                          ("[(_)]")

  (* Special syntax for filter *)
  "@filter"   :: [idt, 'a list, bool] => 'a list          ("(1[_:_ ./ _])")

translations
  "[x, xs]"     == "x#[xs]"
  "[x]"         == "x#[]"
  "[x:xs . P]"  == "filter (%x.P) xs"

syntax (symbols)
  "@filter"   :: [idt, 'a list, bool] => 'a list          ("(1[_\\<in>_ ./ _])")


consts
  lists        :: 'a set => 'a list set

  inductive "lists A"
  intrs
    Nil  "[]: lists A"
    Cons "[| a: A;  l: lists A |] ==> a#l : lists A"


primrec hd list
  "hd([]) = arbitrary"
  "hd(x#xs) = x"
primrec tl list
  "tl([]) = arbitrary"
  "tl(x#xs) = xs"
primrec ttl list
  (* a "total" version of tl: *)
  "ttl([]) = []"
  "ttl(x#xs) = xs"
primrec "op mem" list
  "x mem [] = False"
  "x mem (y#ys) = (if y=x then True else x mem ys)"
primrec set_of_list list
  "set_of_list [] = {}"
  "set_of_list (x#xs) = insert x (set_of_list xs)"
primrec list_all list
  list_all_Nil  "list_all P [] = True"
  list_all_Cons "list_all P (x#xs) = (P(x) & list_all P xs)"
primrec map list
  "map f [] = []"
  "map f (x#xs) = f(x)#map f xs"
primrec "op @" list
  "[] @ ys = ys"
  "(x#xs)@ys = x#(xs@ys)"
primrec rev list
  "rev([]) = []"
  "rev(x#xs) = rev(xs) @ [x]"
primrec filter list
  "filter P [] = []"
  "filter P (x#xs) = (if P x then x#filter P xs else filter P xs)"
primrec foldl list
  "foldl f a [] = a"
  "foldl f a (x#xs) = foldl f (f a x) xs"
primrec length list
  "length([]) = 0"
  "length(x#xs) = Suc(length(xs))"
primrec concat list
  "concat([]) = []"
  "concat(x#xs) = x @ concat(xs)"
primrec drop list
  drop_Nil  "drop n [] = []"
  drop_Cons "drop n (x#xs) = (case n of 0 => x#xs | Suc(m) => drop m xs)"
primrec take list
  take_Nil  "take n [] = []"
  take_Cons "take n (x#xs) = (case n of 0 => [] | Suc(m) => x # take m xs)"
primrec nth nat
  "nth 0 xs = hd xs"
  "nth (Suc n) xs = nth n (tl xs)"
primrec takeWhile list
  "takeWhile P [] = []"
  "takeWhile P (x#xs) = (if P x then x#takeWhile P xs else [])"
primrec dropWhile list
  "dropWhile P [] = []"
  "dropWhile P (x#xs) = (if P x then dropWhile P xs else xs)"

end
