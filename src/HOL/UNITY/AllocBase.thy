(*  Title:      HOL/UNITY/AllocBase
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Common declarations for Chandy and Charpentier's Allocator

add_path "../Induct";
time_use_thy "AllocBase";
*)

AllocBase = Rename + Follows + 

consts
  NbT      :: nat       (*Number of tokens in system*)
  Nclients :: nat       (*Number of clients*)

rules
  NbT_pos  "0 < NbT"

(*This function merely sums the elements of a list*)
consts tokens     :: nat list => nat
primrec 
  "tokens [] = 0"
  "tokens (x#xs) = x + tokens xs"

(*Or could be setsum...(lessThan n)*)
consts sum_below :: "[nat=>'a, nat] => ('a::plus_ac0)"
primrec 
  sum_below_0    "sum_below f 0 = 0"
  sum_below_Suc  "sum_below f (Suc n) = f(n) + sum_below f n"

constdefs sublist :: "['a list, nat set] => 'a list"
    "sublist l A == map fst (filter (%p. snd p : A) (zip l [0..size l(]))"


consts
  bag_of :: 'a list => 'a multiset

primrec
  "bag_of []     = {#}"
  "bag_of (x#xs) = {#x#} + bag_of xs"

end
