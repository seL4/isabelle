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

consts
  bag_of :: 'a list => 'a multiset

primrec
  "bag_of []     = {#}"
  "bag_of (x#xs) = {#x#} + bag_of xs"

end
