(*  Title:      HOL/ex/Primrec
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

Primitive Recursive Functions

Proof adopted from
Nora Szasz, 
A Machine Checked Proof that Ackermann's Function is not Primitive Recursive,
In: Huet & Plotkin, eds., Logical Environments (CUP, 1993), 317-338.

See also E. Mendelson, Introduction to Mathematical Logic.
(Van Nostrand, 1964), page 250, exercise 11.

Demonstrates recursive definitions, the TFL package
*)

Primrec = Main +

consts ack  :: "nat * nat => nat"
recdef ack "less_than <*lex*> less_than"
    "ack (0,n) =  Suc n"
    "ack (Suc m,0) = (ack (m, 1))"
    "ack (Suc m, Suc n) = ack (m, ack (Suc m, n))"

consts  list_add :: nat list => nat
primrec
  "list_add []     = 0"
  "list_add (m#ms) = m + list_add ms"

consts  zeroHd  :: nat list => nat
primrec
  "zeroHd []     = 0"
  "zeroHd (m#ms) = m"


(** The set of primitive recursive functions of type  nat list => nat **)
consts
    PRIMREC :: (nat list => nat) set
    SC      :: nat list => nat
    CONST   :: [nat, nat list] => nat
    PROJ    :: [nat, nat list] => nat
    COMP    :: [nat list => nat, (nat list => nat)list, nat list] => nat
    PREC    :: [nat list => nat, nat list => nat, nat list] => nat

defs

  SC_def    "SC l        == Suc (zeroHd l)"

  CONST_def "CONST k l   == k"

  PROJ_def  "PROJ i l    == zeroHd (drop i l)"

  COMP_def  "COMP g fs l == g (map (%f. f l) fs)"

  (*Note that g is applied first to PREC f g y and then to y!*)
  PREC_def  "PREC f g l == case l of
                             []   => 0
                           | x#l' => nat_rec (f l') (%y r. g (r#y#l')) x"

  
inductive PRIMREC
  intrs
    SC       "SC : PRIMREC"
    CONST    "CONST k : PRIMREC"
    PROJ     "PROJ i : PRIMREC"
    COMP     "[| g: PRIMREC; fs: lists PRIMREC |] ==> COMP g fs : PRIMREC"
    PREC     "[| f: PRIMREC; g: PRIMREC |] ==> PREC f g: PRIMREC"
  monos      lists_mono

end
