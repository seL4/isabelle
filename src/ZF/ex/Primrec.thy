(*  Title: 	ZF/ex/Primrec.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Primitive Recursive Functions

Proof adopted from
Nora Szasz, 
A Machine Checked Proof that Ackermann's Function is not Primitive Recursive,
In: Huet & Plotkin, eds., Logical Environments (CUP, 1993), 317-338.

See also E. Mendelson, Introduction to Mathematical Logic.
(Van Nostrand, 1964), page 250, exercise 11.
*)

Primrec = List +
consts
    primrec :: "i"
    SC      :: "i"
    CONST   :: "i=>i"
    PROJ    :: "i=>i"
    COMP    :: "[i,i]=>i"
    PREC    :: "[i,i]=>i"
    ACK	    :: "i=>i"
    ack	    :: "[i,i]=>i"

translations
  "ack(x,y)"  == "ACK(x) ` [y]"

defs

  SC_def    "SC == lam l:list(nat).list_case(0, %x xs.succ(x), l)"

  CONST_def "CONST(k) == lam l:list(nat).k"

  PROJ_def  "PROJ(i) == lam l:list(nat). list_case(0, %x xs.x, drop(i,l))"

  COMP_def  "COMP(g,fs) == lam l:list(nat). g ` map(%f. f`l, fs)"

  (*Note that g is applied first to PREC(f,g)`y and then to y!*)
  PREC_def  "PREC(f,g) == \
\            lam l:list(nat). list_case(0, \
\                      %x xs. rec(x, f`xs, %y r. g ` Cons(r, Cons(y, xs))), l)"
  
  ACK_def   "ACK(i) == rec(i, SC, \
\                      %z r. PREC (CONST (r`[1]), COMP(r,[PROJ(0)])))"


inductive
  domains "primrec" <= "list(nat)->nat"
  intrs
    SC       "SC : primrec"
    CONST    "k: nat ==> CONST(k) : primrec"
    PROJ     "i: nat ==> PROJ(i) : primrec"
    COMP     "[| g: primrec; fs: list(primrec) |] ==> COMP(g,fs): primrec"
    PREC     "[| f: primrec; g: primrec |] ==> PREC(f,g): primrec"
  monos      "[list_mono]"
  con_defs   "[SC_def,CONST_def,PROJ_def,COMP_def,PREC_def]"
  type_intrs "nat_typechecks @ list.intrs @   		        \
\	      [lam_type, list_case_type, drop_type, map_type,   \
\	      apply_type, rec_type]"

end
